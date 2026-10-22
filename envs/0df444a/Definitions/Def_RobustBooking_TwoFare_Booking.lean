-- Prove2me | Definitions.Def_RobustBooking_TwoFare_Booking
-- name    : RobustBooking_TwoFare_Booking
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-02T22:18:25.032326+00:00
-- url     : https://prove2.me/theorems/e31377d6-d842-4e7f-a2f0-1056b9ad27c3
-- title:
--   The continuous two-fare online booking problem: requests, offline optimum, online policies, competitive ratios
-- statement:
--   **The continuous two-fare booking problem.** A seller holds $n > 0$ units of capacity (real-valued: in the continuous problem demands and acceptances may be any nonnegative reals). There are two fare classes, *high* with fare $f_1$ and *low* with fare $f_2$. A **request** is a fare class together with a quantity $q > 0$; any part $0 \le a \le q$ of it may be accepted. An **instance** $I$ is a finite sequence of requests.
--
--   The **optimal offline revenue** is
--   $$v^*(I) \;=\; \sup\Big\{\textstyle\sum_i f_{c_i}\, x_i \;:\; 0 \le x_i \le q_i,\ \sum_i x_i \le n\Big\},$$
--   the best revenue achievable knowing the whole sequence in advance (written $R^*(I)$ in the paper). The function `b` is $b(r) = 1/(2-r)$, Eq. (1).
--
--   A **deterministic online policy** $A$ is any rule that, when a request arrives, proposes a quantity to accept based only on the earlier requests (each with the quantity accepted from it) and the current request. Running $A$ on $I$ processes the requests in order; each proposal is clipped to $[0, \min(q, n - \text{capacity already sold})]$, so every rule is a feasible policy and every nonanticipative feasible policy arises this way. Its revenue $v'(I) = R(A, I)$ is $\sum_i f_{c_i} a_i$ over the accepted quantities $a_i$.
--
--   The **competitive ratio** of $A$ is
--   $$\inf_{I \,:\, v^*(I) > 0} \frac{v'(I)}{v^*(I)}.$$
--   A **randomized policy** is a random choice $A(\omega)$ of a deterministic policy, $\omega$ drawn from a probability measure $\mu$; its competitive ratio is $\inf_{I : v^*(I)>0} \mathbb{E}_\mu[v'_{A(\omega)}(I)] / v^*(I)$.
--
--   **Formalization Note.** Requests carry a positive real quantity (`qty_pos`); unit requests are `qty = 1`. The offline optimum is an `sSup`; for $n \ge 0$ its set is nonempty ($x = 0$) and bounded above ($x \le q$), so it is the true maximum. The competitive ratios are `sInf`s over instances with positive optimum; that set is nonempty for $n>0$, $f_1>0$ (a single request) and bounded below by $0$ (fares positive, accepted quantities nonnegative). The expectation is a Bochner integral; theorems that use it assume measurability of $\omega \mapsto R(A(\omega), I)$, and the revenue is bounded by $f_1 n$, so it is integrable. The policy may depend on $n, f_1, f_2$ (they are fixed parameters of the problem) but never on future requests or the length of the sequence.
-- source:
--   Ball, Queyranne, Toward Robust Revenue Management: Competitive Analysis of Online Booking, Oper. Res. 57(4), 2009, pp. 950–954: competitive ratio (p. 950, p. 951), continuous problem (p. 952), Eq. (1) (p. 953), randomized algorithms as random choices of deterministic ones (p. 954)

import Mathlib

namespace RobustBooking.TwoFare

open MeasureTheory

/-- The two fare classes of the two-fare problem (Ball–Queyranne 2009, §1.1, p. 953): a `high`
request pays the full fare `f₁`, a `low` request pays the discounted fare `f₂`. -/
inductive FareClass where
  | high
  | low
  deriving DecidableEq

/-- A booking request of the continuous two-fare problem (p. 952): a fare class and a positive real
quantity. Partial acceptance is allowed; a unit request is the case `qty = 1`. -/
structure Request where
  /-- The fare class of the request. -/
  cls : FareClass
  /-- The requested quantity. -/
  qty : ℝ
  /-- The requested quantity is positive. -/
  qty_pos : 0 < qty

/-- The fare paid per unit by a request of class `c`: `f₁` for `high`, `f₂` for `low`. -/
def fare (f₁ f₂ : ℝ) : FareClass → ℝ
  | .high => f₁
  | .low => f₂

/-- `b(r) = 1 / (2 - r)`, Eq. (1), p. 953. -/
noncomputable def b (r : ℝ) : ℝ := 1 / (2 - r)

/-- An offline acceptance vector `x` for the instance `I` (the finite request sequence) is feasible
for capacity `n` when `0 ≤ xᵢ ≤ qtyᵢ` for every request and `∑ xᵢ ≤ n`. -/
def IsFeasible (n : ℝ) (I : List Request) (x : Fin I.length → ℝ) : Prop :=
  (∀ i, 0 ≤ x i ∧ x i ≤ (I.get i).qty) ∧ ∑ i, x i ≤ n

/-- The optimal offline revenue `v*(I)` (written `R*(I)` in §1.1): the supremum of
`∑ᵢ fare(clsᵢ) · xᵢ` over all feasible offline acceptance vectors. For `0 ≤ n` the set is nonempty
(`x = 0`) and bounded above (`x ≤ qty`), so this is the true maximum. -/
noncomputable def optRevenue (f₁ f₂ n : ℝ) (I : List Request) : ℝ :=
  sSup {v : ℝ | ∃ x : Fin I.length → ℝ, IsFeasible n I x ∧
    v = ∑ i, fare f₁ f₂ (I.get i).cls * x i}

/-- A deterministic online booking policy: given the history (the earlier requests, in arrival
order, each with the quantity that was accepted from it) and the current request, it proposes a
quantity to accept. It never sees future requests or the length of the sequence. -/
abbrev DetPolicy : Type := List (Request × ℝ) → Request → ℝ

/-- Running a policy with capacity `n` on the remaining requests, given the history so far and the
capacity `used` already sold. Each proposal is clipped to `[0, min qty (n - used)]`, so every
policy is feasible; the result lists the accepted quantities in arrival order. -/
noncomputable def runFrom (n : ℝ) (A : DetPolicy) :
    List (Request × ℝ) → ℝ → List Request → List ℝ
  | _, _, [] => []
  | hist, used, q :: rest =>
      let a := max 0 (min (A hist q) (min q.qty (n - used)))
      a :: runFrom n A (hist ++ [(q, a)]) (used + a) rest

/-- The quantities accepted by policy `A` from the requests of `I`, in arrival order. -/
noncomputable def accepted (n : ℝ) (A : DetPolicy) (I : List Request) : List ℝ :=
  runFrom n A [] 0 I

/-- The online revenue `v′(I) = R(A, I)` of policy `A` on instance `I`:
`∑ᵢ fare(clsᵢ) · (accepted quantity)ᵢ`. -/
noncomputable def revenue (f₁ f₂ n : ℝ) (A : DetPolicy) (I : List Request) : ℝ :=
  (List.zipWith (fun q a => fare f₁ f₂ q.cls * a) I (accepted n A I)).sum

/-- The competitive ratio of a deterministic policy (p. 950): the infimum of `v′(I) / v*(I)` over all
instances with positive optimal offline revenue. -/
noncomputable def competitiveRatio (f₁ f₂ n : ℝ) (A : DetPolicy) : ℝ :=
  sInf {c : ℝ | ∃ I : List Request, 0 < optRevenue f₁ f₂ n I ∧
    c = revenue f₁ f₂ n A I / optRevenue f₁ f₂ n I}

/-- The competitive ratio of a randomized policy (p. 951; p. 954): a random choice `A ω` of a
deterministic policy, `ω` drawn from the probability measure `μ`; the infimum of
`E[v′(I)] / v*(I)` over all instances with positive optimal offline revenue. -/
noncomputable def randCompetitiveRatio (f₁ f₂ n : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (A : Ω → DetPolicy) : ℝ :=
  sInf {c : ℝ | ∃ I : List Request, 0 < optRevenue f₁ f₂ n I ∧
    c = (∫ ω, revenue f₁ f₂ n (A ω) I ∂μ) / optRevenue f₁ f₂ n I}

end RobustBooking.TwoFare


