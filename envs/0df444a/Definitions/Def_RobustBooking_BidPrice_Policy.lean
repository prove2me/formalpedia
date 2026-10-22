-- Prove2me | Definitions.Def_RobustBooking_BidPrice_Policy
-- name    : RobustBooking_BidPrice_Policy
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-03T00:37:42.130275+00:00
-- url     : https://prove2.me/theorems/ea6489de-b838-4f3a-a4df-b037e628f64f
-- title:
--   Deterministic and randomized online booking policies, their runs and revenues, and competitive ratios over a fare set
-- statement:
--   **Online booking policies.** A **deterministic online policy** $A$ is a rule that, when a request arrives, proposes a quantity to accept from the history (the earlier requests, each with the quantity accepted from it, oldest first) and the current request; it never sees future requests or the length of the instance. Running $A$ with capacity $n$ on an instance processes the requests in order; each proposal is clipped to $[0, \min(d, n - \hat q)]$, where $\hat q$ is the total quantity already accepted, so decisions are irrevocable and capacity is never exceeded. The **revenue** $v'_A(I)$ is $\sum_i O_i a_i$ over the accepted quantities $a_i$. For a history, $\hat q$ is its total accepted quantity and $\hat q(f)$ the quantity accepted from requests with fare at most $f$.
--
--   For a fare set $F$ the **competitive ratio** of $A$ is
--   $$\mathrm{CR}_F(A) = \inf\Big\{\frac{v'_A(I)}{v^*(I)} \;:\; I \text{ admissible for } F,\ v^*(I) > 0\Big\}.$$
--   A **randomized policy** is a random choice $A(\omega)$ of a deterministic policy, $\omega$ drawn from a probability measure $\mu$ on a measurable space $\Omega$; its competitive ratio replaces $v'_A(I)$ by the expectation $\mathbb{E}_\mu[v'_{A(\omega)}(I)]$.
--
--   **Formalization Note.** Every function `List (Request × ℝ) → Request → ℝ` is a policy and every nonanticipative feasible policy is one (clipping makes any proposal feasible). The competitive ratios are real `sInf`s over admissible instances with positive optimum; for $n > 0$ and $F$ containing a positive fare the set is nonempty (a single request), and when all fares in $F$ are nonnegative it is bounded below by $0$. The expectation is a Bochner integral: theorems that use it assume $\omega \mapsto v'_{A(\omega)}(I)$ measurable for every admissible $I$; the revenue is then bounded (by $n \sup F$ for bounded $F$), hence integrable, so the integral is a genuine expectation. No finiteness of the randomization is assumed.
-- source:
--   Ball, Queyranne, Toward Robust Revenue Management: Competitive Analysis of Online Booking, Oper. Res. 57(4), 2009, pp. 950–951 (online algorithms, competitive ratio, randomized competitive ratio), p. 954 (randomized policies as random choices of deterministic ones), p. 956 (q̂ and q̂(f))

import Mathlib
import Definitions.Def_RobustBooking_BidPrice_Model

namespace RobustBooking.BidPrice

open MeasureTheory

/-- A deterministic online booking policy (p. 950: "a decision on each successive input must be
made at the time the input is received"). When a request arrives, the policy sees the history of
the earlier requests, each with the quantity that was accepted from it, and the current request,
and proposes a quantity to accept. It never sees future requests or the length of the instance.
(The accepted quantities in the history are themselves functions of the earlier requests, so this
is the class of all nonanticipative deterministic policies.) -/
structure DetPolicy where
  /-- `decide hist q` is the proposed accepted quantity for the current request `q`, given the
  history `hist` of earlier requests paired with their accepted quantities, oldest first. -/
  decide : List (Request × ℝ) → Request → ℝ

/-- `q̂`: total quantity accepted in a history (p. 956). -/
def acceptedTotal (hist : List (Request × ℝ)) : ℝ :=
  (hist.map Prod.snd).sum

/-- `q̂(f)`: total quantity accepted in a history from requests with fare `≤ f` (p. 956). -/
noncomputable def acceptedAtOrBelow (f : ℝ) (hist : List (Request × ℝ)) : ℝ :=
  ((hist.filter fun e => decide (e.1.fare ≤ f)).map Prod.snd).sum

/-- One step of the run: the proposal `p` of the policy on request `q` is clipped to the feasible
interval `[0, min (qty q) (n - accepted so far)]`, so decisions are irrevocable, partial acceptance
is allowed, and capacity `n` is never exceeded. -/
noncomputable def runFrom (P : DetPolicy) (n : ℝ) :
    List (Request × ℝ) → List Request → List (Request × ℝ)
  | hist, [] => hist
  | hist, q :: rest =>
    let a := max 0 (min (P.decide hist q) (min q.qty (n - acceptedTotal hist)))
    runFrom P n (hist ++ [(q, a)]) rest

/-- The run of policy `P` with capacity `n` on instance `I`: every request of `I`, in arrival
order, paired with the quantity accepted from it. -/
noncomputable def run (P : DetPolicy) (n : ℝ) (I : List Request) : List (Request × ℝ) :=
  runFrom P n [] I

/-- The revenue `v′(I)` of policy `P` with capacity `n` on instance `I`:
`∑ fare · accepted quantity`. -/
noncomputable def revenue (n : ℝ) (P : DetPolicy) (I : List Request) : ℝ :=
  ((run P n I).map fun e => e.1.fare * e.2).sum

/-- The competitive ratio of a deterministic policy (p. 950) on the problem whose instances have
all fares in `F`: `inf_I v′(I) / v*(I)`, the infimum taken over all such instances with positive
offline optimum. For the bid-price problem `F = [f_min, f_max]`. For `0 < n` and `F` containing a
positive fare this set is nonempty (a single request) and bounded below by `0` when all fares in
`F` are nonnegative (revenues are then nonnegative), so the real `sInf` is the true infimum. -/
noncomputable def competitiveRatioOn (F : Set ℝ) (n : ℝ) (P : DetPolicy) : ℝ :=
  sInf {c : ℝ | ∃ I : List Request, FaresIn F I ∧ 0 < offlineOpt n I ∧
    c = revenue n P I / offlineOpt n I}

/-- The competitive ratio of a randomized policy (p. 951, p. 954) on the problem whose instances
have all fares in `F`: the policy is a random choice `A ω` of a deterministic policy, `ω` drawn from
a probability measure `μ` on a measurable space `Ω`; its value is `inf_I E[v′(I)] / v*(I)` over such
instances with positive offline optimum, where `E[v′(I)] = ∫ ω, revenue n (A ω) I ∂μ`. Statements
using it assume that each `ω ↦ revenue n (A ω) I` is measurable; for a bounded fare set the
revenue is bounded, so it is then integrable. -/
noncomputable def competitiveRatioRandOn (F : Set ℝ) (n : ℝ) {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) (A : Ω → DetPolicy) : ℝ :=
  sInf {c : ℝ | ∃ I : List Request, FaresIn F I ∧ 0 < offlineOpt n I ∧
    c = (∫ ω, revenue n (A ω) I ∂μ) / offlineOpt n I}

end RobustBooking.BidPrice


