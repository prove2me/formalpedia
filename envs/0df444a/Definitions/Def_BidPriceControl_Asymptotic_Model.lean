-- Prove2me | Definitions.Def_BidPriceControl_Asymptotic_Model
-- name    : BidPriceControl_Asymptotic_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-03T11:25:14.032983+00:00
-- url     : https://prove2.me/theorems/6f4feca9-5d46-468f-83f4-80e7e7dab57a
-- title:
--   Network revenue management model: request set 𝒮, request laws, Bellman value J (2)–(3), relaxed value J̄ (8), θ-scaling (12), fixed-bid-price heuristic J^H, Nⁱ, Var(Y_ijt)
-- statement:
--   An airline **network** has $m$ legs and $n$ origin–destination itineraries. Itinerary $j$ uses $a_{ij} \in \mathbb{N}$ seats of leg $i$; $A = [a_{ij}]$ and $A^j$ is its $j$-th column. The state is the vector $y \in \mathbb{N}^m$ of remaining leg capacities, and selling itinerary $j$ moves it to $y - A^j$. Time is counted **backwards**: period $t$ is the period with $t$ periods to go.
--
--   Each period brings one **request vector** $R_t = (R_t^1, \dots, R_t^n)$ with values in
--   $$\mathcal{S} = \{\alpha e : e \in E_n,\ \alpha \ge 0\},\qquad E_n = \{0, e_1, \dots, e_n\},$$
--   so every component is nonnegative and at most one is positive. $R_t^j > 0$ is a request for itinerary $j$ with revenue $R_t^j$, and $R_t = 0$ means no request. A law $P$ on $\mathbb{R}^n$ is a **request law** (`IsRequestLaw`) if it satisfies the standing assumptions of §1: it is a probability measure concentrated on $\mathcal{S}$; each marginal distribution function $r \mapsto P(R^j \le r)$ is continuous on $(0, +\infty)$, that is, no marginal has an atom at a positive value; and each coordinate has a finite mean. The laws are $F : \mathbb{N} \to \mathrm{Measure}(\mathbb{R}^n)$, $F_t$ being the law of $R_t$, and the periods are independent.
--
--   The **optimal expected revenue** $J_t(y)$ is the solution of the Bellman equations (2)–(3),
--   $$J_0(y) = 0,\qquad J_t(y) = \mathbb{E}_{r \sim F_t}\Big[\max\Big(J_{t-1}(y),\ \max_{j:\,A^j \le y}\big(r^j + J_{t-1}(y - A^j)\big)\Big)\Big].$$
--   The inner maximum runs over the control set $\mathcal{U}(y) = \{e \in E_n : Ae \le y\}$ (reject, or accept an itinerary that fits) and is taken separately for each realized request.
--
--   For bid prices $\mu \in \mathbb{R}^m$ write $\mu A^j = \sum_i \mu^i a_{ij}$. The **relaxed value** is the closed form (8),
--   $$\bar J_k(x, \mu) = \sum_{t=1}^{k} \sum_{j=1}^{n} \mathbb{E}\,(R_t^j - \mu A^j)^+ + \mu x.$$
--   A vector $\mu^*$ is an **optimal solution of (9)**, $v_k(x) = \min_{\mu \ge 0} \bar J_k(x, \mu)$, if $\mu^* \ge 0$ and $\bar J_k(x, \mu^*) \le \bar J_k(x, \mu)$ for every $\mu \ge 0$.
--
--   The **$\theta$-scaled problem** (12) has capacity $\theta x$, horizon $\theta k$ and request laws $R_t(\theta) \sim F_{\lceil t/\theta \rceil}$.
--
--   The **fixed-bid-price heuristic (H)** with bid prices $\mu$ accepts a request for itinerary $j$ with revenue $r$ if and only if there is sufficient capacity ($A^j \le y$) and $r > \mu A^j$. Its **expected revenue** $J^H_K(y)$ over $K$ periods with laws $G$ is the expectation of its pathwise revenue under the product law of $K$ independent periods. The $s$-th period in chronological order ($s = 0, \dots, K - 1$) has law $G_{K-s}$. For the proof of Theorem 1 the file also defines three quantities:
--   - the seat count $N^i = \sum_{s} \sum_j \mathbf{1}\{R^j > \mu A^j\}\, a_{ij}$ of an uncapacitated system that accepts every request above its bid price;
--   - the probability $p_{tj} = P(R_t^j > \mu A^j)$;
--   - the variance $\operatorname{Var}(Y_{ijt}) = a_{ij}^2\, p_{tj}(1 - p_{tj})$ of $Y_{ijt} = \mathbf{1}\{R_t^j > \mu A^j\}\, a_{ij}$.
--
--   **Formalization Note.** Legs are `Fin m`, itineraries `Fin n`, `A : Fin m → Fin n → ℕ`, capacities `Fin m → ℕ`. The capacity subtraction `y - A^j` in `ℕ` is only taken when `A^j ≤ y`. `optValue A F t y` is $J_t(y)$, defined by recursion on $t$; its inner maximum is a `Finset.fold max` starting from the reject value. Accepting an itinerary at $r^j = 0$ is allowed, as in $\mathcal{U}(y)$; it never helps. `relaxedValue` is the evaluated form (8); the paper defines $\bar J$ as the maximum (7) and evaluates it as (8). `scaledLaw F θ t = F ((t + θ - 1) / θ)` equals $F_{\lceil t/\theta \rceil}$ for $\theta \ge 1$. `heuristicRun` sells the least acceptable itinerary; on $\mathcal{S}$ with $\mu \ge 0$ at most one itinerary is acceptable. `heuristicValue` integrates it against `Measure.pi`. The bound $R_t^j \le C$ of the asymptotic results is not part of `IsRequestLaw`; each theorem that uses it states it.
-- source:
--   Talluri, van Ryzin, An Analysis of Bid-Price Controls for Network Revenue Management, Management Sci. 44(11), 1998, pp. 1579–1580 (§1: model, standing assumptions, 𝒰(x)); p. 1580 (Bellman equations (2)–(3)); p. 1583 (§4.1, (7)–(9)); p. 1584 (§4.2, heuristic H, scaling (12)); p. 1585 (Nⁱ, Y_ijt)

import Mathlib

namespace BidPriceControl.Asymptotic

open MeasureTheory

/-- The request set `𝒮 = {α e : e ∈ E_n, α ≥ 0}` of Talluri–van Ryzin (1998, §1, p. 1579): a request
vector `r = (r¹, …, rⁿ)` has nonnegative components and at most one positive component (at most one
arrival per period; `r = 0` means no request, `r^j > 0` a request for itinerary `j` with revenue `r^j`). -/
def InS {n : ℕ} (r : Fin n → ℝ) : Prop :=
  (∀ j, 0 ≤ r j) ∧ ∀ j j', 0 < r j → 0 < r j' → j = j'

/-- The standing assumptions of §1 (pp. 1579–1580) on the law `P` of one period's request vector
`R_t`: `P` is a probability measure on `ℝⁿ` supported on `𝒮`; every marginal distribution function
`F_t^j(r) = P(R_t^j ≤ r)` is continuous on `(0, +∞)`, i.e. no marginal has an atom at a positive
value; and every `R_t^j` has a finite mean. (Independence across periods is built into the model:
the dynamic program integrates one period at a time and the heuristic runs on a product measure.)
The bounded-support assumption of the asymptotic results, `P(R_t^j ≤ C) = 1`, is stated separately. -/
structure IsRequestLaw {n : ℕ} (P : Measure (Fin n → ℝ)) : Prop where
  isProbabilityMeasure : IsProbabilityMeasure P
  ae_inS : ∀ᵐ r ∂P, InS r
  noAtom_pos : ∀ j : Fin n, ∀ s : ℝ, 0 < s → P {r | r j = s} = 0
  integrable_coord : ∀ j : Fin n, Integrable (fun r : Fin n → ℝ => r j) P

/-- The bid-price sum `μ A^j = ∑_i μ^i a_ij` of itinerary `j` for the leg bid-price vector `μ`
(`A : Fin m → Fin n → ℕ`, `A i j = a_ij` seats of leg `i` used by itinerary `j`). -/
def bidSum {m n : ℕ} (A : Fin m → Fin n → ℕ) (μ : Fin m → ℝ) (j : Fin n) : ℝ :=
  ∑ i, μ i * (A i j : ℝ)

/-- Column `A^j` of the seat matrix, as a capacity vector. -/
def column {m n : ℕ} (A : Fin m → Fin n → ℕ) (j : Fin n) : Fin m → ℕ := fun i => A i j

/-- `A^j ≤ y`: itinerary `j` fits in the remaining capacity `y` (the control `e_j ∈ 𝒰(y)`). -/
def Fits {m n : ℕ} (A : Fin m → Fin n → ℕ) (y : Fin m → ℕ) (j : Fin n) : Prop :=
  ∀ i, A i j ≤ y i

instance {m n : ℕ} (A : Fin m → Fin n → ℕ) (y : Fin m → ℕ) (j : Fin n) :
    Decidable (Fits A y j) := by
  unfold Fits; infer_instance

/-- The optimal expected revenue `J_t(y)` of the Bellman equations (2)–(3) (§2, p. 1580), time
counted backwards (`t` periods to go; `F t` is the law of the request `R_t` of the period with `t`
periods to go):
`J_0(y) = 0` and `J_t(y) = E[max_{u ∈ 𝒰(y)} (R_t u + J_{t-1}(y − A u))]`, where
`𝒰(y) = {e ∈ E_n : A e ≤ y}` consists of `e_0 = 0` (reject, value `J_{t-1}(y)`) and every unit
vector `e_j` with `A^j ≤ y` (accept itinerary `j`, value `r^j + J_{t-1}(y − A^j)`). The maximum over
the finite set `𝒰(y)` is taken pointwise inside the expectation, which is the maximum over control
functions `u_t(y, ·)` of (2). -/
noncomputable def optValue {m n : ℕ} (A : Fin m → Fin n → ℕ) (F : ℕ → Measure (Fin n → ℝ)) :
    ℕ → (Fin m → ℕ) → ℝ
  | 0, _ => 0
  | t + 1, y =>
      ∫ r, (Finset.univ.filter (fun j => Fits A y j)).fold max (optValue A F t y)
        (fun j => r j + optValue A F t (y - column A j)) ∂(F (t + 1))

/-- The relaxed value `J̄_k(x, μ)` in its closed form (8) (§4.1, p. 1583):
`J̄_k(x, μ) = ∑_{t=1}^k ∑_{j=1}^n E(R_t^j − μA^j)^+ + μx`. -/
noncomputable def relaxedValue {m n : ℕ} (A : Fin m → Fin n → ℕ) (F : ℕ → Measure (Fin n → ℝ))
    (k : ℕ) (x : Fin m → ℕ) (μ : Fin m → ℝ) : ℝ :=
  (∑ t ∈ Finset.Icc 1 k, ∑ j, ∫ r, max (r j - bidSum A μ j) 0 ∂(F t)) + ∑ i, μ i * (x i : ℝ)

/-- `μ*` is an optimal solution of the convex program (9), `v_k(x) = min_{μ ≥ 0} J̄_k(x, μ)`
(§4.1, p. 1583): `μ* ≥ 0` and `J̄_k(x, μ*) ≤ J̄_k(x, μ)` for every `μ ≥ 0`. Then
`v_k(x) = relaxedValue A F k x μ*`. -/
def IsRelaxedMinimizer {m n : ℕ} (A : Fin m → Fin n → ℕ) (F : ℕ → Measure (Fin n → ℝ))
    (k : ℕ) (x : Fin m → ℕ) (μstar : Fin m → ℝ) : Prop :=
  0 ≤ μstar ∧ ∀ μ : Fin m → ℝ, 0 ≤ μ → relaxedValue A F k x μstar ≤ relaxedValue A F k x μ

/-- The laws of the `θ`-scaled problem (12) (§4.2, p. 1584): `R_t(θ) =_D R_{⌈t/θ⌉}`. In `ℕ`,
`⌈t/θ⌉ = (t + θ - 1) / θ` for `θ ≥ 1`; for `t ∈ [1, θk]` the index lies in `[1, k]`. -/
def scaledLaw {n : ℕ} (F : ℕ → Measure (Fin n → ℝ)) (θ : ℕ) (t : ℕ) : Measure (Fin n → ℝ) :=
  F ((t + θ - 1) / θ)

/-- The itineraries the fixed-bid-price heuristic (H) would accept for request `r` at remaining
capacity `y`: those with `r^j > μA^j` (strict) and sufficient capacity `A^j ≤ y`. On `𝒮` there is
at most one, since `μA^j ≥ 0` for `μ ≥ 0` forces `r^j > 0`. -/
noncomputable def acceptSet {m n : ℕ} (A : Fin m → Fin n → ℕ) (μ : Fin m → ℝ) (y : Fin m → ℕ)
    (r : Fin n → ℝ) : Finset (Fin n) :=
  Finset.univ.filter (fun j => bidSum A μ j < r j ∧ Fits A y j)

/-- Pathwise revenue of the fixed-bid-price heuristic (H) (§4.2, p. 1584) with bid prices `μ` on a
chronological list of request vectors, starting from capacity `y`: if some itinerary is acceptable
(`r^j > μA^j` and `A^j ≤ y`), the least such `j` is sold, its revenue `r^j` collected and the
capacity reduced to `y − A^j`; otherwise the request is rejected. -/
noncomputable def heuristicRun {m n : ℕ} (A : Fin m → Fin n → ℕ) (μ : Fin m → ℝ) :
    List (Fin n → ℝ) → (Fin m → ℕ) → ℝ
  | [], _ => 0
  | r :: rs, y =>
      if h : (acceptSet A μ y r).Nonempty then
        r ((acceptSet A μ y r).min' h) +
          heuristicRun A μ rs (y - column A ((acceptSet A μ y r).min' h))
      else heuristicRun A μ rs y

/-- The joint law of the request vectors of a `K`-period horizon with per-period laws `G`
(indexed by time-to-go): independent periods, coordinate `s : Fin K` being the `s`-th period in
chronological order, which has `K - s` periods to go. -/
noncomputable def pathMeasure {n : ℕ} (G : ℕ → Measure (Fin n → ℝ)) (K : ℕ) :
    Measure (Fin K → Fin n → ℝ) :=
  Measure.pi (fun s : Fin K => G (K - (s : ℕ)))

/-- `J^H_K(y)`: the expected revenue of the fixed-bid-price heuristic with bid prices `μ`, horizon
`K`, per-period laws `G` and initial capacity `y` (§4.2, p. 1584). -/
noncomputable def heuristicValue {m n : ℕ} (A : Fin m → Fin n → ℕ) (G : ℕ → Measure (Fin n → ℝ))
    (K : ℕ) (y : Fin m → ℕ) (μ : Fin m → ℝ) : ℝ :=
  ∫ ω, heuristicRun A μ (List.ofFn ω) y ∂(pathMeasure G K)

/-- `N^i` of the proof of Theorem 1 (p. 1585): `N^i = ∑_t ∑_j 1{R_t^j > μA^j} a_ij`, the number of
leg-`i` seats sold by the uncapacitated alternate system that accepts every request above its bid
price, as a random variable on the path space `Fin K → ℝⁿ`. -/
noncomputable def seatsCounted {m n K : ℕ} (A : Fin m → Fin n → ℕ) (μ : Fin m → ℝ) (i : Fin m)
    (ω : Fin K → Fin n → ℝ) : ℝ :=
  ∑ s, ∑ j, if bidSum A μ j < ω s j then (A i j : ℝ) else 0

/-- `P(R_t^j > μA^j)` under the law `F t`. -/
noncomputable def exceedProb {m n : ℕ} (A : Fin m → Fin n → ℕ) (F : ℕ → Measure (Fin n → ℝ))
    (μ : Fin m → ℝ) (t : ℕ) (j : Fin n) : ℝ :=
  (F t {r | bidSum A μ j < r j}).toReal

/-- `Var(Y_ijt)` for `Y_ijt = 1{R_t^j > μA^j} a_ij` (p. 1585), computed as the variance of `a_ij`
times a Bernoulli variable: `a_ij² p (1 − p)` with `p = P(R_t^j > μA^j)`. -/
noncomputable def indicatorVar {m n : ℕ} (A : Fin m → Fin n → ℕ) (F : ℕ → Measure (Fin n → ℝ))
    (μ : Fin m → ℝ) (i : Fin m) (t : ℕ) (j : Fin n) : ℝ :=
  (A i j : ℝ) ^ 2 * exceedProb A F μ t j * (1 - exceedProb A F μ t j)

end BidPriceControl.Asymptotic


