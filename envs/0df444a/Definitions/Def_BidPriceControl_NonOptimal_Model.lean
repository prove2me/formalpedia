-- Prove2me | Definitions.Def_BidPriceControl_NonOptimal_Model
-- name    : BidPriceControl_NonOptimal_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-03T12:01:19.388684+00:00
-- url     : https://prove2.me/theorems/2776942c-b15a-45f0-88f4-06c4d5b70bb0
-- title:
--   Network revenue management: request set 𝒮, request laws, Bellman value J (2)–(3), admissible controls and their expected revenue, the control (4), bid-price controls (Definition 1)
-- statement:
--   An airline **network** has $m$ legs and $n$ origin–destination itineraries; $a_{ij} \in \mathbb{N}$ is the number of seats of leg $i$ used by itinerary $j$, $A = [a_{ij}]$, and $A^j$ is the $j$-th column. The state is the vector $y \in \mathbb{N}^m$ of remaining leg capacities; selling itinerary $j$ moves it to $y - A^j$. Time is counted **backwards**: period $t$ is the period with $t$ periods to go.
--
--   In each period one **request vector** $R_t = (R_t^1, \dots, R_t^n)$ arrives; $R_t^j > 0$ is a request for itinerary $j$ with revenue $R_t^j$, and $R_t = 0$ means no request. Requests lie in
--   $$\mathcal{S} = \{\alpha e : e \in E_n,\ \alpha \ge 0\},$$
--   where $E_n = \{e_0, e_1, \dots, e_n\}$, $e_0 = 0$ and $e_j$ the $j$-th unit vector: all components are nonnegative and at most one is positive. A law $P$ on $\mathbb{R}^n$ is a **request law** (`IsRequestLaw`) if it is a probability measure concentrated on $\mathcal{S}$ and every coordinate has a finite first moment. The laws are $F : \mathbb{N} \to \mathrm{Measure}(\mathbb{R}^n)$, $F_t$ being the law of $R_t$; periods are independent.
--
--   The **optimal expected revenue** $J_t(y)$ (`optValue`) solves the Bellman equations (2)–(3):
--   $$J_0(y) = 0, \qquad J_t(y) = \mathbb{E}_{r \sim F_t}\Big[\max\Big(J_{t-1}(y),\ \max_{j : A^j \le y} \big(r^j + J_{t-1}(y - A^j)\big)\Big)\Big],$$
--   the maximum over the decision set $\mathcal{U}(y) = \{e \in E_n : Ae \le y\}$ being taken for each realized request; `bellmanIntegrand t y` is the expression inside the expectation that defines $J_{t+1}(y)$.
--
--   A **control** $u$ assigns to each period $t$, capacity $y$ and request $r$ a decision $u_t(y, r) \in E_n$: reject ($e_0$) or sell itinerary $j$ ($e_j$). It is **admissible** if every decision lies in $\mathcal{U}(y)$ and, for each $t$ and $y$, the decision is a measurable function of $r$. Its **expected revenue** $V^u_t(y)$ (`controlValue`) is (2) with the maximum replaced by the decision of $u$:
--   $$V^u_0(y) = 0, \qquad V^u_t(y) = \mathbb{E}_{r \sim F_t}\big[r\,u_t(y, r) + V^u_{t-1}(y - A\,u_t(y, r))\big].$$
--
--   The control $u^*$ of **(4)** (`optimalControl`) accepts an arriving request for itinerary $j$ if and only if $A^j \le y$ and $r^j \ge J_{t-1}(y) - J_{t-1}(y - A^j)$.
--
--   **Bid prices** are real-valued functions $\mu_t(y) = (\mu_t^1(y), \dots, \mu_t^m(y))$ of the period and the capacity. The **bid-price control** of Definition 1, (1) (`bidPriceControl`) accepts an arriving request for itinerary $j$ if and only if $A^j \le y$ and
--   $$r^j \ge \sum_{i \in A^j} \sum_{h=0}^{a_{ij}-1} \mu_t^i(y - h e_i).$$
--
--   **Formalization Note.** Legs are `Fin m`, itineraries `Fin n`, `A : Fin m → Fin n → ℕ`, capacities `Fin m → ℕ`; `y - A^j` is only taken when $A^j \le y$. A decision is `Option (Fin n)` (`none` = $e_0$, `some j` = $e_j$); a control may depend on the whole request vector $r$ (the paper writes $u_k^j(x, r^j)$; on $\mathcal{S}$ this is no restriction). The inner maximum of $J$ is a `Finset.fold max` starting from the reject value. Admissible controls may, as $\mathcal{U}(y)$ allows, sell an itinerary with $r^j = 0$. Read literally, (1) and (4) set $u^j = 1$ for *every* itinerary whose zero fare meets its threshold, which is not a unit vector; both are encoded as "accept the arriving request" ($r^j > 0$), the least such $j$ (on $\mathcal{S}$ there is at most one). "$x - h$" in (1) is read as $y - h e_i$ (`Function.update y i (y i - h)`), $h$ fewer seats on leg $i$. Bid prices are arbitrary reals (Definition 1 does not require $\mu \ge 0$). The continuity of the marginals assumed in §1 is not part of `IsRequestLaw`: Proposition 1 does not use it and the §3.1 instance violates it.
-- source:
--   Talluri, van Ryzin, An Analysis of Bid-Price Controls for Network Revenue Management, Management Sci. 44(11), 1998, pp. 1579–1580 (§1 model, 𝒮, 𝒰(x), Definition 1, eq. (1)), p. 1580 (Bellman equations (2)–(3)), pp. 1580–1581 (Proposition 1, eq. (4))

import Mathlib

namespace BidPriceControl.NonOptimal

open MeasureTheory

/-- The request set `𝒮 = {α e : e ∈ E_n, α ≥ 0}` of Talluri–van Ryzin (1998, §1, p. 1579): a request
vector `r = (r¹, …, rⁿ)` has nonnegative components and at most one positive component (at most one
arrival per period; `r = 0` means no request, `r^j > 0` a request for itinerary `j` with revenue `r^j`). -/
def InS {n : ℕ} (r : Fin n → ℝ) : Prop :=
  (∀ j, 0 ≤ r j) ∧ ∀ j j', 0 < r j → 0 < r j' → j = j'

/-- The assumptions of Proposition 1 (§1, pp. 1579–1580, and §2, p. 1580) on the law `P` of one
period's request vector `R_t`: `P` is a probability measure on `ℝⁿ` whose support lies in `𝒮`, and
every `R_t^j` has a finite first moment. (No continuity of the marginals is assumed: Proposition 1
does not use it, and the instance of §3.1 has deterministic fares. Independence across periods is
built into the model: the recursions below integrate one period at a time.) -/
structure IsRequestLaw {n : ℕ} (P : Measure (Fin n → ℝ)) : Prop where
  isProbabilityMeasure : IsProbabilityMeasure P
  ae_inS : ∀ᵐ r ∂P, InS r
  integrable_coord : ∀ j : Fin n, Integrable (fun r : Fin n → ℝ => r j) P

/-- Column `A^j` of the seat matrix (`A i j = a_ij`, seats of leg `i` used by itinerary `j`), as a
capacity vector. -/
def column {m n : ℕ} (A : Fin m → Fin n → ℕ) (j : Fin n) : Fin m → ℕ := fun i => A i j

/-- `A^j ≤ y`: itinerary `j` fits in the remaining capacity `y` (the control `e_j ∈ 𝒰(y)`). -/
def Fits {m n : ℕ} (A : Fin m → Fin n → ℕ) (y : Fin m → ℕ) (j : Fin n) : Prop :=
  ∀ i, A i j ≤ y i

instance {m n : ℕ} (A : Fin m → Fin n → ℕ) (y : Fin m → ℕ) (j : Fin n) :
    Decidable (Fits A y j) := by
  unfold Fits; infer_instance

/-- The optimal expected revenue `J_t(y)` of the Bellman equations (2)–(3) (§2, p. 1580), time
counted backwards (`t` periods to go; `F t` is the law of the request `R_t` of the period with `t`
periods to go): `J_0(y) = 0` and `J_t(y) = E[max_{u ∈ 𝒰(y)} (R_t u + J_{t-1}(y − A u))]`, where
`𝒰(y) = {e ∈ E_n : A e ≤ y}` consists of `e_0 = 0` (reject, value `J_{t-1}(y)`) and every unit
vector `e_j` with `A^j ≤ y` (accept itinerary `j`, value `r^j + J_{t-1}(y − A^j)`). The maximum over
the finite set `𝒰(y)` is taken pointwise inside the expectation. -/
noncomputable def optValue {m n : ℕ} (A : Fin m → Fin n → ℕ) (F : ℕ → Measure (Fin n → ℝ)) :
    ℕ → (Fin m → ℕ) → ℝ
  | 0, _ => 0
  | t + 1, y =>
      ∫ r, (Finset.univ.filter (fun j => Fits A y j)).fold max (optValue A F t y)
        (fun j => r j + optValue A F t (y - column A j)) ∂(F (t + 1))

/-- The integrand of the Bellman equation (2) at `t + 1` periods to go and capacity `y`:
`max_{u ∈ 𝒰(y)} (r u + J_t(y − A u))`, so that `J_{t+1}(y) = ∫ bellmanIntegrand t y ∂F_{t+1}`. -/
noncomputable def bellmanIntegrand {m n : ℕ} (A : Fin m → Fin n → ℕ)
    (F : ℕ → Measure (Fin n → ℝ)) (t : ℕ) (y : Fin m → ℕ) (r : Fin n → ℝ) : ℝ :=
  (Finset.univ.filter (fun j => Fits A y j)).fold max (optValue A F t y)
    (fun j => r j + optValue A F t (y - column A j))

/-- A (Markov) control (§1, p. 1580): at `t` periods to go, remaining capacity `y` and request
`r`, the decision `u t y r` is `none` (the zero vector `e_0`: accept nothing) or `some j` (the unit
vector `e_j`: sell itinerary `j`). -/
abbrev Control (m n : ℕ) := ℕ → (Fin m → ℕ) → (Fin n → ℝ) → Option (Fin n)

/-- An admissible control: every decision lies in `𝒰(y) = {e ∈ E_n : A e ≤ y}` (an itinerary is
sold only if it fits in the remaining capacity), and for each period and capacity the decision is a
measurable function of the request (so that its expected revenue is a genuine expectation). -/
structure IsAdmissible {m n : ℕ} (A : Fin m → Fin n → ℕ) (u : Control m n) : Prop where
  fits : ∀ t y r j, u t y r = some j → Fits A y j
  measurableSet : ∀ t y j, MeasurableSet {r : Fin n → ℝ | u t y r = some j}

/-- The expected revenue `V^u_t(y)` of the control `u` with `t` periods to go and remaining capacity
`y`: the recursion (2) with the maximum replaced by the decision of `u` ("applying `u`", p. 1581):
`V_0(y) = 0`, `V_t(y) = E[R_t u_t(y, R_t) + V_{t-1}(y − A u_t(y, R_t))]`. -/
noncomputable def controlValue {m n : ℕ} (A : Fin m → Fin n → ℕ) (F : ℕ → Measure (Fin n → ℝ))
    (u : Control m n) : ℕ → (Fin m → ℕ) → ℝ
  | 0, _ => 0
  | t + 1, y =>
      ∫ r, (match u (t + 1) y r with
        | none => controlValue A F u t y
        | some j => r j + controlValue A F u t (y - column A j)) ∂(F (t + 1))

/-- The control `u*` of Proposition 1, (4) (pp. 1580–1581): at `t` periods to go and capacity `y`,
accept the arriving request for itinerary `j` (`r^j > 0`) iff `A^j ≤ y` and
`r^j ≥ J_{t-1}(y) − J_{t-1}(y − A^j)` (the least such `j`; on `𝒮` there is at most one);
otherwise reject. -/
noncomputable def optimalControl {m n : ℕ} (A : Fin m → Fin n → ℕ)
    (F : ℕ → Measure (Fin n → ℝ)) : Control m n := fun t y r =>
  let S := Finset.univ.filter (fun j => 0 < r j ∧ Fits A y j ∧
    optValue A F (t - 1) y - optValue A F (t - 1) (y - column A j) ≤ r j)
  if h : S.Nonempty then some (S.min' h) else none

/-- The bid-price sum of Definition 1, (1) (p. 1580), for bid prices `μ_t(y) = (μ_t^1(y), …,
μ_t^m(y))`: `∑_{i ∈ A^j} ∑_{h=0}^{a_ij − 1} μ_t^i(y − h e_i)`, where `y − h e_i` is the capacity
vector with `h` fewer seats on leg `i` (legs not used by `j` contribute an empty inner sum). -/
def bidPriceSum {m n : ℕ} (A : Fin m → Fin n → ℕ) (μ : ℕ → (Fin m → ℕ) → Fin m → ℝ)
    (t : ℕ) (y : Fin m → ℕ) (j : Fin n) : ℝ :=
  ∑ i, ∑ h ∈ Finset.range (A i j), μ t (Function.update y i (y i - h)) i

/-- The bid-price control of Definition 1, (1) (p. 1580), with bid prices
`μ : ℕ → (Fin m → ℕ) → (Fin m → ℝ)` (arbitrary real values, depending on the time-to-go and on the
remaining capacity): the arriving request for itinerary `j` (`r^j > 0`) is accepted iff `A^j ≤ y`
and `r^j ≥ ∑_{i ∈ A^j} ∑_{h=0}^{a_ij − 1} μ_t^i(y − h e_i)` (the least such `j`; on `𝒮` there is at
most one); otherwise the request is rejected. -/
noncomputable def bidPriceControl {m n : ℕ} (A : Fin m → Fin n → ℕ)
    (μ : ℕ → (Fin m → ℕ) → Fin m → ℝ) : Control m n := fun t y r =>
  let S := Finset.univ.filter (fun j => 0 < r j ∧ Fits A y j ∧ bidPriceSum A μ t y j ≤ r j)
  if h : S.Nonempty then some (S.min' h) else none

end BidPriceControl.NonOptimal


