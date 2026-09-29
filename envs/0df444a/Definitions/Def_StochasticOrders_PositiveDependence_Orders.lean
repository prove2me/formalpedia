-- Prove2me | Definitions.Def_StochasticOrders_PositiveDependence_Orders
-- name    : StochasticOrders_PositiveDependence_Orders
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T23:15:42.319523+00:00
-- url     : https://prove2.me/theorems/946a3029-eeb0-47cf-96db-2aa31c986e78
-- title:
--   The PQD order and the supermodular order, and their joint survival/distribution functions
-- statement:
--   Let $X$ and $Y$ be two $\iota$-indexed (finite-dimensional) random vectors with laws $P$, $Q$
--   on $\iota \to \mathbb{R}$. `survivalVec` and `cdfVec` are the joint survival and distribution
--   functions $\bar F(x) = P\{Y_i > x_i \text{ for all } i\}$, $F(x) = P\{Y_i \le x_i \text{ for
--   all } i\}$, cast to reals (both lie in $[0,1]$ under a probability measure).
--
--   $X$ is **smaller than $Y$ in the PQD order**, written $X \le_{PQD} Y$, if
--
--   $$\bar F(x) \le \bar G(x) \text{ and } F(x) \le G(x) \quad \text{for every } x \in \mathbb{R}^\iota,$$
--
--   the general multivariate form of Lehmann's positive-quadrant-dependence order. (It follows,
--   though it is not assumed, that $X$ and $Y$ then share the same univariate marginals.)
--
--   $X$ is **smaller than $Y$ in the supermodular order**, written $X \le_{sm} Y$, if
--
--   $$E[\varphi(X)] \le E[\varphi(Y)] \quad \text{for every supermodular } \varphi : \mathbb{R}^\iota
--     \to \mathbb{R} \text{ for which the two expectations exist,}$$
--
--   where $\varphi$ supermodular means $\varphi(x)+\varphi(y) \le \varphi(x\wedge y)+\varphi(x\vee
--   y)$ for the coordinatewise meet/join — the same function-level notion the platform's
--   Topkis/Supermodularity series already formalizes for games and lattices
--   (`Supermodularity.Monotonicity.SupermodularOn`, reused here as a `reference` item with
--   `S := Set.univ`, its plain unrelativized form). Since $\varphi_x = I_{\{y:y>x\}}$ and
--   $\psi_x = I_{\{y:y\le x\}}$ are themselves supermodular, $X \le_{sm} Y \implies X \le_{PQD} Y$
--   (Eq. 9.A.17) — the supermodular order is a sufficient condition for positive dependence, and of
--   independent interest in its own right.
--
--   **Formalization Note** Both orders are stated directly on the two random vectors' **laws**
--   $P, Q$ (measures on $\iota \to \mathbb{R}$) rather than on random variables composed with an
--   ambient probability space — the book's own comparisons never reference a joint law of $X$ and
--   $Y$ together, only their separate distributions, so this is the natural Mathlib-idiomatic
--   shape (and it is what lets Theorem 9.A.9(c)'s marginalization and (a)'s coordinatewise
--   composition be stated as plain pushforwards, `Measure.map`). The index type $\iota$ is left an
--   arbitrary `Fintype` (rather than fixed to `Fin n`) precisely so the same `SupermodularOrder`/
--   `PQDOrder` declarations serve both a full $n$-vector and any marginal sub-vector obtained by
--   restricting to a subset $I$ of coordinates, without a separate definition for each dimension.
-- source:
--   Shaked & Shanthikumar, Stochastic Orders, Springer 2007, p. 392 (Eqs. 9.A.13-9.A.14), p. 395 (Eq. 9.A.17)

import Mathlib
import Definitions.Def_Supermodularity_Monotonicity_SupermodularOn

namespace StochasticOrders.PositiveDependence

open MeasureTheory Supermodularity.Monotonicity

variable {ι : Type*} [Fintype ι]

/-- The joint survival function `P{Yᵢ > xᵢ for all i}` of the law `P` of a (finite-dimensional)
random vector indexed by `ι`, as a real number (Shaked & Shanthikumar, *Stochastic Orders*,
Springer 2007, p. 392, notation `F̄`). Indexing by an arbitrary finite `ι` (rather than fixing
`Fin n`) lets the same definition serve both the full vector and any sub-vector `X_I` obtained by
marginalizing onto a subset `I` of coordinates (Theorem 9.A.9(c)). -/
noncomputable def survivalVec (P : Measure (ι → ℝ)) (x : ι → ℝ) : ℝ :=
  (P {y : ι → ℝ | ∀ i, x i < y i}).toReal

/-- The joint distribution function `P{Yᵢ ≤ xᵢ for all i}` of the law `P` of a (finite-dimensional)
random vector indexed by `ι`, as a real number (Shaked & Shanthikumar, *Stochastic Orders*,
Springer 2007, p. 392, notation `F`). -/
noncomputable def cdfVec (P : Measure (ι → ℝ)) (x : ι → ℝ) : ℝ :=
  (P {y : ι → ℝ | ∀ i, y i ≤ x i}).toReal

/-- The PQD order `X ≤PQD Y` in its general multivariate form (Shaked & Shanthikumar,
*Stochastic Orders*, Springer 2007, p. 392, Eqs. (9.A.13)-(9.A.14)): the law `P` of `X` is smaller
than the law `Q` of `Y` in the PQD order if the joint survival functions and the joint
distribution functions are both pointwise ordered. (It follows, though it is not assumed, that
`X` and `Y` then share the same univariate marginals.) -/
def PQDOrder (P Q : Measure (ι → ℝ)) : Prop :=
  (∀ x : ι → ℝ, survivalVec P x ≤ survivalVec Q x) ∧
  (∀ x : ι → ℝ, cdfVec P x ≤ cdfVec Q x)

/-- The supermodular order `X ≤sm Y` (Shaked & Shanthikumar, *Stochastic Orders*, Springer 2007,
p. 395): the law `P` of a random vector `X` indexed by `ι` is smaller than the law `Q` of `Y` in
the supermodular order if `E[φ(X)] ≤ E[φ(Y)]` for every supermodular `φ : (ι → ℝ) → ℝ` for which
the two expectations exist, where supermodularity is `ι → ℝ`'s own coordinatewise lattice
structure (`⊔`/`⊓` = coordinatewise max/min), exactly the book's `φ(x)+φ(y) ≤ φ(x∧y)+φ(x∨y)`.
`SupermodularOn` is reused from the platform's Topkis/Supermodularity series
(`Supermodularity.Monotonicity.SupermodularOn`, `S := Set.univ`), the same function-level
predicate on a general lattice. -/
def SupermodularOrder (P Q : Measure (ι → ℝ)) : Prop :=
  ∀ φ : (ι → ℝ) → ℝ, SupermodularOn φ Set.univ → Integrable φ P → Integrable φ Q →
    ∫ x, φ x ∂P ≤ ∫ x, φ x ∂Q

end StochasticOrders.PositiveDependence


