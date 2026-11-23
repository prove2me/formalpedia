-- Prove2me | Definitions.Def_MaxSpectralRisk_Duality_Supplement_Finite
-- name    : MaxSpectralRisk_Duality_Supplement_Finite
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T10:07:18.010308+00:00
-- url     : https://prove2.me/theorems/2cf1f0b9-55f6-4668-959a-cfb2c59a700a
-- title:
--   §6 — finite MES, normalized dual polyhedron, active vertices and Hadamard derivative interface
-- statement:
--   The finite carriers are $\mathcal X=\mathrm{Fin}(m+1)$ and $\mathcal Y=\mathrm{Fin}(n+1)$. A probability vector is the published predicate of nonnegative coordinates summing to one, and $K$ is the product of the two closed probability simplices. A vector $p$ represents the measure $\sum_i p_i\delta_i$. The finite value is $V_\alpha$ of these measures, using (11).
--
--   The primal model (15) consists of nonnegative arrays $(\pi,\Theta)$ with row sums $\mu$, column sums $\nu$, total $\Theta$ mass one and $\Theta_{ij}\le(1-\alpha)^{-1}\pi_{ij}$, and objective $\sum_{ij}L_{ij}\Theta_{ij}$. These constraints are defined for use in the proof; their equivalence with the risk formulation is not assumed.
--
--   For a loss matrix $L=(L_{ij})$, the normalized dual feasible polyhedron consists of $z=(\varphi,\psi,\rho,\beta)$ satisfying
--   $$
--   \varphi_0=0,\qquad (1-\alpha)(\varphi_i+\psi_j)-\rho_{ij}\ge0,\qquad
--   \rho_{ij}+\beta\ge L_{ij},\qquad\rho_{ij}\ge0.
--   $$
--   Its vertices are its actual extreme points in the product real vector space. Set $q_z(\mu,\nu)=\varphi\cdot\mu+\psi\cdot\nu+\beta$, $I(\mu,\nu)=\{z\text{ a vertex}:q_z(\mu,\nu)=V_\alpha(\mu,\nu)\}$ and
--   $$
--   V'_\alpha(\mu,\nu;h_\mu,h_\nu)=\inf_{z\in I(\mu,\nu)}(\varphi\cdot h_\mu+\psi\cdot h_\nu).
--   $$
--   Theorem 3 asserts finiteness, nonemptiness and attainment for this last infimum. The generic Hadamard interface tests every positive sequence $t_k\to0$ and every direction sequence $h_k\to h$ with $\theta+t_kh_k\in K$, requiring the difference quotients to converge to $V'_\alpha(\theta;h)$, a continuous, possibly nonlinear function of $h$.
--
--   **Formalization Note** Coordinate zero is the paper's coordinate one. Every finite carrier supporting a probability measure is nonempty, so using successor cardinalities loses no source instance. Values start in `EReal`; the real coordinate is used only on $K$, where (16) and Theorem 3 assert finiteness. Infima outside the finite nonempty active sets are unused. The standalone Hadamard predicate is an interface for (18), not an assumed differentiability result.
-- source:
--   Ghossoub, Hall, Saunders, Maximum Spectral Measures of Risk with given Risk Factor Marginal Distributions, arXiv:2010.14673v1, pp. 18–19, §6, dual preceding (16), (16), (18)

import Mathlib
import Definitions.Def_CalibratedCE_Forecast_IsDist
import Definitions.Def_MaxSpectralRisk_Duality_Supplement_Valpha

namespace MaxSpectralRisk.Duality.Supplement

open MeasureTheory Filter Topology

/-- §6: nonempty finite carriers, indexed from zero instead of one.
Every finite carrier admitting a probability measure has this form up to relabeling. -/
abbrev Marginals (m n : ℕ) := (Fin (m + 1) → ℝ) × (Fin (n + 1) → ℝ)

/-- The set K in Theorem 3, including its boundary. -/
def K {m n : ℕ} : Set (Marginals m n) :=
  {θ | CalibratedCE.Forecast.IsDist θ.1 ∧ CalibratedCE.Forecast.IsDist θ.2}

/-- The measure represented by a vector. Only probability vectors are used in results. -/
noncomputable def vectorMeasure {k : ℕ} (p : Fin k → ℝ) : Measure (Fin k) :=
  ∑ i, ENNReal.ofReal (p i) • Measure.dirac i

/-- The MES (11), on finite spaces; it is not defined by the dual vertex formula. -/
noncomputable def finiteV {m n : ℕ} (α : ℝ)
    (L : Fin (m + 1) → Fin (n + 1) → ℝ) (θ : Marginals m n) : EReal :=
  Valpha α (fun p => L p.1 p.2) (vectorMeasure θ.1) (vectorMeasure θ.2)

/-- Real coordinates of the finite value, used only on K. Equation (16) states
finiteness there before this conversion is used in the differential theorem. -/
noncomputable def realV {m n : ℕ} (α : ℝ)
    (L : Fin (m + 1) → Fin (n + 1) → ℝ) (θ : Marginals m n) : ℝ :=
  (finiteV α L θ).toReal

/-- (15), pp. 18–19: the primal pair (π, Θ), with both arrays on X × Y. -/
abbrev PrimalPoint (m n : ℕ) :=
  ((Fin (m + 1) × Fin (n + 1)) → ℝ) × ((Fin (m + 1) × Fin (n + 1)) → ℝ)

/-- The actual feasible constraints of (15); the value remains defined by (11),
so identifying this LP value is proof work rather than a model assumption. -/
def primalPolyhedron {m n : ℕ} (α : ℝ) (θ : Marginals m n) : Set (PrimalPoint m n) :=
  {z | (∀ i, ∑ j, z.1 (i, j) = θ.1 i) ∧ (∀ j, ∑ i, z.1 (i, j) = θ.2 j) ∧
    (∀ i j, z.2 (i, j) ≤ (1 - α)⁻¹ * z.1 (i, j)) ∧
    (∑ i, ∑ j, z.2 (i, j)) = 1 ∧ (∀ i j, 0 ≤ z.1 (i, j) ∧ 0 ≤ z.2 (i, j))}

/-- The primal objective in (15). -/
def primalObjective {m n : ℕ} (L : Fin (m + 1) → Fin (n + 1) → ℝ)
    (z : PrimalPoint m n) : ℝ :=
  ∑ i, ∑ j, L i j * z.2 (i, j)

/-- (ϕ, ψ, ρ, β), with the product vector-space structure. -/
abbrev DualPoint (m n : ℕ) := (Fin (m + 1) → ℝ) ×
  ((Fin (n + 1) → ℝ) × (((Fin (m + 1) × Fin (n + 1)) → ℝ) × ℝ))

/-- The dual feasible polyhedron on p. 19, including ϕ₁ = 0 (here coordinate 0).
Its coefficients depend on α and L, not on the marginals. -/
def dualPolyhedron {m n : ℕ} (α : ℝ)
    (L : Fin (m + 1) → Fin (n + 1) → ℝ) : Set (DualPoint m n) :=
  {z | z.1 0 = 0 ∧ ∀ i j,
    0 ≤ (1 - α) * (z.1 i + z.2.1 j) - z.2.2.1 (i, j) ∧
    L i j ≤ z.2.2.1 (i, j) + z.2.2.2 ∧ 0 ≤ z.2.2.1 (i, j)}

/-- The actual extreme points of that polyhedron, not arbitrary dual solutions. -/
def vertices {m n : ℕ} (α : ℝ) (L : Fin (m + 1) → Fin (n + 1) → ℝ) :
    Set (DualPoint m n) :=
  (dualPolyhedron α L).extremePoints ℝ

/-- The objective of the dual on p. 19. -/
def dualObjective {m n : ℕ} (z : DualPoint m n) (θ : Marginals m n) : ℝ :=
  (∑ i, z.1 i * θ.1 i) + (∑ j, z.2.1 j * θ.2 j) + z.2.2.2

/-- I(µ,ν) in (18), indexed by extreme points rather than their enumeration. -/
def active {m n : ℕ} (α : ℝ) (L : Fin (m + 1) → Fin (n + 1) → ℝ)
    (θ : Marginals m n) : Set (DualPoint m n) :=
  {z | z ∈ vertices α L ∧ dualObjective z θ = realV α L θ}

/-- The linear slope of a dual objective; β is constant in the marginals. -/
def dualSlope {m n : ℕ} (z : DualPoint m n) (h : Marginals m n) : ℝ :=
  (∑ i, z.1 i * h.1 i) + (∑ j, z.2.1 j * h.2 j)

/-- (18): the minimum of active slopes. Theorem 3 explicitly asserts a finite,
nonempty active set and attainment, ruling out a default real sInf. -/
noncomputable def derivativeV {m n : ℕ} (α : ℝ)
    (L : Fin (m + 1) → Fin (n + 1) → ℝ) (θ h : Marginals m n) : ℝ :=
  sInf ((fun z => dualSlope z h) '' active α L θ)

/-- Theorem 3, p. 19: Hadamard directional differentiability tangentially to a
subset. All positive steps tending to zero and all converging directions with
feasible perturbed points are tested; no fixed direction or interior restriction.
The derivative is continuous, but need not be linear. -/
def HasHadamardWithin {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → ℝ) (S : Set E) (x : E) (d : E → ℝ) : Prop :=
  Continuous d ∧ ∀ (h : E) (t : ℕ → ℝ) (v : ℕ → E),
    (∀ k, 0 < t k) → Tendsto t atTop (𝓝 0) → Tendsto v atTop (𝓝 h) →
    (∀ k, x + t k • v k ∈ S) →
    Tendsto (fun k => (f (x + t k • v k) - f x) / t k) atTop (𝓝 (d h))

end MaxSpectralRisk.Duality.Supplement


