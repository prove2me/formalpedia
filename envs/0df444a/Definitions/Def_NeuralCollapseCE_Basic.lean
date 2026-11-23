-- Prove2me | Definitions.Def_NeuralCollapseCE_Basic
-- name    : NeuralCollapseCE_Basic
-- status  : Definition
-- author  : @Xeroth
-- created : 2026-11-23T17:09:11.679416+00:00
-- url     : https://prove2.me/theorems/f68a8c2c-f9ab-4737-ab61-2da505fbf683
-- title:
--   Cross-entropy and symmetric losses on the sphere, simplex ETFs, and the relaxed energy
-- statement:
--   Objects of Section 1 of Lu and Steinerberger, *Neural collapse with cross-entropy loss* (arXiv:2012.08465).
--
--   1. **Configurations.** Points $u_1,\dots,u_n\in\mathbb{R}^d$ with the Euclidean norm $\|\cdot\|$ and inner product $\langle\cdot,\cdot\rangle$. A configuration is admissible if $\|u_i\|=1$ for every $i$. The unit sphere of $\mathbb{R}^d$ is written $\mathbb{S}^d$, as in the paper.
--   2. **Symmetric loss (eq. 1).** For $\alpha\in\mathbb{R}$,
--   $$\mathcal{L}_\alpha(u)=\sum_{i=1}^n\log\Big(1+\sum_{j\ne i}e^{\alpha(\langle u_j,u_i\rangle-1)}\Big).$$
--   3. **Cross-entropy loss (eq. 2).**
--   $$\mathcal{L}(u,v)=\sum_{i=1}^n\log\frac{\sum_{j=1}^n e^{\langle v_j,u_i\rangle}}{e^{\langle v_i,u_i\rangle}}.$$
--   4. **Global minimisers.** $u$ is a global minimiser of $\mathcal{L}_\alpha$ if it is admissible and $\mathcal{L}_\alpha(u)\le\mathcal{L}_\alpha(w)$ for every admissible $w$. $(u,v)$ is a global minimiser of $\mathcal{L}$ if $u$ and $v$ are admissible and $\mathcal{L}(u,v)\le\mathcal{L}(u',v')$ for all admissible $u',v'$.
--   5. **Simplex equiangular tight frame.** Unit vectors $u_1,\dots,u_n$ with $\langle u_i,u_j\rangle=-\frac{1}{n-1}$ for all $i\ne j$.
--   6. **Uniform measure and empirical measures.** $\sigma_d$ is the surface measure of $\mathbb{S}^d$ normalised to total mass $1$. For points $u_1,\dots,u_n\in\mathbb{S}^d$, $\mu_n=\frac1n\sum_{i=1}^n\delta_{u_i}$.
--   7. **Relaxed energy (eq. 3).** For a measure $\mu$ on $\mathbb{S}^d$,
--   $$\mathcal{L}_\alpha(\mu)=\int_{\mathbb{S}^d}\log\Big(\int_{\mathbb{S}^d}e^{\alpha(\langle x,y\rangle-1)}\,\mu(dy)\Big)\,\mu(dx).$$
--
--   **Formalization Note** $\mathbb{R}^d$ is `EuclideanSpace ℝ (Fin d)` and $\mathbb{S}^d$ is its unit sphere `Metric.sphere 0 1`, so $\mathbb{S}^d$ here is the sphere of dimension $d-1$ (the paper's own notation). The uniform measure is Mathlib's `Measure.toSphere` of Lebesgue measure divided by its total mass. The simplex ETF is defined by unit norms and the pairwise inner products $-1/(n-1)$, which is the characterisation the paper's proofs use; the formula is meant for $n\ge2$, and every statement using it assumes $n\ge2$.
-- source:
--   Lu and Steinerberger, Neural collapse with cross-entropy loss, arXiv:2012.08465v2 (2021), Section 1.1 eqs. (1)-(2) p. 1, Section 1.2 Theorems 1-2 p. 2, Section 1.3 Theorem 3, eq. (3), Proposition 4 p. 3; simplex ETF characterisation in Sections 2-3, pp. 6, 8

import Mathlib

/-!
Lu and Steinerberger, *Neural collapse with cross-entropy loss*, arXiv:2012.08465v2 (2021):
the unit-sphere configurations, the symmetric loss `L_α` (eq. (1)), the cross-entropy loss `L`
(eq. (2)), their constrained global minimisers (Theorems 1 and 2), the simplex equiangular tight
frame, the uniform probability measure on the sphere, the empirical measure of a configuration
(Theorem 3) and the relaxed energy `L_α(μ)` on probability measures (eq. (3), Proposition 4),
all from Section 1.
-/

open MeasureTheory

noncomputable section

namespace NeuralCollapseCE

/-- Section 1.1, p. 1: the feature space `ℝ^d` with the Euclidean norm `‖·‖` and inner
product `⟨·,·⟩`. -/
abbrev Vec (d : ℕ) : Type := EuclideanSpace ℝ (Fin d)

/-- Section 1.3, Theorem 3, p. 3: the unit sphere `S^d = {x ∈ ℝ^d : ‖x‖ = 1}` (the paper writes
`S^d` for the unit sphere of `ℝ^d`, on which the points `u_i ∈ ℝ^d`, `‖u_i‖ = 1` lie). -/
abbrev Sph (d : ℕ) : Type := Metric.sphere (0 : Vec d) 1

/-- Section 1.1, eqs. (1)-(2), p. 1, and Theorems 1-3: the constraint `‖u_i‖ = 1` for
`i = 1, …, n`. -/
def IsUnitConfig {n d : ℕ} (u : Fin n → Vec d) : Prop :=
  ∀ i, ‖u i‖ = 1

/-- Eq. (1), p. 1: the symmetric loss
`L_α(u) = ∑_{i=1}^n log (1 + ∑_{j ≠ i} exp (α (⟨u_j, u_i⟩ - 1)))`. -/
def symLoss {n d : ℕ} (α : ℝ) (u : Fin n → Vec d) : ℝ :=
  ∑ i, Real.log (1 + ∑ j ∈ Finset.univ.erase i, Real.exp (α * (inner ℝ (u j) (u i) - 1)))

/-- Eq. (2), p. 1: the cross-entropy loss
`L(u, v) = ∑_{i=1}^n log ((∑_{j=1}^n exp ⟨v_j, u_i⟩) / exp ⟨v_i, u_i⟩)`. -/
def ceLoss {n d : ℕ} (u v : Fin n → Vec d) : ℝ :=
  ∑ i, Real.log ((∑ j, Real.exp (inner ℝ (v j) (u i))) / Real.exp (inner ℝ (v i) (u i)))

/-- Theorem 2, p. 2 (and Theorem 3, p. 3): `u` is a global minimiser of `L_α(u)` subject to
`u_i ∈ ℝ^d`, `‖u_i‖ = 1`, `i = 1, …, n`. -/
def IsSymMinimizer {n d : ℕ} (α : ℝ) (u : Fin n → Vec d) : Prop :=
  IsUnitConfig u ∧ ∀ w : Fin n → Vec d, IsUnitConfig w → symLoss α u ≤ symLoss α w

/-- Theorem 1, p. 2: `(u, v)` is a global minimiser of `L(u, v)` subject to `u_i, v_i ∈ ℝ^d`,
`‖u_i‖ = ‖v_i‖ = 1`, `i = 1, …, n`. -/
def IsCEMinimizer {n d : ℕ} (u v : Fin n → Vec d) : Prop :=
  IsUnitConfig u ∧ IsUnitConfig v ∧
    ∀ u' v' : Fin n → Vec d, IsUnitConfig u' → IsUnitConfig v' → ceLoss u v ≤ ceLoss u' v'

/-- Theorems 1 and 2, p. 2: `{u_i}_{i=1}^n` form a simplex equiangular tight frame, i.e. unit
vectors with `⟨u_i, u_j⟩ = -1/(n-1)` for `i ≠ j` (the characterisation used at the end of the
proofs of Theorem 2, p. 6, and Theorem 1, p. 8; meaningful for `n ≥ 2`). -/
def IsSimplexETF {n d : ℕ} (u : Fin n → Vec d) : Prop :=
  (∀ i, ‖u i‖ = 1) ∧ ∀ i j, i ≠ j → inner ℝ (u i) (u j) = -1 / ((n : ℝ) - 1)

/-- Theorem 3 and Proposition 4, p. 3: the uniform probability measure on `S^d`, i.e. the surface
measure (Mathlib's `Measure.toSphere` of Lebesgue measure) normalised to total mass one. -/
def uniformSphere (d : ℕ) : Measure (Sph d) :=
  ((volume : Measure (Vec d)).toSphere Set.univ)⁻¹ • (volume : Measure (Vec d)).toSphere

/-- Theorem 3, p. 3: the probability measure `μ_n = (1/n) ∑_{i=1}^n δ_{u_i}` generated by a
configuration of `n` points of `S^d`. -/
def empiricalMeasure {n d : ℕ} (u : Fin n → Sph d) : Measure (Sph d) :=
  ((n : ENNReal)⁻¹) • ∑ i, Measure.dirac (u i)

/-- Eq. (3), p. 3: the relaxed energy of a measure `μ` on `S^d`,
`L_α(μ) = ∫ log (∫ exp (α (⟨x, y⟩ - 1)) μ(dy)) μ(dx)`. -/
def measureEnergy {d : ℕ} (α : ℝ) (μ : Measure (Sph d)) : ℝ :=
  ∫ x, Real.log (∫ y, Real.exp (α * (inner ℝ (x : Vec d) (y : Vec d) - 1)) ∂μ) ∂μ

end NeuralCollapseCE


