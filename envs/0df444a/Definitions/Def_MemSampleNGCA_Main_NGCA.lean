-- Prove2me | Definitions.Def_MemSampleNGCA_Main_NGCA
-- name    : MemSampleNGCA_Main_NGCA
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T19:38:55.625052+00:00
-- url     : https://prove2.me/theorems/a60414ca-546b-4c5b-b0c3-4d723d7d9483
-- title:
--   Hidden-direction distributions P_{A,θ}, the Ornstein–Uhlenbeck operator, Assumptions A1–A2, the uniform measure on the sphere (Definitions 1.1, A.6; Problem 1.2)
-- statement:
--   Let $\gamma=N(0,1)$ on $\mathbb R$ and $\gamma_d=N(0,I_d)$ on $\mathbb R^d$. For a probability measure $A$ on $\mathbb R$ write $g_A=dA/d\gamma$.
--
--   - **Ornstein–Uhlenbeck operator** (Definition A.6): $(U_\rho f)(z)=\mathbb E_{G\sim\gamma}\big[f(\rho z+\sqrt{1-\rho^2}\,G)\big]$.
--   - **Assumption A1** with parameter $M>0$: $A\ll\gamma$ and $dA/d\gamma\in[0,M]$.
--   - **Assumption A2** (Gaussian smoothing) with parameters $C>0$, $m\in\mathbb N$: for every $\rho\in[0,1/\sqrt2]$,
--   $$\|U_\rho g_A\|_{L^\infty(\gamma)}\le 1+C^m\rho^{2m}.$$
--   - **Hidden-direction distribution** (Definition 1.1): for $\theta\in\mathbb R^d$, $P_{A,\theta}$ is the law on $\mathbb R^d$ whose projection on a unit vector $\theta$ is $A$ and whose projection on $\theta^\perp$ is an independent standard $(d-1)$-dimensional Gaussian, i.e. $\frac{dP_{A,\theta}}{d\gamma_d}(x)=g_A(\langle\theta,x\rangle)$.
--   - **NGCA alternatives** (Problem 1.2): $\{P_{A,\theta}:\theta\in S^{d-1}\}$, tested against the null $N(0,I_d)$.
--   - **Uniform measure** $\pi$ on $S^{d-1}$, and the NGCA density family $(\theta,x)\mapsto g_A(\langle\theta,x\rangle)$ on $S^{d-1}\times\mathbb R^d$ used in §C.1.
--
--   These are the objects of the paper's main theorem.
--
--   **Formalization Note.** $\mathbb R^d$ is `EuclideanSpace ℝ (Fin d)`, $\gamma$ is `gaussianReal 0 1`, $\gamma_d$ is Mathlib's `stdGaussian`. $g_A$ is the real value of `A.rnDeriv γ` (a version of the Radon–Nikodym derivative); A1 bounds it $\gamma$-a.e. $P_{A,\theta}$ is `γ_d.withDensity (x ↦ dA/dγ(⟨θ, x⟩))`, the same measure as the product description of Definition 1.1. The $L^\infty(\gamma)$ norm is `eLpNorm · ∞ γ` (essential supremum of the absolute value). $U_\rho$ is a Bochner integral; whenever A1 holds and $|\rho|<1$ the integrand is bounded and integrable, so the value is the paper's. $\pi$ is the surface measure `volume.toSphere` divided by its total mass.
-- source:
--   Pensia, Gupta, Verchand, Sharan, Vedantam, Memory-Sample Tradeoffs in High-Dimensional Statistics, STOC 2027 submission (manuscript sha256 ac94994a…), p. 2 (PDF 4) Definition 1.1; p. 3 (PDF 5) Problem 1.2; p. 4 (PDF 6) Assumptions A1–A2; p. 15 (PDF 17) Definition A.6; p. 24 (PDF 26) Assumption C.1

import Mathlib

open MeasureTheory ProbabilityTheory
open scoped ENNReal RealInnerProductSpace

namespace MemSampleNGCA.Main

/-! # The NGCA model: hidden-direction distributions, the OU operator, Assumptions A1–A2

Pensia, Gupta, Verchand, Sharan, Vedantam, *Memory-Sample Tradeoffs in High-Dimensional
Statistics*, STOC 2027 submission (manuscript sha256 ac94994a…): Definition 1.1 (p. 2, PDF 4),
Problem 1.2 (p. 3, PDF 5), Assumptions A1–A2 (p. 4, PDF 6), Definition A.6 (p. 15, PDF 17),
Assumption C.1 (p. 24, PDF 26), and the uniform measure `π` on `S^{d−1}` (§B, p. 16; §C.1).

`ℝ^d` is `EuclideanSpace ℝ (Fin d)`; `γ = N(0,1)` is `gaussianReal 0 1` and `γ_d = N(0, I_d)` is
Mathlib's `stdGaussian`. -/

/-- `ℝ^d` with its Euclidean structure. -/
abbrev Rd (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- The standard Gaussian `γ = N(0, 1)` on `ℝ`. -/
noncomputable def gamma1 : Measure ℝ := gaussianReal 0 1

/-- The standard Gaussian `γ_d = N(0, I_d)` on `ℝ^d`. -/
noncomputable def gammaD (d : ℕ) : Measure (Rd d) := stdGaussian (Rd d)

/-- The likelihood ratio `g_A = dA/dγ` (a version of the Radon–Nikodym derivative), real valued. -/
noncomputable def gA (A : Measure ℝ) : ℝ → ℝ := fun z => (A.rnDeriv gamma1 z).toReal

/-- The Ornstein–Uhlenbeck operator (Definition A.6; display before Assumption A2):
`(U_ρ f)(z) = E_{G∼γ}[f(ρ z + √(1 − ρ²) G)]`. -/
noncomputable def ouOp (ρ : ℝ) (f : ℝ → ℝ) (z : ℝ) : ℝ :=
  ∫ g, f (ρ * z + Real.sqrt (1 - ρ ^ 2) * g) ∂gamma1

/-- Assumption A1 (bounded likelihood ratio) with parameter `M > 0`: `A ≪ γ` and
`dA/dγ ∈ [0, M]` (`γ`-a.e.; the Radon–Nikodym derivative is nonnegative by construction). -/
def AssumptionA1 (M : ℝ) (A : Measure ℝ) : Prop :=
  0 < M ∧ A ≪ gamma1 ∧ ∀ᵐ z ∂gamma1, A.rnDeriv gamma1 z ≤ ENNReal.ofReal M

/-- Assumption A2 (Gaussian smoothing) with parameters `C > 0`, `m ∈ ℕ`: for every
`ρ ∈ [0, 1/√2]`, `‖U_ρ g_A‖_{L∞(γ)} ≤ 1 + C^m ρ^{2m}` (the `L∞(γ)` norm is `eLpNorm · ∞ γ`,
the `γ`-essential supremum of the absolute value). -/
def AssumptionA2 (C : ℝ) (m : ℕ) (A : Measure ℝ) : Prop :=
  0 < C ∧ ∀ ρ : ℝ, 0 ≤ ρ → ρ ≤ 1 / Real.sqrt 2 →
    eLpNorm (ouOp ρ (gA A)) ∞ gamma1 ≤ ENNReal.ofReal (1 + C ^ m * ρ ^ (2 * m))

/-- The hidden-direction distribution `P_{A,θ}` on `ℝ^d` (Definition 1.1): the law whose
projection on `θ` is `A` and whose projection on `θ^⊥` is an independent standard Gaussian.
Written through its density against `γ_d`: `dP_{A,θ}/dγ_d (x) = g_A(⟨θ, x⟩)`. -/
noncomputable def hiddenDir {d : ℕ} (A : Measure ℝ) (θ : Rd d) : Measure (Rd d) :=
  (gammaD d).withDensity (fun x => A.rnDeriv gamma1 ⟪θ, x⟫)

/-- The alternative of the NGCA testing problem (Problem 1.2): `{P_{A,θ} : θ ∈ S^{d−1}}`. -/
def ngcaAlternatives (d : ℕ) (A : Measure ℝ) : Set (Measure (Rd d)) :=
  (fun θ => hiddenDir A θ) '' Metric.sphere (0 : Rd d) 1

/-- The uniform probability measure `π` on the unit sphere `S^{d−1}`: Mathlib's surface measure
`volume.toSphere`, normalized to total mass one. -/
noncomputable def sphereUnif (d : ℕ) : Measure (Metric.sphere (0 : Rd d) 1) :=
  ((volume : Measure (Rd d)).toSphere Set.univ)⁻¹ • (volume : Measure (Rd d)).toSphere

/-- The NGCA likelihood ratio `dP_{A,θ}/dγ_d (x) = g_A(⟨θ, x⟩)` as a function of
`(θ, x) ∈ S^{d−1} × ℝ^d` (the density family used in §C.1). -/
noncomputable def ngcaDensity (d : ℕ) (A : Measure ℝ) :
    Metric.sphere (0 : Rd d) 1 → Rd d → ℝ :=
  fun θ x => gA A ⟪(θ : Rd d), x⟫

end MemSampleNGCA.Main


