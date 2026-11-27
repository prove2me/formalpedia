-- Prove2me | Definitions.Def_MPBSelect_Supplement_KRR
-- name    : MPBSelect_Supplement_KRR
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T02:46:07.954253+00:00
-- url     : https://prove2.me/theorems/ad467d1b-b7e6-4ced-84af-6ed6ef52ed64
-- title:
--   Kernel-ridge estimator, predictive means and cumulant generating function
-- statement:
--   A positive-definite kernel is represented by feature vectors in a real Hilbert space, so $K(\theta_b,\theta_{b'})$ is their inner product. For one solution, this bundle defines the penalized Gaussian negative-log-likelihood objective (31), its minimizers, the kernel matrix $K_i$, the diagonal sampling-variance matrix $\Sigma_{i,n}$, the predictive-mean vector, and the closed form
--
--   $$
--   \beta_i\mathbf 1_B+K_i^\top(K_i+2\kappa\Sigma_{i,n})^{-1}(\mu_{i,n}-\beta_i\mathbf 1_B),
--   $$
--
--   which corrects the printed $\kappa\Sigma_{i,n}$ of (32) (the factor $2$ comes from the weight $N/(2\lambda^2)$ of (31)). It also defines the normal laws of the posterior-mean vectors (5) under a normal prior and an extended-real cumulant generating function using a nonnegative integral, so divergent exponential moments cannot default to zero.
-- source:
--   Kim, Kim, Song, Selection of the Most Probable Best, arXiv:2207.07533v2, Section 6, problem (31), pp.27-28

import Mathlib
import Definitions.Def_MPBSelect_Problem
import Definitions.Def_MPBSelect_Supplement_ExactRates

noncomputable section

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal RealInnerProductSpace Topology

namespace MPBSelect.Supplement

/-- Public bundle type for finite kernel feature maps used in Section 6. -/
abbrev KRR (B : ℕ) (H : Type*) := Fin B → H

/-- The finite kernel matrix `K_i`; its `(b,b')` entry is the inner product of the two RKHS
feature vectors, hence `K(θ_b,θ_b')`. -/
def kernelMatrix {B : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (feature : Fin B → H) : Matrix (Fin B) (Fin B) ℝ :=
  fun b b' => inner ℝ (feature b) (feature b')

/-- The diagonal sampling-variance matrix `Σ_{i,n}`. -/
def samplingVariance {k B : ℕ} (P : MPBSelect.Problem k B) (i : Fin k)
    (N : Fin B → ℕ) : Matrix (Fin B) (Fin B) ℝ :=
  Matrix.diagonal fun b => P.lam i b ^ 2 / (N b : ℝ)

/-- The GNLLL plus RKHS penalty in (31), written through a feature realization of the
positive-definite kernel. `β + ⟪feature b,g⟫` is the predicted conditional mean at `θ_b`. -/
def krrObjective {k B : ℕ} (P : MPBSelect.Problem k B) (i : Fin k)
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (feature : Fin B → H) (N : Fin B → ℕ) (μvec : Fin B → ℝ)
    (β κ : ℝ) (g : H) : ℝ :=
  ∑ b, (N b : ℝ) / (2 * P.lam i b ^ 2) *
      (μvec b - inner ℝ (feature b) g - β) ^ 2 + κ * ‖g‖ ^ 2

/-- `g` solves the penalized GNLLL problem (31). -/
def IsKRRMinimizer {k B : ℕ} (P : MPBSelect.Problem k B) (i : Fin k)
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (feature : Fin B → H) (N : Fin B → ℕ) (μvec : Fin B → ℝ)
    (β κ : ℝ) (g : H) : Prop :=
  ∀ h : H, krrObjective P i feature N μvec β κ g ≤
    krrObjective P i feature N μvec β κ h

/-- The vector of predictive means `β_i + g(θ_b)`. -/
def predictiveMean {B : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (feature : Fin B → H) (β : ℝ) (g : H) : Fin B → ℝ :=
  fun b => β + inner ℝ (feature b) g

/-- The closed form of the predictive means of (31): `β 1_B + Kᵀ (K + 2κ Σ)⁻¹ (μ - β 1_B)`.

**Formalization Note (correction of (32), p.28).** The page prints `(K_i + κ Σ_{i,n})⁻¹`. For the
objective (31), whose data term carries the factor `N/(2λ²) = 1/(2 Σ_bb)`, the first-order
condition gives `(K_i + 2κ Σ_{i,n})⁻¹`; the e-companion proof (EC.45), p.ec30, drops the `1/2` of
(31). Counterexample to the printed form: `B = 1`, `K = 1`, `λ = N = κ = μ = 1`, `β = 0`; (31) is
`(1 - g)²/2 + g²`, minimized at `g = 1/3`, while the printed (32) gives `1/2`. The transpose and the
intercept are kept as printed (`Kᵀ = K`). -/
def krrClosedForm {k B : ℕ} (P : MPBSelect.Problem k B) (i : Fin k)
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (feature : Fin B → H) (N : Fin B → ℕ) (μvec : Fin B → ℝ)
    (β κ : ℝ) : Fin B → ℝ :=
  let K := kernelMatrix feature
  let S := samplingVariance P i N
  fun b => β + ((K.transpose * (K + (2 * κ) • S)⁻¹).mulVec (fun c => μvec c - β)) b

/-- Independent posterior-mean vectors `μ_{i,n} = {μ_{i,n}(θ_b)}_b` of (5), p.9, for one solution `i`
under the normal prior `pr` (zero precision: the noninformative prior) and Gaussian outputs with
true mean `y_i(θ_b)` and variance `λ²_i(θ_b)` (Model (4)): `μ_{i,n}(θ_b)` is normal with mean
`(τ μ₀ + N y/λ²)/(τ + N/λ²)` and variance `(N/λ²)/(τ + N/λ²)²`, where `τ = 1/σ²_{i,0}(θ_b)`; for
`τ = 0` these are `y_i(θ_b)` and `λ²_i(θ_b)/N`. Dependence across different horizons is left
unrestricted, as Theorem 9 uses only each horizon's marginal vector. -/
def IsGaussianMeanArray {k B : ℕ} (P : MPBSelect.Problem k B) (i : Fin k)
    (pr : GaussianPrior k B)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (N : ℕ → Fin B → ℕ) (X : ℕ → Fin B → Ω → ℝ) : Prop :=
  (∀ n, iIndepFun (X n) μ) ∧
  ∀ n b, Measurable (X n b) ∧
    Measure.map (X n b) μ = gaussianReal
      ((pr.prec i b * pr.mean i b + (N n b : ℝ) * P.y i b / P.lam i b ^ 2) /
        (pr.prec i b + (N n b : ℝ) / P.lam i b ^ 2))
      ⟨((N n b : ℝ) / P.lam i b ^ 2) / (pr.prec i b + (N n b : ℝ) / P.lam i b ^ 2) ^ 2,
        div_nonneg (div_nonneg (Nat.cast_nonneg _) (sq_nonneg _)) (sq_nonneg _)⟩

/-- Cumulant generating function computed with a nonnegative integral, so a divergent moment
has extended-real value `+∞` rather than the Bochner integral's default zero. -/
def kernelCGF {B : ℕ} {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : Ω → Fin B → ℝ) (t : Fin B → ℝ) : EReal :=
  ENNReal.log (∫⁻ ω, ENNReal.ofReal (Real.exp (∑ b, t b * X ω b)) ∂μ)

/-- The scaled CGF `n⁻¹ Λ̂_{i,n}(n t)` in (33). -/
def scaledKernelCGF {B : ℕ} {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : ℕ → Ω → Fin B → ℝ) (n : ℕ) (t : Fin B → ℝ) : EReal :=
  (n : EReal)⁻¹ * kernelCGF μ (X n) (fun b => (n : ℝ) * t b)

/-- One summand of the extended-real reading of (33). At a zero limiting allocation, the
quadratic term is `+∞` for `t_b ≠ 0` and its continuous value is zero for `t_b = 0`. -/
def cgfLimitTerm (y lam α t : ℝ) : EReal :=
  if α = 0 then
    if t = 0 then (0 : EReal) else ⊤
  else ((y * t + lam ^ 2 * t ^ 2 / (2 * α) : ℝ) : EReal)

end MPBSelect.Supplement


