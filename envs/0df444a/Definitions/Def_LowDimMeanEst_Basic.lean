-- Prove2me | Definitions.Def_LowDimMeanEst_Basic
-- name    : LowDimMeanEst_Basic
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T04:40:00.867769+00:00
-- url     : https://prove2.me/theorems/7759826f-e7e5-4a06-835d-8d97aa543419
-- title:
--   Notation: $\mathbb R^d$, $\log\frac1\delta$, mean, directional variance, $\Sigma\preceq sI$, $x^\top Ax$, $\min(1,x^\top Ax)$, $\mathrm{Tr}(A)$
-- statement:
--   Points live in $\mathbb R^d$ with the Euclidean norm $\|\cdot\|_2$ and dot product $x\cdot z$. All logarithms are natural; write
--
--   $$L=\log\frac1\delta,\qquad LL=\log\log\frac1\delta .$$
--
--   For a probability distribution $D$ on $\mathbb R^d$, the **mean** is $\mu=\mathbb E_{X\sim D}[X]$, the **variance in direction** $z$ is $\mathbb E\langle X-\mu,z\rangle^2$ and the **second moment in direction** $z$ is $\mathbb E\langle X,z\rangle^2=z^\top\mathbb E[XX^\top]z$. The covariance bound $\Sigma\preceq sI$ means that $D$ has a finite second moment and $\mathbb E\langle X-\mu,z\rangle^2\le s$ for every unit vector $z$; the second-moment bound $\mathbb E[XX^\top]\preceq sI$ means the same with the uncentred moment.
--
--   A $d\times d$ matrix $A$ acts on $\mathbb R^d$; $A\succeq0$ means symmetric positive semidefinite, $\mathrm{Tr}(A)$ is its trace and $\|A\|_{op}$ its operator norm. The **trimming weight** of a sample $x$ under $A$ is
--
--   $$\min(1,\;x^\top Ax).$$
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note** $\mathbb R^d$ is `EuclideanSpace ℝ (Fin d)`, matrices are continuous linear maps of it, and $A\succeq0$ is Mathlib's `IsPositive`. The bounds $\Sigma\preceq sI$ and $\mathbb E[XX^\top]\preceq sI$ include `MemLp id 2 D`: without it Lean's integral of a non-integrable function is $0$ and the bounds would hold vacuously.
-- source:
--   Lee, Mathashery, Valiant, Wang, Optimal Sub-Gaussian Mean Estimation in Low Dimensions, STOC 2027 submission (manuscript sha256 7316d30e…), notation of §1.1 (p.2), Algorithm 2 and Lemma 3 (p.9), §§6–9 (pp.12–47)

import Mathlib

open MeasureTheory

namespace LowDimMeanEst

/-!
# Notation shared by every statement of the mission

Lee, Mathashery, Valiant, Wang, *Optimal Sub-Gaussian Mean Estimation in Low Dimensions*, STOC 2027
submission (manuscript sha256 7316d30e…): the notation of §1.1 (p.2), Algorithm 2 (p.9), Lemma 3
(p.9) and the statements of §§6–9.

**Formalization Note.**
* Points live in `E d = EuclideanSpace ℝ (Fin d)`, so `‖·‖` is the Euclidean norm `‖·‖₂` and
  `inner ℝ x z` is the dot product `x · z`.
* `log` is the natural logarithm (the constant `√2` and the Chernoff computations of the paper force
  it). `logInv δ = log (1/δ)` and `loglogInv δ = log log (1/δ)`; the statements always restrict `δ`
  so that these are positive where they are divided by.
* A `d × d` matrix is a continuous linear map `E d →L[ℝ] E d`; `x⊤ A x` is `quad A x`, `Tr(A)` is
  `tr A`, `∥·∥op` is the operator norm, and "symmetric positive semidefinite" is Mathlib's
  `ContinuousLinearMap.IsPositive` (symmetric with `⟨A x, x⟩ ≥ 0`).
* A distribution `D` on `ℝ^d` is a measure on `E d` (a probability measure, supplied as an instance
  where it is used). "Covariance `Σ ⪯ s I`" is `CovLe D s`: finite second moment (`MemLp id 2 D`) and
  `E⟨X − µ, z⟩² ≤ s` for every unit vector `z`. "Second moment `E[XX⊤] ⪯ s I`" is `SecondMomentLe D s`,
  with no centring. `MemLp id 2 D` is required because Lean's Bochner integral of a non-integrable
  function is `0`, which would make the variance bounds vacuous.
-/

/-- The ambient space `ℝ^d` with the Euclidean norm. -/
abbrev E (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- `log (1/δ)` (natural logarithm). -/
noncomputable def logInv (δ : ℝ) : ℝ := Real.log (1 / δ)

/-- `log log (1/δ)` (natural logarithms). -/
noncomputable def loglogInv (δ : ℝ) : ℝ := Real.log (Real.log (1 / δ))

/-- The mean `µ = E_{X∼D}[X]` (Bochner integral). -/
noncomputable def popMean {d : ℕ} (D : Measure (E d)) : E d := ∫ x, x ∂D

/-- The variance of `D` in direction `z`: `E[⟨X − µ, z⟩²]`. -/
noncomputable def dirVar {d : ℕ} (D : Measure (E d)) (z : E d) : ℝ :=
  ∫ x, (inner ℝ (x - popMean D) z) ^ 2 ∂D

/-- The uncentred second moment of `D` in direction `z`: `E[⟨X, z⟩²] = z⊤ E[XX⊤] z`. -/
noncomputable def secondMoment {d : ℕ} (D : Measure (E d)) (z : E d) : ℝ :=
  ∫ x, (inner ℝ x z) ^ 2 ∂D

/-- `Σ ⪯ s I`: `D` has finite second moment and variance at most `s` in every unit direction. -/
def CovLe {d : ℕ} (D : Measure (E d)) (s : ℝ) : Prop :=
  MemLp id 2 D ∧ ∀ z : E d, ‖z‖ = 1 → dirVar D z ≤ s

/-- `E[XX⊤] ⪯ s I`: `D` has finite second moment and `E[⟨X, z⟩²] ≤ s` in every unit direction. -/
def SecondMomentLe {d : ℕ} (D : Measure (E d)) (s : ℝ) : Prop :=
  MemLp id 2 D ∧ ∀ z : E d, ‖z‖ = 1 → secondMoment D z ≤ s

/-- The quadratic form `x⊤ A x`. -/
noncomputable def quad {d : ℕ} (A : E d →L[ℝ] E d) (x : E d) : ℝ := inner ℝ x (A x)

/-- The trimming weight `min(1, x⊤ A x)` of a sample `x` under the trimming matrix `A` (Lemma 3). -/
noncomputable def trim {d : ℕ} (A : E d →L[ℝ] E d) (x : E d) : ℝ := min 1 (quad A x)

/-- The trace `Tr(A)`. -/
noncomputable def tr {d : ℕ} (A : E d →L[ℝ] E d) : ℝ :=
  LinearMap.trace ℝ (E d) (A : E d →ₗ[ℝ] E d)

end LowDimMeanEst


