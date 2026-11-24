-- Prove2me | Definitions.Def_RegMT_Classif_Supplement_Kernels
-- name    : RegMT_Classif_Supplement_Kernels
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T05:27:44.704316+00:00
-- url     : https://prove2.me/theorems/4e18b989-db73-4d6c-8793-42fb059d6d91
-- title:
--   Gram objectives and kernel hypotheses
-- statement:
--   For training inputs define $K_{ij}=k(\hat x_i,\hat x_j)$ and
--   $$q(\beta)=\sum_{i,j}\beta_iK_{ij}\beta_j,\qquad h_\beta=\sum_i\beta_i\Phi(\hat x_i).$$
--   The regression objective is $N^{-1}\sum_i L((K\beta)_i-\hat y_i)+\rho\operatorname{lip}(L)\sqrt{q(\beta)+1}$. The classification program imposes $L(\hat y_i(K\beta)_i)\le s_i$, $L(-\hat y_i(K\beta)_i)-\kappa\lambda\le s_i$, and $\operatorname{lip}(L)\sqrt{q(\beta)}\le\lambda$, and minimizes $\lambda\rho+N^{-1}\sum_i s_i$. These are the full programs in Theorems 3.26 and 3.27, p.16.
--   The quadratic form equals $\|K^{1/2}\beta\|_2^2$ because the Gram matrix is positive semidefinite. No inverse, chosen square root, or strict positivity is required, and repeated sample points are allowed.
-- source:
--   Shafieezadeh-Abadeh, Kuhn & Mohajerin Esfahani, Regularization via Mass Transportation, arXiv:1710.10016v3, p.16, Gram-matrix definition and Theorems 3.26–3.27, (32)

import Mathlib
import Definitions.Def_RegMT_Classif_Supplement_RKHS
import Definitions.Def_RegMT_Classif_Model

open scoped ENNReal

noncomputable section

namespace RegMT.Classif.Supplement
open DRLogReg.Reformulation WassersteinDRO.Duality

variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]

def gram {X : Set V} {N : ℕ} (R : RKHSData X H) (x : Fin N → X) : Matrix (Fin N) (Fin N) ℝ :=
  fun i j => R.kernel (x i) (x j)

def kernelQuadratic {N : ℕ} (K : Matrix (Fin N) (Fin N) ℝ) (β : Fin N → ℝ) : ℝ :=
  ∑ i, ∑ j, β i * K i j * β j

def kernelHyp {X : Set V} {N : ℕ} (R : RKHSData X H) (x : Fin N → X) (β : Fin N → ℝ) : H :=
  ∑ i, β i • R.feature (x i)

def kernelRegObjective {N : ℕ} (K : Matrix (Fin N) (Fin N) ℝ)
    (y : Fin N → ℝ) (L : ℝ → ℝ) (ρ : ℝ) (β : Fin N → ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal ((N : ℝ)⁻¹ * ∑ i, L ((∑ j, K i j * β j) - y i)) +
    ENNReal.ofReal ρ * lipschitzModulus L * ENNReal.ofReal (Real.sqrt (kernelQuadratic K β + 1))

def kernelClassFeasible {N : ℕ} (K : Matrix (Fin N) (Fin N) ℝ)
    (y : Fin N → Bool) (L : ℝ → ℝ) (κ : ℝ)
    (q : (Fin N → ℝ) × (ℝ × (Fin N → ℝ))) : Prop :=
  (∀ i, L (sgn (y i) * ∑ j, K i j * q.1 j) ≤ q.2.2 i) ∧
  (∀ i, L (-(sgn (y i) * ∑ j, K i j * q.1 j)) - κ * q.2.1 ≤ q.2.2 i) ∧
  (lipschitzModulus L).toReal * Real.sqrt (kernelQuadratic K q.1) ≤ q.2.1

def kernelClassObjective {N : ℕ} (ρ : ℝ)
    (q : (Fin N → ℝ) × (ℝ × (Fin N → ℝ))) : ℝ≥0∞ :=
  ENNReal.ofReal (q.2.1 * ρ + (N : ℝ)⁻¹ * ∑ i, q.2.2 i)

def kernelClassValue {N : ℕ} (K : Matrix (Fin N) (Fin N) ℝ)
    (y : Fin N → Bool) (L : ℝ → ℝ) (κ ρ : ℝ) : ℝ≥0∞ :=
  ⨅ q, ⨅ (_ : kernelClassFeasible K y L κ q), kernelClassObjective ρ q

end RegMT.Classif.Supplement


