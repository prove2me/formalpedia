-- Prove2me | Definitions.Def_KellyStochasticNetworks_LossLimits_Gaussian
-- name    : KellyStochasticNetworks_LossLimits_Gaussian
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-22T03:46:19.719846+00:00
-- url     : https://prove2.me/theorems/c0b71196-ca27-4f1e-8e1f-3d628b162468
-- title:
--   Canonical Gaussian law on the active-link kernel
-- statement:
--   Let $A\in\mathbb N^{J\times R}$, let $B\in\mathbb R^J$, and let $x\in\mathbb R^R$. Set $\mathcal B=\{j:B_j>0\}$, let $H=A_{\mathcal B}$ contain precisely these rows, and write $D=\operatorname{diag}(x)$. Start with independent coordinates $Z_r\sim\mathcal N(0,x_r)$ and define the law of
--   $$U=Z-DH^{\mathsf T}(HDH^{\mathsf T})^{-1}HZ.$$
--   For positive $x$ and linearly independent rows of $H$, this is the canonical Gaussian conditioned on $HU=0$, with covariance
--   $$\Sigma=D-DH^{\mathsf T}(HDH^{\mathsf T})^{-1}HD.$$
--
--   This construction specifies the limit law uniquely from the network data, including singular limits. It does not condition by dividing by the probability of a null event.
--
--   **Formalization Note** The definition is total: the input variances are clipped below at zero and the matrix inverse is Lean's nonsingular inverse, which is zero at singular matrices. Under the mission hypotheses $x$ is positive and the active Gram matrix is invertible. When no link is active the residual map is the identity and the coordinates stay independent.
-- source:
--   Kelly & Yudovina, Stochastic Networks (2014), supplied Lecture Notes PDF, printed p. 63 (PDF p. 71), active-link definitions and Theorem 3.14 (printed pp. 63–64 / PDF pp. 71–72); DOI 10.1017/cbo9781139565363.

import Mathlib

open MeasureTheory ProbabilityTheory

namespace KellyStochasticNetworks.LossLimits

/-- Active rows are exactly those for which `B j > 0`. -/
def Active {J : ℕ} (B : Fin J → ℝ) := {j : Fin J // 0 < B j}

noncomputable instance {J : ℕ} (B : Fin J → ℝ) : Fintype (Active B) := by
  classical
  unfold Active
  infer_instance

/-- The weighted active-row Gram matrix `A_B diag(x) A_Bᵀ`. -/
noncomputable def activeGram {J R : ℕ} (A : Fin J → Fin R → ℕ)
    (B : Fin J → ℝ) (x : Fin R → ℝ) : Matrix (Active B) (Active B) ℝ :=
  fun j k => ∑ r, (A j.val r : ℝ) * x r * (A k.val r : ℝ)

/-- Gaussian regression residual `z - D A_Bᵀ (A_B D A_Bᵀ)⁻¹ A_B z`.
This is weighted projection, not Euclidean projection of the unwhitened vector. -/
noncomputable def gaussianResidual {J R : ℕ} (A : Fin J → Fin R → ℕ)
    (B : Fin J → ℝ) (x : Fin R → ℝ) (z : Fin R → ℝ) : Fin R → ℝ := by
  classical
  exact fun r => z r - x r * ∑ j : Active B, (A j.val r : ℝ) *
    (∑ k : Active B, (activeGram A B x)⁻¹ j k * ∑ s, (A k.val s : ℝ) * z s)

/-- Canonical Gaussian conditioned on `A_B u = 0`, defined even when the event is null.
For positive `x` and independent active rows its covariance is
`D - D A_Bᵀ (A_B D A_Bᵀ)⁻¹ A_B D`. Empty active sets give the independent law. -/
noncomputable def conditionedGaussian {J R : ℕ} (A : Fin J → Fin R → ℕ)
    (B : Fin J → ℝ) (x : Fin R → ℝ) : Measure (Fin R → ℝ) :=
  (Measure.pi (fun r => gaussianReal 0 (Real.toNNReal (x r)))).map
    (gaussianResidual A B x)

end KellyStochasticNetworks.LossLimits


