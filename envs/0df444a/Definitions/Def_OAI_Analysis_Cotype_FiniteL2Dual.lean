-- Prove2me | Definitions.Def_OAI_Analysis_Cotype_FiniteL2Dual
-- name    : OAI_Analysis_Cotype_FiniteL2Dual
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T17:27:51.498088+00:00
-- url     : https://prove2.me/theorems/dfa7dcd6-637f-4a70-bb75-7783ebdda488
-- title:
--   Dual functionals on finite l2-sums
-- statement:
--   These notions belong to a proof that a real Banach space $X$ with the approximation property is K-convex (the Rademacher projection is bounded on $L_2(\{\pm1\}^n;X)$ uniformly in $n$) if and only if $X$ and its dual $X^*$ both have finite cotype. The converse direction shows that such $X$ has nontrivial type, i.e. does not contain $\ell_1^n$ uniformly, and then derives K-convexity from a power-gap estimate for commuting coordinate projections. Let $\Omega$ be finite.
--
--   1. **Finite $\ell_2$ dual.** A tuple $g_a\in X^*$ defines $z\mapsto\sum_ag_a(z_a)$ on $\ell_2(\Omega;X)$, with norm at most $\bigl(\sum_a\|g_a\|^2\bigr)^{1/2}$.
--   2. **Probability normalization.** On the cube, $f$ is identified with $2^{-n/2}f\in\ell_2(\{0,1\}^n;X)$, so that
--   $$
--   \|2^{-n/2}f\|_{\ell_2}=\|f\|_{L_2}
--   $$
--   for the probability normalization, and dual tuples are scaled the same way.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Cotype/FiniteL2Dual.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Cotype/FiniteL2Dual.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the Cotype mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_Cotype
import Definitions.Def_OAI_Analysis_Cotype_ComplexDualLift
import Definitions.Def_OAI_Analysis_Cotype_Cube
import Definitions.Def_OAI_Analysis_Cotype_Target
import Definitions.Def_OAI_Analysis_Cotype_Moments
import Definitions.Def_OAI_Analysis_Cotype_Fourier
import Definitions.Def_OAI_Analysis_Cotype_ScalarWalsh
import Definitions.Def_OAI_Analysis_Cotype_VectorWalsh
import Definitions.Def_OAI_Analysis_Cotype_WalshNorm
import Definitions.Def_OAI_Analysis_Cotype_WalshCoordinates
import Definitions.Def_OAI_Analysis_Cotype_WalshDuality
import Definitions.Def_OAI_Analysis_Cotype_CubeNoise
import Definitions.Def_OAI_Analysis_Cotype_ProjectionProducts
import Definitions.Def_OAI_Analysis_Cotype_UniformL1
import Definitions.Def_OAI_Analysis_Cotype_BConvexity
import Definitions.Def_OAI_Analysis_Cotype_ProjectionAverages
import Definitions.Def_OAI_Analysis_Cotype_ProjectionSemigroup
import Definitions.Def_OAI_Analysis_Cotype_ProjectionSemigroupBasics
import Definitions.Def_OAI_Analysis_Cotype_ProjectionSpectrum
import Definitions.Def_OAI_Analysis_Cotype_ComplexProjectionPolynomial
import Definitions.Def_OAI_Analysis_Cotype_ComplexProjectionSpectrum
import Definitions.Def_OAI_Analysis_Cotype_ProjectionGenerator
import Definitions.Def_OAI_Analysis_Cotype_PowerGapInverse
import Definitions.Def_OAI_Analysis_Cotype_ExponentialIntegral
import Definitions.Def_OAI_Analysis_Cotype_ProjectionResolvent
import Definitions.Def_OAI_Analysis_Cotype_SectorResolvent
import Definitions.Def_OAI_Analysis_Cotype_FiniteContour
import Definitions.Def_OAI_Analysis_Cotype_NoiseHypercontractivity
import Definitions.Def_OAI_Analysis_Cotype_QuadraticTypeTensor
import Definitions.Def_OAI_Analysis_Cotype_WalshAmplification

namespace OAI

noncomputable section
open scoped BigOperators
open WithLp
namespace Cotype
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
variable {Ω : Type*} [Fintype Ω]

def finiteL2DualLinear (g : Ω → (X →L[ℝ] ℝ)) : PiLp 2 (fun _ : Ω => X) →ₗ[ℝ] ℝ where
  toFun z := ∑ a, g a (z a)
  map_add' x y := by simp [Finset.sum_add_distrib]
  map_smul' c x := by simp [Finset.mul_sum]

theorem finiteL2DualLinear_bound (g : Ω → (X →L[ℝ] ℝ)) (z : PiLp 2 (fun _ : Ω => X)) :
    ‖finiteL2DualLinear g z‖ ≤ ‖(toLp 2 g : PiLp 2 (fun _ : Ω => (X →L[ℝ] ℝ)))‖ * ‖z‖ := by
  calc
    _ ≤ ∑ a, ‖g a (z a)‖ := norm_sum_le _ _
    _ ≤ ∑ a, ‖g a‖ * ‖z a‖ := Finset.sum_le_sum (fun a _ => (g a).le_opNorm _)
    _ ≤ _ := by
      simpa only [PiLp.norm_eq_of_L2, ofLp_toLp] using
        Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun a => ‖g a‖) (fun a => ‖z a‖)

def finiteL2Dual (g : Ω → (X →L[ℝ] ℝ)) : PiLp 2 (fun _ : Ω => X) →L[ℝ] ℝ :=
  (finiteL2DualLinear g).mkContinuous ‖(toLp 2 g : PiLp 2 (fun _ : Ω => (X →L[ℝ] ℝ)))‖
    (finiteL2DualLinear_bound g)

@[simp] theorem finiteL2Dual_apply (g : Ω → (X →L[ℝ] ℝ)) (z : PiLp 2 (fun _ : Ω => X)) :
    finiteL2Dual g z = ∑ a, g a (z a) := rfl

def probabilityL2Vector {n : ℕ} (f : Cube n → X) : PiLp 2 (fun _ : Cube n => X) :=
  Real.sqrt ((Fintype.card (Cube n) : ℝ)⁻¹) • toLp 2 f

def probabilityL2Dual {n : ℕ} (g : Cube n → (X →L[ℝ] ℝ)) :
    PiLp 2 (fun _ : Cube n => X) →L[ℝ] ℝ :=
  Real.sqrt ((Fintype.card (Cube n) : ℝ)⁻¹) • finiteL2Dual g

end Cotype

end

end OAI


