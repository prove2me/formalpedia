-- Prove2me | Definitions.Def_OAI_Analysis_Cotype_FiniteSupDual
-- name    : OAI_Analysis_Cotype_FiniteSupDual
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T17:31:31.357964+00:00
-- url     : https://prove2.me/theorems/9679c717-7244-4c32-836f-629525eca109
-- title:
--   Dual functionals on finite sup-sums
-- statement:
--   These notions belong to a proof that a real Banach space $X$ with the approximation property is K-convex (the Rademacher projection is bounded on $L_2(\{\pm1\}^n;X)$ uniformly in $n$) if and only if $X$ and its dual $X^*$ both have finite cotype. The converse direction shows that such $X$ has nontrivial type, i.e. does not contain $\ell_1^n$ uniformly, and then derives K-convexity from a power-gap estimate for commuting coordinate projections. Let $\Omega$ be finite.
--
--   1. **Finite sup dual.** A tuple $g_a\in X^*$ defines the functional
--   $$
--   f\mapsto\sum_ag_a(f(a))
--   $$
--   on $\ell_\infty(\Omega;X)$, with norm at most $\sum_a\|g_a\|$ (in fact equal). This identifies the dual of the sup-sum with the $\ell_1$-sum of duals.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Cotype/FiniteSupDual.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Cotype/FiniteSupDual.lean by skeleton subtraction
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
import Definitions.Def_OAI_Analysis_Cotype_FiniteL2Dual
import Definitions.Def_OAI_Analysis_Cotype_DualMomentLifts

namespace OAI

noncomputable section
open scoped BigOperators
namespace Cotype
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {Ω : Type*} [Fintype Ω]

def finiteSupDualLinear (g : Ω → (X →L[ℝ] ℝ)) : (Ω → X) →ₗ[ℝ] ℝ where
  toFun f := ∑ a, g a (f a)
  map_add' f h := by simp [Finset.sum_add_distrib]
  map_smul' c f := by simp [Finset.mul_sum]

theorem finiteSupDualLinear_bound (g : Ω → (X →L[ℝ] ℝ)) (f : Ω → X) :
    ‖finiteSupDualLinear g f‖ ≤ (∑ a, ‖g a‖) * ‖f‖ := by
  calc
    _ ≤ ∑ a, ‖g a (f a)‖ := norm_sum_le _ _
    _ ≤ ∑ a, ‖g a‖ * ‖f‖ := Finset.sum_le_sum (fun a _ =>
      ((g a).le_opNorm _).trans (mul_le_mul_of_nonneg_left (norm_le_pi_norm f a) (norm_nonneg _)))
    _ = _ := (Finset.sum_mul _ _ _).symm

def finiteSupDual (g : Ω → (X →L[ℝ] ℝ)) : (Ω → X) →L[ℝ] ℝ :=
  (finiteSupDualLinear g).mkContinuous (∑ a, ‖g a‖) (finiteSupDualLinear_bound g)

@[simp] theorem finiteSupDual_apply (g : Ω → (X →L[ℝ] ℝ)) (f : Ω → X) :
    finiteSupDual g f = ∑ a, g a (f a) := rfl

end Cotype

end

end OAI


