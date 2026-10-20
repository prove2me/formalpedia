-- Prove2me | Definitions.Def_OAI_Analysis_Cotype_FrameOrbit
-- name    : OAI_Analysis_Cotype_FrameOrbit
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T18:11:12.30399+00:00
-- url     : https://prove2.me/theorems/10ea7f3d-62cf-4e60-abd9-a7bb2508dc31
-- title:
--   Coordinate duality for finite coordinate spaces
-- statement:
--   These notions belong to a proof that a real Banach space $X$ with the approximation property is K-convex (the Rademacher projection is bounded on $L_2(\{\pm1\}^n;X)$ uniformly in $n$) if and only if $X$ and its dual $X^*$ both have finite cotype. The converse direction shows that such $X$ has nontrivial type, i.e. does not contain $\ell_1^n$ uniformly, and then derives K-convexity from a power-gap estimate for commuting coordinate projections. Let $\mathbb K$ be a field and $\iota$ finite.
--
--   1. **Coordinate dual.** The linear isomorphism $\mathbb K^\iota\to(\mathbb K^\iota)^*$,
--   $$
--   v\mapsto\Bigl(w\mapsto\sum_iv_iw_i\Bigr),
--   $$
--   with inverse reading values on the unit vectors. Over $\mathbb F_2$ it identifies Walsh characters with linear functionals.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Cotype/FrameOrbit.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Cotype/FrameOrbit.lean by skeleton subtraction
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
import Definitions.Def_OAI_Analysis_Cotype_FiniteSupDual
import Definitions.Def_OAI_Analysis_Cotype_PrimalMomentLifts
import Definitions.Def_OAI_Analysis_Cotype_CotypeAmplification
import Definitions.Def_OAI_Analysis_Cotype_TypeCotypeDuality
import Definitions.Def_OAI_Analysis_Cotype_Rectangles
import Definitions.Def_OAI_Analysis_Cotype_BinaryRank
import Definitions.Def_OAI_Analysis_Cotype_BiasedFourier
import Definitions.Def_OAI_Analysis_Cotype_Damping
import Definitions.Def_OAI_Analysis_Cotype_WalshExactPairing
import Definitions.Def_OAI_Analysis_Cotype_WalshSymmetry
import Definitions.Def_OAI_Analysis_Cotype_CubeCoordinateProjections
import Definitions.Def_OAI_Analysis_Cotype_CubeFirstChaos

namespace OAI

noncomputable section

open scoped BigOperators
namespace Cotype
variable {𝕜 : Type*} [Field 𝕜]
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

def coordinateDual : (ι → 𝕜) ≃ₗ[𝕜] Module.Dual 𝕜 (ι → 𝕜) where
  toFun v :=
    { toFun := fun w => ∑ i, v i * w i
      map_add' := by intro x y; simp [mul_add, Finset.sum_add_distrib]
      map_smul' := by intro t x; simp [Finset.mul_sum, mul_left_comm] }
  invFun f i := f (Pi.single i 1)
  left_inv := by intro v; funext i; simp [Pi.single_apply]
  right_inv := by
    intro f
    apply LinearMap.ext
    intro x
    change (∑ i, f (Pi.single i 1) * x i) = f x
    conv_rhs => rw [pi_eq_sum_univ' x, map_sum]
    simp [mul_comm]
  map_add' := by intro x y; ext w; simp [add_mul, Finset.sum_add_distrib]
  map_smul' := by intro t x; ext w; simp [mul_assoc, Finset.mul_sum]

@[simp] theorem coordinateDual_apply (v w : ι → 𝕜) :
    coordinateDual v w = ∑ i, v i * w i := rfl

variable {E : Type*} [AddCommGroup E] [Module 𝕜 E]

end Cotype

end

end OAI


