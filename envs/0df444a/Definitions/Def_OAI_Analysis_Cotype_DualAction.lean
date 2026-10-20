-- Prove2me | Definitions.Def_OAI_Analysis_Cotype_DualAction
-- name    : OAI_Analysis_Cotype_DualAction
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T18:23:09.310565+00:00
-- url     : https://prove2.me/theorems/27bbfe8d-8e51-4b45-9a8e-5be740f621ea
-- title:
--   Dual actions of isometry groups
-- statement:
--   These notions belong to a proof that a real Banach space $X$ with the approximation property is K-convex (the Rademacher projection is bounded on $L_2(\{\pm1\}^n;X)$ uniformly in $n$) if and only if $X$ and its dual $X^*$ both have finite cotype. The converse direction shows that such $X$ has nontrivial type, i.e. does not contain $\ell_1^n$ uniformly, and then derives K-convexity from a power-gap estimate for commuting coordinate projections. Let $\rho$ be a representation of a group $\Gamma$ by linear isometries of $X$.
--
--   1. **Dual isometry.** For a linear isometric isomorphism $e$, the map $\varphi\mapsto\varphi\circ e^{-1}$ is a linear isometric isomorphism of $X^*$.
--   2. **Dual action.**
--   $$
--   g\mapsto\bigl(\varphi\mapsto\varphi\circ\rho(g)^{-1}\bigr),
--   $$
--   a representation of $\Gamma$ on $X^*$ by isometries, compatible with the pairing: $(g\varphi)(\rho(g)x)=\varphi(x)$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Cotype/DualAction.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Cotype/DualAction.lean by skeleton subtraction
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
import Definitions.Def_OAI_Analysis_Cotype_FrameOrbit
import Definitions.Def_OAI_Analysis_Cotype_BinaryCoordinates
import Definitions.Def_OAI_Analysis_Cotype_WalshFrameOrbit
import Definitions.Def_OAI_Analysis_Cotype_FrameFeasibility
import Definitions.Def_OAI_Analysis_Cotype_EquivariantLifts

namespace OAI

noncomputable section
namespace Cotype
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

def dualIsometry (e : X ≃ₗᵢ[ℝ] X) : (X →L[ℝ] ℝ) ≃ₗᵢ[ℝ] (X →L[ℝ] ℝ) where
  toFun f := f.comp e.symm.toContinuousLinearEquiv.toContinuousLinearMap
  invFun f := f.comp e.toContinuousLinearEquiv.toContinuousLinearMap
  left_inv f := by ext x; simp
  right_inv f := by ext x; simp
  map_add' f g := by ext x; simp
  map_smul' c f := by ext x; simp
  norm_map' f := by
    apply le_antisymm
    · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg f)
      intro x
      simpa using f.le_opNorm (e.symm x)
    · apply f.opNorm_le_bound (norm_nonneg _)
      intro x
      have h := (f.comp e.symm.toContinuousLinearEquiv.toContinuousLinearMap).le_opNorm (e x)
      simpa using h

@[simp] theorem dualIsometry_apply (e : X ≃ₗᵢ[ℝ] X) (f : X →L[ℝ] ℝ) (x : X) :
    dualIsometry e f x = f (e.symm x) := rfl

variable {Γ : Type*} [Group Γ]

def dualAction (ρ : Γ →* (X ≃ₗᵢ[ℝ] X)) : Γ →* ((X →L[ℝ] ℝ) ≃ₗᵢ[ℝ] (X →L[ℝ] ℝ)) where
  toFun g := dualIsometry (ρ g)
  map_one' := by
    ext f x
    change f ((ρ 1).symm x) = f x
    rw [map_one]
    rfl
  map_mul' g h := by
    ext f x
    simp [dualIsometry_apply, map_mul, LinearIsometryEquiv.mul_def]

end Cotype

end

end OAI


