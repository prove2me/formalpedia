-- Prove2me | Definitions.Def_OAI_Analysis_Cotype_WalshFrameOrbit
-- name    : OAI_Analysis_Cotype_WalshFrameOrbit
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T18:14:54.777986+00:00
-- url     : https://prove2.me/theorems/2f615bc6-47e7-418f-9afd-2fac64a6d032
-- title:
--   Linear Walsh symmetries
-- statement:
--   These notions belong to a proof that a real Banach space $X$ with the approximation property is K-convex (the Rademacher projection is bounded on $L_2(\{\pm1\}^n;X)$ uniformly in $n$) if and only if $X$ and its dual $X^*$ both have finite cotype. The converse direction shows that such $X$ has nontrivial type, i.e. does not contain $\ell_1^n$ uniformly, and then derives K-convexity from a power-gap estimate for commuting coordinate projections. Let $H$ be a linear automorphism of $\mathbb F_2^n$.
--
--   1. **Dual transport.** $\varphi\mapsto\varphi\circ H^{-1}$ on linear functionals.
--   2. **Contragredient.** $H^{-\top}$, transported through the coordinate dual, so that
--   $$
--   \langle H^{-\top}v,Hu\rangle=\langle v,u\rangle .
--   $$
--   3. **Linear Walsh symmetry.** $(H,H^{-\top})$ acting on the cube is a Walsh symmetry. Since $\mathrm{GL}_n(\mathbb F_2)$ acts transitively on linearly independent tuples, binary frames lie in one orbit.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Cotype/WalshFrameOrbit.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Cotype/WalshFrameOrbit.lean by skeleton subtraction
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

namespace OAI

noncomputable section

namespace Cotype
variable {n r s : ℕ}

def binaryDualTransport (H : BinarySpace n ≃ₗ[ZMod 2] BinarySpace n) :
    Module.Dual (ZMod 2) (BinarySpace n) ≃ₗ[ZMod 2] Module.Dual (ZMod 2) (BinarySpace n) where
  toFun φ := φ.comp H.symm.toLinearMap
  invFun φ := φ.comp H.toLinearMap
  left_inv := by intro φ; ext x; simp
  right_inv := by intro φ; ext x; simp
  map_add' := by intro φ ψ; rfl
  map_smul' := by intro c φ; rfl

def binaryContragredient (H : BinarySpace n ≃ₗ[ZMod 2] BinarySpace n) :
    BinarySpace n ≃ₗ[ZMod 2] BinarySpace n :=
  coordinateDual.trans ((binaryDualTransport H).trans coordinateDual.symm)

theorem binaryContragredient_pairing (H : BinarySpace n ≃ₗ[ZMod 2] BinarySpace n)
    (u v : BinarySpace n) :
    coordinateDual (binaryContragredient H v) (H u) = coordinateDual v u := by
  change coordinateDual (coordinateDual.symm ((coordinateDual v).comp H.symm.toLinearMap)) (H u) = _
  rw [coordinateDual.apply_symm_apply]
  simp

def walshSymmetryOfLinear (H : BinarySpace n ≃ₗ[ZMod 2] BinarySpace n) : WalshSymmetry n :=
  ⟨((cubeBinaryEquiv n).trans (H.toEquiv.trans (cubeBinaryEquiv n).symm),
    (cubeBinaryEquiv n).trans ((binaryContragredient H).toEquiv.trans (cubeBinaryEquiv n).symm)), by
    intro u v
    simp only [Equiv.trans_apply, character_binary_dot, Equiv.apply_symm_apply]
    exact congrArg binarySign (binaryContragredient_pairing H _ _)⟩

end Cotype

end

end OAI


