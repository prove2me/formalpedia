-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_EqZeroOfFderivEqZero
-- name    : Development_AbelianVarietyTheory_Proofs_ModuliProofs_EqZeroOfFderivEqZero
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T16:40:58.528805+00:00
-- url     : https://prove2.me/theorems/b9865a3e-9409-46b3-9c00-4ec3faa4d1ef
-- title:
--   Eq Zero Of Fderiv Eq Zero
-- statement:
--   Definitions and structural lemmas for Eq Zero Of Fderiv Eq Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/EqZeroOfFderivEqZero.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EqZeroOfSemicharacterMultiplier
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_IsUnitOfLagrangian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsUniquePointOfRingHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsTestFunctionsSubsetOfMemNhds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsEtaleCoordsVanishing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TangentBijectionOfValues
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_LevelThreeSeparatesPoints
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_FderivEqZeroOfAffine
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_PolarisedTorusAlgebraicOfParts
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_DimB_ex_add

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real CategoryTheory.Obj
namespace GlobalTheory.TorusTransfer
section Tangent
variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)
end Tangent
section Reparam
variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)
def reparam (ψ : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (q : (Fin g → ℂ) → ℂ) (hq : Differentiable ℂ q)
    (Λ : Submodule ℤ (Fin g → ℂ)) (hd : DiscreteTopology Λ) (hf : Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤)
    (hΛ : ∀ z, ψ z ∈ u.Λ ↔ z ∈ Λ) : HolUnif A L g where
  ex z := u.ex (ψ z)
  ex_add z w := by rw [map_add, u.ex_add]
  ex_onto := u.ex_onto.comp ψ.surjective
  Λ := Λ
  ker z := (u.ker _).trans (hΛ z)
  discrete := hd
  full := hf
  hol U f := ⟨(u.hol U f).1.preimage ψ.toContinuousLinearEquiv.continuous,
    (u.hol U f).2.comp ψ.toContinuousLinearEquiv.differentiable.differentiableOn fun _ hz => hz⟩
  fr i z := u.fr i (ψ z) * cexp (q (ψ z))
  fr_hol i := ((u.fr_hol i).mul hq.cexp.differentiableOn).comp
    ψ.toContinuousLinearEquiv.differentiable.differentiableOn fun _ hz => hz
  fr_ne i z hz := mul_ne_zero (u.fr_ne i _ hz) (Complex.exp_ne_zero _)
  fr_compat i j z hz := by rw [u.fr_compat i j _ hz, _root_.mul_assoc]
end Reparam
section NormalForm
open SiegelNormalForm
variable {g : ℕ}
end NormalForm
end GlobalTheory.TorusTransfer


