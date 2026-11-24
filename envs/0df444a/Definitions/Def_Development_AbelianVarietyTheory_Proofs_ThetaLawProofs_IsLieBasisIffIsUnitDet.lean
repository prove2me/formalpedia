-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_IsLieBasisIffIsUnitDet
-- name    : Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_IsLieBasisIffIsUnitDet
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-24T22:25:02.890608+00:00
-- url     : https://prove2.me/theorems/d507cf36-96f8-4b0d-ade2-79654039b9a7
-- title:
--   Is Lie Basis Iff Is Unit Det
-- statement:
--   Definitions and structural lemmas for Is Lie Basis Iff Is Unit Det, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/IsLieBasisIffIsUnitDet.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_AwayToAwayRightEqOfComp
import Theorems.Thm_GlobalTheory_SqZero_lieExp_add
import Theorems.Thm_GlobalTheory_SqZero_lieExp_congr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_isTan_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_id

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap spMap_id isTan_iff)
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp epsR IsTangent IsLieComb IsLieBasis)
open TrivSqZeroExt (inl inr)
namespace GlobalTheory.LieComb
open GlobalTheory.SqZero
attribute [local instance] Over.cartesianMonoidalCategory
variable {R : Type} [CommRing R] {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]
  {n : ℕ} {v : Fin n → (epsR R ⟶ G)}
def combHom (hv : ∀ i, IsTangent (v i)) :
    (Fin n → R) →+ Additive (sp (R₀ := R) (DualNumber R) ⟶ G) :=
  AddMonoidHom.mk' (fun c => Additive.ofMul (tanExp v c)) (fun c c' => by
    rw [← ofMul_mul]
    refine congrArg Additive.ofMul ?_
    rw [← lieExp_add hv _ _ _ _ (fun _ => TrivSqZeroExt.inr_mul_inr _ _ _)
      (fun _ => by rw [← TrivSqZeroExt.inr_add]; exact TrivSqZeroExt.inr_mul_inr _ _ _)]
    exact lieExp_congr _ (fun i => TrivSqZeroExt.inr_add _ _ _) _ _)
end GlobalTheory.LieComb


