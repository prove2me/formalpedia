-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PSplitRelDeg
-- name    : GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PSplitRelDeg
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:44:13.849903+00:00
-- url     : https://prove2.me/theorems/a33d961b-20c3-474d-bfec-4dd281b60cdb
-- title:
--   PSplit Rel Deg
-- statement:
--   Definitions and structural lemmas for PSplit Rel Deg, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PSplitRelDeg.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsRename
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_ContractBlocksSplitPrime
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PRenameMultiHomog
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.FieldNumbers
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u
section SplitRelDeg
variable {F : Type u} [Field F] {K K' : Type} (j : K ↪ K') {ι' : K' → Type}
  (P' : Ideal (MRing ι' F)) [P'.IsPrime]
def splitQuotToFrac :
    (MRing (splitCoord j ι') F ⧸ splitPrime j P') →ₐ[F] FractionRing (MRing ι' F ⧸ P') :=
  (IsScalarTower.toAlgHom F (MRing ι' F ⧸ P') (FractionRing (MRing ι' F ⧸ P'))).comp
    (Ideal.quotientMapₐ P' (rename (splitVar j ι')) le_rfl)
def splitFracMap :
    FractionRing (MRing (splitCoord j ι') F ⧸ splitPrime j P') →ₐ[F]
      FractionRing (MRing ι' F ⧸ P') :=
  IsFractionRing.liftAlgHom (g := splitQuotToFrac j P')
    ((IsFractionRing.injective (MRing ι' F ⧸ P') (FractionRing (MRing ι' F ⧸ P'))).comp
      Ideal.quotientMap_injective)
end SplitRelDeg
end
end GroundTheory.Heights₂.Heights.FieldNumbers


