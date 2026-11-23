-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PowMulMemSubalgebraOfResBasicOpen
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_PowMulMemSubalgebraOfResBasicOpen
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:38:59.863353+00:00
-- url     : https://prove2.me/theorems/b97fb9b0-3076-4bf6-9cfd-7a2e7811e694
-- title:
--   Pow Mul Mem Subalgebra Of Res Basic Open
-- statement:
--   Definitions and structural lemmas for Pow Mul Mem Subalgebra Of Res Basic Open, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PowMulMemSubalgebraOfResBasicOpen.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SubNatCompSubIncl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsPowMulMemAdjoinOfLocalizationAwayStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AffineInterFiniteBasicOpenCoverStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemAdjoinRestrictedSectionsOfLocalStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits Opposite GlobalTheory.QcSub
namespace GlobalTheory.QcSub.PowerMultiple
variable {X : Scheme.{0}} (F : X.Opensᵒᵖ ⥤ CommRingCat) (α : X.presheaf ⟶ F)
end GlobalTheory.QcSub.PowerMultiple


