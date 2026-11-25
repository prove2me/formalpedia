-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NcardDependentVectorsAffineGramLe
-- name    : Development_AbelianVarietyTheory_Proofs_FlagMeasures_NcardDependentVectorsAffineGramLe
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T05:19:34.315562+00:00
-- url     : https://prove2.me/theorems/2dbb93a9-c93a-50e0-ac98-7649fb323762
-- title:
--   Ncard Dependent Vectors Affine Gram Le
-- statement:
--   Definitions and structural lemmas for Ncard Dependent Vectors Affine Gram Le, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/NcardDependentVectorsAffineGramLe.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_PrimOfIsUnitDet
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.GramCount
open scoped Classical
namespace GlobalTheory.GramCount
variable {B : Type} [CommRing B]
def depSet (c : B →+* B) {k n : ℕ} (x : Fin k → Fin n → B) (g : Fin k → B) (a : B) :
    Set (Fin n → B) :=
  {y | (∀ i, ip c y (x i) = g i) ∧ ∃ s : Fin k → B, a • y = ∑ i, s i • x i}
end GlobalTheory.GramCount


