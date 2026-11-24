-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ThetaLiftGeometry_TemperedRepresentations
-- name    : Development_AbelianVarietyTheory_BlockTheory_ThetaLiftGeometry_TemperedRepresentations
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-24T18:34:08.227562+00:00
-- url     : https://prove2.me/theorems/9e6e6093-0fb0-4206-8cbe-e45b3cdafd2f
-- title:
--   Tempered Representations
-- statement:
--   Definitions and structural lemmas for Tempered Representations, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/ThetaLiftGeometry/TemperedRepresentations.lean

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataN
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GlobalTheory.IndefiniteRowSideFullHecke.TemperedRepresentations
open Formalism.BasicNotions Formalism.MainNotions.N
variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R}
def TemperedRank (N : NData R H what₂) (A : NAut N) (a : ℕ) : Prop :=
  ∀ π : A.CG a, A.csd π → A.ralg π → ∀ w : PlE H, A.tempered (A.locG π w)
def Tempered (N : NData R H what₂) (A : NAut N) : Prop :=
  ∀ (a : ℕ), 1 ≤ a → ∀ π : A.CG a, A.csd π → A.ralg π →
    ∀ w : PlE H, A.tempered (A.locG π w)
end GlobalTheory.IndefiniteRowSideFullHecke.TemperedRepresentations


