-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ThetaLiftGeometry_ThetaLiftOfEachRow
-- name    : Development_AbelianVarietyTheory_BlockTheory_ThetaLiftGeometry_ThetaLiftOfEachRow
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-24T18:34:04.348916+00:00
-- url     : https://prove2.me/theorems/957f6bab-7c88-479b-a74e-a3a4bdffbe22
-- title:
--   Theta Lift Of Each Row
-- statement:
--   Definitions and structural lemmas for Theta Lift Of Each Row, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/ThetaLiftGeometry/ThetaLiftOfEachRow.lean

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
noncomputable section
namespace GlobalTheory.IndefiniteRowSideFullHecke.ThetaLiftOfEachComponent
open Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions.N
def EachRowHasThetaLift {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂)
    (A : NAut N) : Prop :=
  ∀ (i : N.Loc) (σ : what₂.FT), what₂.isot (N.j i) σ ≠ ⊥ → ∃ P : A.AV i, thetaOf N A i σ P
variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)
end GlobalTheory.IndefiniteRowSideFullHecke.ThetaLiftOfEachComponent


