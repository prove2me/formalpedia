-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_GluingImageCardPowLeDefectGroupCard
-- name    : Development_AbelianVarietyTheory_Proofs_FlagMeasures_GluingImageCardPowLeDefectGroupCard
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T06:36:35.764796+00:00
-- url     : https://prove2.me/theorems/8dc5f77d-3b39-41ce-9710-d5ce166b060e
-- title:
--   Gluing Image Card Pow Le Defect Group Card
-- statement:
--   Definitions and structural lemmas for Gluing Image Card Pow Le Defect Group Card, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/GluingImageCardPowLeDefectGroupCard.lean

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CardEqPowAndIndexGe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetTermBasicFacts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TermExponentsNonnegAndDefectGroupBoundStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_PairingSecondTypeTestOnRepresentativesStatement
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks


set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
namespace GlobalTheory.HL.SmallImage
section
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)
def reps (Λ : Submodule L.O S.V) : Submodule L.O S.V where
  carrier := {y | y ∈ Λ ∧ ∃ w ∈ S.W0, ∃ la ∈ S.X, ∃ la' ∈ S.X', w + la ∈ Λ ∧
    la' - la = algebraMap F E S.th • y}
  zero_mem' := ⟨Λ.zero_mem, 0, Submodule.zero_mem _, 0, Submodule.zero_mem _, 0, Submodule.zero_mem _,
    by simp, by simp⟩
  add_mem' := by
    rintro a b ⟨ha, w, hw, la, hla, la', hla', h1, h2⟩ ⟨hb, v, hv, lb, hlb, lb', hlb', h3, h4⟩
    refine ⟨Λ.add_mem ha hb, w + v, add_mem hw hv, la + lb, add_mem hla hlb, la' + lb', add_mem hla' hlb',
      ?_, ?_⟩
    · rw [add_add_add_comm]; exact Λ.add_mem h1 h3
    · rw [smul_add, ← h2, ← h4]; abel
  smul_mem' := by
    rintro c a ⟨ha, w, hw, la, hla, la', hla', h1, h2⟩
    refine ⟨Λ.smul_mem c ha, (c : E) • w, Submodule.smul_mem _ _ hw, (c : E) • la,
      Submodule.smul_mem _ _ hla, (c : E) • la', Submodule.smul_mem _ _ hla', ?_, ?_⟩
    · rw [← smul_add]; exact Λ.smul_mem c h1
    · rw [← smul_sub, h2, smul_comm]; rfl
end
end GlobalTheory.HL.SmallImage


