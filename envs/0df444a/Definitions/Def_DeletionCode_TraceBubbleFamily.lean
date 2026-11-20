-- Prove2me | Definitions.Def_DeletionCode_TraceBubbleFamily
-- name    : DeletionCode_TraceBubbleFamily
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T06:55:17.825178+00:00
-- url     : https://prove2.me/theorems/ab607493-2a2f-4842-8bcf-63b2d62ca0b6
-- title:
--   Trace Bubble Family
-- statement:
--   Definitions and structural lemmas for Trace Bubble Family, from Eyal En Gad's pinned Deletion codes: binary insertion/deletion bound development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/TraceBubbleFamily.lean

import Definitions.Def_DeletionCode_TraceEditData
import Definitions.Def_DeletionCode_RunBubbleConstruction
import Definitions.Def_DeletionCode_TraceSeparation
import Theorems.Thm_DeletionCode_RunBubbleConstruction_exists_deletion_bubble
import Theorems.Thm_DeletionCode_RunBubbleConstruction_exists_insertion_bubble
import Theorems.Thm_DeletionCode_TraceEditData_oneEditTarget_of_deletion
import Theorems.Thm_DeletionCode_TraceEditData_oneEditTarget_of_insertion
import Theorems.Thm_DeletionCode_TraceSeparation_sourcePosition_margins

set_option autoImplicit true
namespace DeletionCode.TraceBubbleFamily
open Windows HeaderRecovery CatalogueWords AlignmentTrace FiniteConflictGraph
open RunBubbleConstruction TraceEditData
def BubbleAt (trace : Trace) (k : ℕ) (c : EditColumn trace) :=
  LocalBubble k trace.source (oneEditTarget trace c) (position trace c) (orientation trace c)
theorem position_margins (trace : Trace) (k : ℕ)
    (hsep : Separated (4 * windowLength k) trace) (c : EditColumn trace) :
    4 * windowLength k ≤ position trace c ∧
      position trace c + 4 * windowLength k ≤ trace.source.length :=
  TraceSeparation.sourcePosition_margins hsep c.val c.property
theorem exists_bubbleAt (trace : Trace) (k : ℕ)
    (hx : KUnique (listLetters trace.source) trace.source.length k)
    (hsep : Separated (4 * windowLength k) trace) (c : EditColumn trace) :
    Nonempty (BubbleAt trace k c) := by
  have hm := position_margins trace k hsep c
  rcases column_cases trace c with ⟨b, hc⟩ | ⟨b, hc⟩
  · unfold BubbleAt
    rw [orientation_of_deletion trace c b hc, oneEditTarget_of_deletion trace c b hc]
    exact exists_deletion_bubble trace.source (position trace c) k hx hm.1 hm.2
  · unfold BubbleAt
    rw [orientation_of_insertion trace c b hc, oneEditTarget_of_insertion trace c b hc]
    obtain ⟨p, _⟩ := exists_insertion_bubble trace.source (position trace c) k b hx hm.1 hm.2
    exact ⟨p⟩
noncomputable def bubbleAt (trace : Trace) (k : ℕ)
    (hx : KUnique (listLetters trace.source) trace.source.length k)
    (hsep : Separated (4 * windowLength k) trace) (c : EditColumn trace) :
    BubbleAt trace k c := Classical.choice (exists_bubbleAt trace k hx hsep c)
noncomputable def bubbleWords (trace : Trace) (k : ℕ)
    (hx : KUnique (listLetters trace.source) trace.source.length k)
    (hsep : Separated (4 * windowLength k) trace) : EditColumn trace → BubbleWord k :=
  fun c => (bubbleAt trace k hx hsep c).bubble
noncomputable def indexedBubbleWords (trace : Trace) (k t : ℕ)
    (hx : KUnique (listLetters trace.source) trace.source.length k)
    (hsep : Separated (4 * windowLength k) trace)
    (hdel : trace.deletions = t) (hins : trace.insertions = t) : Fin (2 * t) → BubbleWord k :=
  fun i => bubbleWords trace k hx hsep (editEquiv trace t hdel hins i)
end DeletionCode.TraceBubbleFamily


