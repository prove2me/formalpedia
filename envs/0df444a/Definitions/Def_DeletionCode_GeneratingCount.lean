-- Prove2me | Definitions.Def_DeletionCode_GeneratingCount
-- name    : DeletionCode_GeneratingCount
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T06:06:17.153332+00:00
-- url     : https://prove2.me/theorems/9987e980-783b-4db3-b46e-954d028b6b75
-- title:
--   Generating Count
-- statement:
--   Definitions and structural lemmas for Generating Count, from Eyal En Gad's pinned Deletion codes: binary insertion/deletion bound development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/GeneratingCount.lean

import Definitions.Def_DeletionCode_RecordSerialization
import Mathlib.SetTheory.Cardinal.Finite
import Theorems.Thm_DeletionCode_RecordSerialization_serialized_generating_coverage

set_option autoImplicit true
namespace DeletionCode.GeneratingCount
open Windows HeaderRecovery GeneratingModel GeneratingRecovery RecordSerialization DescriptionCount
def GeneratingData (x : Letters) (n k ν c : ℕ) (data : RecoveredData ν) : Prop :=
  ∃ E : EditedFamily (Fin ν) k,
    E.family.Generating x n (windowLength k) ∧
    Fintype.card (SupportComponents.GraphComponents E.family (windowLength k)) = c ∧
    dataOfFamily E = data
theorem generatingData_record_exists (x : Letters) (n k ν c : ℕ)
    (hν : 1 ≤ ν) (hx : KUnique x n k)
    (data : {data : RecoveredData ν // GeneratingData x n k ν c data}) :
    ∃ d : Description n (windowLength k) ν c,
      decodeDescription x n k ν c hν d = some data.val := by
  obtain ⟨E, hg, hc, hdata⟩ := data.property
  obtain ⟨d, hd⟩ := serialized_generating_coverage E x n c hν hx hg hc
  exact ⟨d, by simpa only [hdata] using hd⟩
noncomputable def encodeGeneratingData (x : Letters) (n k ν c : ℕ)
    (hν : 1 ≤ ν) (hx : KUnique x n k)
    (data : {data : RecoveredData ν // GeneratingData x n k ν c data}) :
    Description n (windowLength k) ν c :=
  Classical.choose (generatingData_record_exists x n k ν c hν hx data)
end DeletionCode.GeneratingCount


