-- Prove2me | Definitions.Def_Submission_ThreeSum_TernaryCoverRegularity
-- name    : Submission_ThreeSum_TernaryCoverRegularity
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T07:51:16.861814+00:00
-- url     : https://prove2.me/theorems/8fc623fd-7408-4fd7-835d-1c6936502835
-- title:
--   Ternary Cover Regularity
-- statement:
--   Shared definitions for the weighted-cache 3SUM development.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverRegularity.lean

import Definitions.Def_Submission_ThreeSum_TernaryCoverLocal
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Tactic
import Theorems.Thm_ThreeSum_TernaryCoverLocal_edge_data

set_option autoImplicit false
noncomputable section
namespace ThreeSum.TernaryCoverRegularity
open Finset TernaryJointType TernaryCoverLocal
variable {L : ℕ}
def reindex (σ : Equiv.Perm (Fin L)) (w : TritWord L) : TritWord L := w ∘ σ
theorem digitCount_reindex (σ : Equiv.Perm (Fin L)) (w : TritWord L) (d : Fin 3) :
    digitCount (reindex σ w) d = digitCount w d :=
  Equiv.sum_comp σ (fun i => if w i = d then 1 else 0)
theorem type_reindex (σ : Equiv.Perm (Fin L)) {w : TritWord L} {α : DigitType}
    (hw : HasType w α) : HasType (reindex σ w) α := by
  intro d
  rw [digitCount_reindex]
  exact hw d
theorem edge_reindex (σ : Equiv.Perm (Fin L)) {a b q : TritWord L} {α π : DigitType}
    (he : Edge α π a b q) : Edge α π (reindex σ a) (reindex σ b) (reindex σ q) :=
  ⟨type_reindex σ he.1, type_reindex σ he.2.1, type_reindex σ he.2.2.1, fun i => he.2.2.2 (σ i)⟩
def mapEdge (σ : Equiv.Perm (Fin L)) {α π : DigitType} (e : LocalEdge L α π) :
    LocalEdge L α π := by
  classical
  exact ⟨(reindex σ (left e), reindex σ (right e), reindex σ (output e)),
    mem_filter.mpr ⟨mem_univ _, edge_reindex σ (edge_data e)⟩⟩
abbrev sourceFiber (α π : DigitType) (a : TritWord L) := {e : LocalEdge L α π // left e = a}
def swapEdge {α π : DigitType} (e : LocalEdge L α π) : LocalEdge L α π := by
  classical
  refine ⟨(right e,left e,output e), mem_filter.mpr ⟨mem_univ _, ?_⟩⟩
  have h := edge_data e
  exact ⟨h.2.1,h.1,h.2.2.1,fun i => (Nat.add_comm _ _).trans (h.2.2.2 i)⟩
end ThreeSum.TernaryCoverRegularity


