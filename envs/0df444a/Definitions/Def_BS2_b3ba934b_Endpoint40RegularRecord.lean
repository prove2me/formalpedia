-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint40RegularRecord
-- name    : BS2_b3ba934b_Endpoint40RegularRecord
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T05:59:34.548593+00:00
-- url     : https://prove2.me/theorems/77956d60-577f-4f94-8326-09cfac77b56e
-- title:
--   Sensitivity separation: Endpoint40RegularRecord (complete source module)
-- statement:
--   Complete Lean source module `Endpoint40RegularRecord` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. Original declarations and proof bodies are retained, with local import paths rewritten and residual references explicitly qualified as ThreeBoundRecordFields.residual to avoid the Mathlib topology name collision. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RegularRecord.lean; original SHA-256 dcba10d6ecf6a24dd329fb643d4c875365b2e0d165d38a90ecadf1caf07e373a; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

/- The saturated seven-guard case has a single exact record, independently
of its orientation.  This replaces exhaustive reductions of regular tournaments. -/
import Definitions.Def_BS2_b3ba934b_SaturatedOrientations
import Definitions.Def_BS2_b3ba934b_Q2RecordFields
import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_RecordChunking

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 200000

namespace ThreeBoundEndpoint40Regular
open ThreeBoundQ2 ThreeBoundRecordFields ThreeBoundRecordLookup ThreeBoundSaturated

def allG2 : List Kind := List.replicate 7 5

theorem get_allG2 (v : Fin allG2.length) : allG2.get v=5 := by
  fin_cases v <;> rfl

theorem incoming_allG2 (ds : List Bool) (v : Fin allG2.length) :
    ThreeBoundRecordFields.incoming allG2 ds v=inCount (edges 7) ds v := by
  unfold ThreeBoundRecordFields.incoming
  simp only [get_allG2,show isGuard (5 : Kind)=true from rfl,Bool.true_and]
  rw [← List.countP_eq_length_filter,← inCount_eq_countP]
  rfl

def regularRecord : List ℕ :=
  [0,0,0,0,0,7,0,0,0,0,0,0,0,0,0,0,0,0,0,0,7,0,0,0,0,0,0,0,0]

theorem record_eq_regular (ds : List Bool)
    (h : ds ∈ orientations (fun v : Fin allG2.length => budget (allG2.get v)) (edges allG2.length)) :
    record (allG2,ds)=regularRecord := by
  have hb : (fun v : Fin allG2.length => budget (allG2.get v))=(fun _=>3) := by
    funext v
    rw [get_allG2]
    rfl
  rw [hb] at h
  have hreg := regular_seven ds h
  have hr : _root_.ThreeBoundRecordFields.residual allG2 ds=(fun _=>0) := by
    funext v
    simp only [_root_.ThreeBoundRecordFields.residual,get_allG2,show budget (5 : Kind)=3 from rfl]
    change 3-outCount (edges 7) ds v=0
    rw [(hreg v).1]
  have hi : ThreeBoundRecordFields.incoming allG2 ds=(fun _=>3) := by
    funext v
    rw [incoming_allG2]
    exact (hreg v).2
  rw [record_explicit]
  simp only [typeCount,external,histogram,residualPrefix,sortedResiduals,hr,hi,get_allG2,
    List.mergeSort_eq_insertionSort]
  rfl

theorem regular_in_tree : ThreeBoundEndpoint40Records.tree.contains regularRecord=true := by
  decide +kernel

theorem cases_regular (c : List Kind × List Bool) (hc : c ∈ casesFor allG2) :
    ThreeBoundEndpoint40Records.tree.contains (recordFast c)=true := by
  have ha : allowedTypes allG2 := by decide +kernel
  rw [casesFor,if_pos ha] at hc
  obtain ⟨ds,hds,rfl⟩ := List.mem_map.mp hc
  rw [recordFast_eq,record_eq_regular ds hds]
  exact regular_in_tree

theorem checked_type7_regular :
    checkTypes ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5,5]=true := by
  apply List.all_eq_true.mpr
  intro c hc
  exact cases_regular c hc

theorem checked_regular_chunk (start count : ℕ) :
    checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5,5] start count=true := by
  apply List.all_eq_true.mpr
  intro c hc
  exact cases_regular c (List.mem_of_mem_drop (List.mem_of_mem_take hc))

end ThreeBoundEndpoint40Regular

#print axioms ThreeBoundEndpoint40Regular.record_eq_regular
#print axioms ThreeBoundEndpoint40Regular.checked_type7_regular


