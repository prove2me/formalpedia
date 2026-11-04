-- Prove2me | Definitions.Def_Submission_ThreeSum_LightTernaryMomentBatch
-- name    : Submission_ThreeSum_LightTernaryMomentBatch
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:46:11.011233+00:00
-- url     : https://prove2.me/theorems/8d837b1e-46cc-4b60-abb6-85b72575c1e6
-- title:
--   Light Ternary Moment Batch
-- statement:
--   Definitions and structural lemmas for Light Ternary Moment Batch, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryMomentBatch.lean

import Definitions.Def_Submission_ThreeSum_LightTernaryMomentRow
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set
import Theorems.Thm_Light_Ends_skip

set_option autoImplicit false
noncomputable section
namespace ThreeSum.LightTernaryMomentBatch
open Light FiniteMomentZeroDetector
attribute [local instance] Classical.propDecidable
def flag (hit : ℕ→Prop) (i : ℕ) : ℤ := by
  classical
  exact if ∃ j < i, hit j then 1 else 0
def body (H pRow : ℕ) : Stmt :=
  .set 6 (k 0) ;;
  .set 8 (k 0) ;;
  .for 7 (v 1) (
    .call pRow [v 0 +' k 3 *' v 7,v 2,v 3,v 4,v 1,v 7,v 5] 8 ;;
    .ite (k 0 <' v 8) (.set 6 (k 1)) .skip) ;;
  .set 0 (v 6)
def time (H count : ℕ) : ℕ := count*(LightTernaryMomentRow.time H+200)+30
structure Procs (H : ℕ) (P : Program) (pMain : ℕ) where
  pRow : ℕ
  row : LightTernaryMomentRow.Procs H P pRow
  main : P[pMain]?=some (body H pRow)
def Inv (μ : ℕ→ℤ) (hit : ℕ→Prop)
    (records count originalA originalCount matrix scratch i : ℕ) (σ : State) : Prop :=
  ∃ (r : ℤ) (ν : ℕ→ℤ),
    σ=⟨frame [records,count,originalA,originalCount,matrix,scratch,flag hit i,i,r],ν⟩ ∧
      Kept μ ν scratch
variable {lim : Limits} {P : Program} {d : ℕ}
def program (H : ℕ) : Program :=
  [body H 1,LightTernaryMomentRow.body H 2 3,LightTernaryMomentGather.body,
    LightMomentDeterminant.body (LightMomentZeroDetector.atoms H) H]
def procs (H : ℕ) : Procs H (program H) 0 where
  pRow := 1
  row := ⟨2,3,rfl,rfl,rfl⟩
  main := rfl
end ThreeSum.LightTernaryMomentBatch


