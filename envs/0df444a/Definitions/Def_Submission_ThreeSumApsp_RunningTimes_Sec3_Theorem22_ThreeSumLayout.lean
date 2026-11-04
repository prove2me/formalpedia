-- Prove2me | Definitions.Def_Submission_ThreeSumApsp_RunningTimes_Sec3_Theorem22_ThreeSumLayout
-- name    : Submission_ThreeSumApsp_RunningTimes_Sec3_Theorem22_ThreeSumLayout
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T11:34:12.375195+00:00
-- url     : https://prove2.me/theorems/4dd07601-b331-4b36-a394-6690a449ac13
-- title:
--   Three Sum Layout
-- statement:
--   Definitions and structural lemmas for Three Sum Layout, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/RunningTimes/Sec3/Theorem22/ThreeSumLayout.lean

import Definitions.Def_Submission_ThreeSumApsp_Lang_TopProcedure
import Definitions.Def_Submission_ThreeSumApsp_Programs_Tasks
import Theorems.Thm_Light_Limits_Addr_abs_le
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_seg_memOf
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_Light_verdictOf_flag
import Theorems.Thm_ThreeSumApsp_Dominated_trans
import Theorems.Thm_ThreeSumApsp_Spec_length_affL
import Theorems.Thm_ThreeSumApsp_Spec_length_subMat
import Theorems.Thm_ThreeSumApsp_WordRam_AgreeOutside_trans
import Theorems.Thm_ThreeSumApsp_WordRam_Bounded_abs_le
import Theorems.Thm_ThreeSumApsp_WordRam_Steps_trans
import Theorems.Thm_ThreeSumApsp_WordRam_effects_cons
import Theorems.Thm_ThreeSumApsp_WordRam_effects_nil
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
attribute [local simp] ThreeSumApsp.Spec.length_affL
attribute [local simp] ThreeSumApsp.Spec.length_subMat
attribute [local simp] ThreeSumApsp.WordRam.effects_cons
attribute [local simp] ThreeSumApsp.WordRam.effects_nil


set_option autoImplicit false
section
namespace Light.Sec3
open ThreeSumApsp ThreeSumApsp.WordRam ThreeSumApsp.Spec
theorem vecOf_ofFn {n : ℕ} (x : Fin n → ℤ) : vecOf n (List.ofFn x) = x := by
  funext i
  simp [vecOf, List.getD_eq_getElem?_getD]
def threeSumInst (x : Bounded EndStatement.ThreeSum) : s3Task.Inst := ⟨x.n, x.U, 1, List.ofFn x.x⟩
theorem pre_threeSum (x : Bounded EndStatement.ThreeSum) (hn : 1 ≤ x.n) (hU : 1 ≤ x.U) :
    s3Task.Pre (threeSumInst x) (memOf ((ofEnd EndStatement.ThreeSum).input x)) (x.n + 1) where
  N_pos := hn
  U_pos := hU
  len := List.length_ofFn (f := x.x)
  seg := by
    simpa [EndStatement.ThreeSum, threeSumInst] using seg_memOf [(x.n : ℤ)] (List.ofFn x.x) []
  le := fun _ ha => Bounded.abs_le ha
  below := (Nat.add_comm 1 x.n).le
theorem post_threeSum (x : Bounded EndStatement.ThreeSum) (r : ℤ) (μ' : ℕ → ℤ)
    (h : s3Task.Post (threeSumInst x) (memOf ((ofEnd EndStatement.ThreeSum).input x)) (x.n + 1) r
      μ') :
    (ofEnd EndStatement.ThreeSum).IsAnswer x (verdictOf true r) fun i =>
      μ' (((ofEnd EndStatement.ThreeSum).input x).length + i) := by
  obtain ⟨rfl, -⟩ := h
  exact ⟨(verdictOf_flag _).trans (iff_of_eq (congrArg ThreeSum (vecOf_ofFn x.x))), trivial⟩
noncomputable def wrap3Sum : Wrap EndStatement.ThreeSum s3Task true where
  args := [v 1, v 2, k 1, v 1 +' k 1]
  inst := threeSumInst
  fr x := x.n + 1
  size_eq _ := rfl
  bound_eq _ := rfl
  fr_pos x := by omega
  fr_le x := by
    have := Nat.le_mul_self x.n
    omega
  vals x σ hn hU _ := by simp [s3Task, threeSumInst, hn, hU]
  safe x lim σ hn _ _ hw := by
    have hnn : (x.n : ℤ) ≤ (x.n : ℤ) * x.n := by exact_mod_cast Nat.le_mul_self x.n
    push_cast at hw
    simp [hn, abs_le]
    omega
  zero x hn _ := ⟨⟨fun h => absurd h (by simp), fun ⟨i, _⟩ => absurd i.isLt (by omega)⟩, trivial⟩
  pre := pre_threeSum
  post x r μ' _ h := post_threeSum x r μ' h
end Light.Sec3


