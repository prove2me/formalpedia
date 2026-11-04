-- Prove2me | Definitions.Def_Submission_ThreeSum_LightTernaryEulerScan
-- name    : Submission_ThreeSum_LightTernaryEulerScan
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:34:07.530573+00:00
-- url     : https://prove2.me/theorems/811ef782-3f4e-4af5-86fc-e60a39ff0bca
-- title:
--   Light Ternary Euler Scan
-- statement:
--   Definitions and structural lemmas for Light Ternary Euler Scan, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryEulerScan.lean

import Definitions.Def_Submission_ThreeSum_LightTernaryEulerRow
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set
import Theorems.Thm_Light_Ends_skip
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSum_LightTernaryWeightedSum_sum_zero
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
attribute [local simp] ThreeSum.LightTernaryWeightedSum.sum_zero


set_option autoImplicit false
namespace ThreeSum.LightTernaryEulerScan
open Light
set_option maxHeartbeats 1800000
def stageValue (μ : ℕ → ℤ) (f : ℕ → ℤ) (rank : ℕ → ℕ)
    (vals current j a : ℕ) : ℤ :=
  if vals ≤ a ∧ a < vals+j ∧ rank (a-vals)=current then f (a-vals) else μ a
def Stored (μ ν : ℕ → ℤ) (f : ℕ → ℤ) (rank : ℕ → ℕ)
    (vals current fr j : ℕ) : Prop :=
  ∀ a < fr, ν a=stageValue μ f rank vals current j a
theorem stageValue_succ_of_ne (μ : ℕ → ℤ) (f : ℕ → ℤ) (rank : ℕ → ℕ)
    {vals current j a : ℕ} (hne : a ≠ vals+j) :
    stageValue μ f rank vals current (j+1) a=stageValue μ f rank vals current j a := by
  unfold stageValue
  have hh : (vals ≤ a ∧ a < vals+(j+1) ∧ rank (a-vals)=current) ↔
      (vals ≤ a ∧ a < vals+j ∧ rank (a-vals)=current) := by omega
  simp only [hh]
theorem Stored.skip {μ ν : ℕ → ℤ} {f : ℕ → ℤ} {rank : ℕ → ℕ}
    {vals current fr j : ℕ} (H : Stored μ ν f rank vals current fr j)
    (hrank : rank j≠current) : Stored μ ν f rank vals current fr (j+1) := by
  intro a ha
  rw [H a ha]
  by_cases he : a=vals+j
  · subst a
    simp [stageValue,hrank]
  · exact (stageValue_succ_of_ne μ f rank he).symm
def loopBody (pFill : ℕ) : Stmt :=
  .ite (M (v 4 +' v 10) =' v 6)
    (.call pFill [v 2 +' v 0 *' v 10,v 3 +' v 0 *' v 10,k 0,v 0,v 8,
      v 6 -' v 7,v 9,v 5 +' v 10] 11)
    .skip
def body (pFill : ℕ) : Stmt :=
  .for 10 (v 1) (loopBody pFill) ;;
  .set 0 (k 0)
def time (N rows V : ℕ) : ℕ := rows*(LightTernaryEulerRow.fillTime N V+150)+100
def Inv (μ : ℕ → ℤ) (f : ℕ → ℤ) (rank : ℕ → ℕ)
    (N rows ws ks ranks vals current h pcount fr j : ℕ) (σ : State) : Prop :=
  ∃ (rval : ℤ) (ν : ℕ → ℤ),
    σ=⟨frame [N,rows,ws,ks,ranks,vals,current,h,pcount,fr,j,rval],ν⟩ ∧
      Stored μ ν f rank vals current fr j
variable {lim : Limits} {P : Program} {d : ℕ}
end ThreeSum.LightTernaryEulerScan


