-- Prove2me | Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Logs
-- name    : Submission_ThreeSumApsp_Lang_Lib_Logs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T07:37:30.129147+00:00
-- url     : https://prove2.me/theorems/187427fa-e1c1-4223-9f05-94d3e46aed36
-- title:
--   Logs
-- statement:
--   Definitions and structural lemmas for Logs, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Lib/Logs.lean

module
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Tactics
public import Mathlib.Data.Nat.Log
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Theorems.Thm_Light_Ends_set
public import Theorems.Thm_Light_sameFrame_cons_cons
public import Theorems.Thm_Light_sameFrame_cons_nil
public import Theorems.Thm_Light_sameFrame_nil
public import Theorems.Thm_Light_sameFrame_nil_cons
public import Theorems.Thm_Light_toNat_natCast_add_natCast
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast


set_option autoImplicit false
@[expose] public section
namespace Light
variable {lim : Limits} {P : Program} {d : ℕ}
namespace Logs
abbrev Arg : ℕ := 0
@[inherit_doc Arg] abbrev Cand : ℕ := 1
@[inherit_doc Arg] abbrev Power : ℕ := 2
end Logs
open Logs
def log2Body : Stmt :=
  .set Cand (k 0) ;;
  .set Power (k 2) ;;
  .while (v Power ≤' v Arg) (
    .set Power (v Power +' v Power) ;;
    .set Cand (v Cand +' k 1)) ;;
  .set Arg (v Cand)
@[simp] def log2Time (x : ℕ) : ℕ := 14 * Nat.log 2 x + 12
def clog2Body : Stmt :=
  .set Cand (k 0) ;;
  .set Power (k 1) ;;
  .while (v Power <' v Arg) (
    .set Power (v Power +' v Power) ;;
    .set Cand (v Cand +' k 1)) ;;
  .set Arg (v Cand)
@[simp] def clog2Time (x : ℕ) : ℕ := 12 * Nat.clog 2 x + 10
theorem exists_le_cube (n : ℕ) : ∃ s, n ≤ s ^ 3 := ⟨n, Nat.le_self_pow (by norm_num) n⟩
def cbrtLeast (n : ℕ) : ℕ := Nat.find (exists_le_cube n)
def cbrtCeilBody : Stmt :=
  .set Cand (k 0) ;;
  .while (v Cand *' v Cand *' v Cand <' v Arg) (
    .set Cand (v Cand +' k 1)) ;;
  .set Arg (v Cand)
@[simp] def cbrtCeilTime (n : ℕ) : ℕ := 12 * cbrtLeast n + 12
def halfBody : Stmt :=
  .set Cand (k 0) ;;
  .while (v Cand +' v Cand <' v Arg) (
    .set Cand (v Cand +' k 1)) ;;
  .set Arg (v Cand)
@[simp] def halfTime (h : ℕ) : ℕ := 10 * ((h + 1) / 2) + 10
end Light


