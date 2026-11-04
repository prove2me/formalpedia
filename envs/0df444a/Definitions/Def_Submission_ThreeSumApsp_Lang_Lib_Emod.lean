-- Prove2me | Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Emod
-- name    : Submission_ThreeSumApsp_Lang_Lib_Emod
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T07:37:31.388943+00:00
-- url     : https://prove2.me/theorems/8b620700-f39c-4321-b1b4-065624bd95e6
-- title:
--   Emod
-- statement:
--   Definitions and structural lemmas for Emod, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Lib/Emod.lean

module
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Seg
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Tactics
public import Mathlib.Data.Nat.Log
public import Mathlib.Data.Nat.Size
public import Mathlib.Tactic.NormNum
public import Theorems.Thm_Light_Ends_set
public import Theorems.Thm_Light_Ends_skip
public import Theorems.Thm_Light_Ends_store
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
namespace Emod
abbrev Arg : ℕ := 0
@[inherit_doc Arg] abbrev Modulus : ℕ := 1
@[inherit_doc Arg] abbrev Free : ℕ := 2
@[inherit_doc Arg] abbrev Rest : ℕ := 3
@[inherit_doc Arg] abbrev Count : ℕ := 4
@[inherit_doc Arg] abbrev Mult : ℕ := 5
end Emod
open Emod in
/-- One entry of the table: the multiple is written to the table and doubled. -/
def emodTableRound : Stmt :=
  .store (v Free +' v Count) (v Mult) ;;
  .set Count (v Count +' k 1) ;;
  .set Mult (v Mult +' v Mult)
open Emod in
/-- The table: M, 2M, 4M, … are written to the free pointer as long as they are at most |x|. -/
def emodTable : Stmt := .while (v Mult ≤' v Rest) emodTableRound
open Emod in
/-- The last entry of the table that has not been tried is subtracted if possible. -/
def emodReduceRound : Stmt :=
  .set Count (v Count -' k 1) ;;
  .ite (M (v Free +' v Count) ≤' v Rest) (.set Rest (v Rest -' M (v Free +' v Count))) .skip
open Emod in
/-- The entries of the table are subtracted, from the largest down, where possible. -/
def emodReduce : Stmt := .while (k 0 <' v Count) emodReduceRound
open Emod in
/-- The sign: the remainder r of |x| gives the remainder of x. -/
def emodSign : Stmt :=
  .ite (v Arg <' k 0)
    (.ite (v Rest =' k 0) (.set Arg (k 0)) (.set Arg (v Modulus -' v Rest)))
    (.set Arg (v Rest))
open Emod in
/-- emod(x, M, fr). -/
def emodBody : Stmt :=
  .ite (v Arg <' k 0) (.set Rest (k 0 -' v Arg)) (.set Rest (v Arg)) ;;
  .set Count (k 0) ;;
  .set Mult (v Modulus) ;;
  emodTable ;;
  emodReduce ;;
  emodSign
def emodRounds (a M : ℕ) : ℕ := Nat.size (a / M)
@[simp] def emodTime (a M : ℕ) : ℕ := 43 * emodRounds a M + 34
namespace Emod
structure Pre (lim : Limits) (Mo V fr : ℕ) : Prop where
  mod_pos : 1 ≤ Mo
  space : (lim.space : ℤ) ≤ lim.word
  word : (4 * V + 4 * Mo + 16 : ℤ) ≤ lim.word
  free : fr + (Nat.log 2 (V + 1) + 2) ≤ lim.space
def Table (μ μ' : ℕ → ℤ) (Mo fr i : ℕ) : Prop :=
  (∀ j < i, μ' (fr + j) = ((Mo * 2 ^ j : ℕ) : ℤ)) ∧ Kept μ μ' fr
variable {μ : ℕ → ℤ} {x : ℤ} {Mo V fr a : ℕ}
end Emod
end Light


