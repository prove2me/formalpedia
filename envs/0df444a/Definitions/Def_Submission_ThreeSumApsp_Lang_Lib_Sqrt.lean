-- Prove2me | Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Sqrt
-- name    : Submission_ThreeSumApsp_Lang_Lib_Sqrt
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T07:52:14.742213+00:00
-- url     : https://prove2.me/theorems/4f6af4ca-3693-48c5-b783-62bbbdb2ae8e
-- title:
--   Sqrt
-- statement:
--   Shared definitions for the weighted-cache 3SUM development.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Lib/Sqrt.lean

module
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Tactics
public import Mathlib.Tactic.Positivity
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
namespace Sqrt
abbrev Arg : ℕ := 0
@[inherit_doc Arg] abbrev Cand : ℕ := 1
@[inherit_doc Arg] abbrev Square : ℕ := 2
end Sqrt
open Sqrt in
/-- sqrt(K). -/
def sqrtBody : Stmt :=
  .set Cand (k 0) ;;
  .set Square (k 1) ;;
  .while (v Square ≤' v Arg) (
    .set Square (v Square +' k 2 *' v Cand +' k 3) ;;
    .set Cand (v Cand +' k 1)) ;;
  .set Arg (v Cand)
@[simp] def sqrtTime (K : ℕ) : ℕ := 18 * Nat.sqrt K + 12
end Light


