-- Prove2me | Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Copy
-- name    : Submission_ThreeSumApsp_Lang_Lib_Copy
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:14:30.848884+00:00
-- url     : https://prove2.me/theorems/6a4bee9a-25ed-47da-a6cb-fa203c9c6f00
-- title:
--   Copy
-- statement:
--   Definitions and structural lemmas for Copy, from the weighted-cache deterministic 3SUM development.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Lib/Copy.lean

import Definitions.Def_Submission_ThreeSumApsp_Lang_Calls
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Pass
import Definitions.Def_WeightedCache3SUM_Alias_231e42e414403f8e
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast


set_option autoImplicit false
section
namespace Light
variable {lim : Limits} {P : Program} {d : ℕ}
namespace Copy
abbrev Src : ℕ := 0
@[inherit_doc Src] abbrev Dst : ℕ := 1
@[inherit_doc Src] abbrev Len : ℕ := 2
@[inherit_doc Src] abbrev Idx : ℕ := 3
end Copy
open Copy in
/-- copy(src, dst, n): for i < n, dst[i] := src[i]. -/
def copyBody : Stmt := pass Idx (v Len) (v Dst) (M (v Src +' v Idx))
@[simp] def copyTime (n : ℕ) : ℕ := 16 * n + 6
namespace Fill
abbrev Dst : ℕ := 0
@[inherit_doc Dst] abbrev Len : ℕ := 1
@[inherit_doc Dst] abbrev Val : ℕ := 2
@[inherit_doc Dst] abbrev Idx : ℕ := 3
end Fill
open Fill in
/-- fill(dst, n, x): for i < n, dst[i] := x. -/
def fillBody : Stmt := pass Idx (v Len) (v Dst) (v Val)
@[simp] def fillTime (n : ℕ) : ℕ := 13 * n + 6
end Light


