-- Prove2me | Definitions.Def_Submission_ThreeSum_ReportingHostRelocation
-- name    : Submission_ThreeSum_ReportingHostRelocation
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T07:46:23.474231+00:00
-- url     : https://prove2.me/theorems/656079a7-c2f1-45b4-a049-6784e9e8e67a
-- title:
--   Reporting Host Relocation
-- statement:
--   Shared definitions for reporting host relocation in the weighted-cache 3SUM development.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostRelocation.lean

import Definitions.Def_Submission_ThreeSumApsp_Lang_Calls
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set
import Theorems.Thm_Light_Ends_skip
import Theorems.Thm_Light_Ends_store
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
namespace ThreeSum.ReportingHostRelocation
open Light
@[simp] def relocate (offset : ℕ) : Stmt → Stmt
  | .skip => .skip
  | .set x e => .set x e
  | .store a e => .store a e
  | .seq s t => .seq (relocate offset s) (relocate offset t)
  | .ite c s t => .ite c (relocate offset s) (relocate offset t)
  | .while c s => .while c (relocate offset s)
  | .call p args x => .call (offset+p) args x
def program (prefixProgram P : Program) : Program := prefixProgram ++ P.map (relocate prefixProgram.length)
end ThreeSum.ReportingHostRelocation


