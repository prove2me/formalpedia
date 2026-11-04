-- Prove2me | Definitions.Def_Submission_ThreeSumApsp_Lang_Assigns
-- name    : Submission_ThreeSumApsp_Lang_Assigns
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T07:25:21.997872+00:00
-- url     : https://prove2.me/theorems/856aa5a9-fb66-42c0-a55a-69ae2c5862d6
-- title:
--   Assigns
-- statement:
--   Definitions and structural lemmas for Assigns, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Assigns.lean

module
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Logic
public import Theorems.Thm_Light_Ends_call
public import Theorems.Thm_Light_Ends_set
public import Theorems.Thm_Light_Ends_skip
public import Theorems.Thm_Light_Ends_store
public import Theorems.Thm_Light_toNat_natCast_add_natCast
attribute [local simp] Light.toNat_natCast_add_natCast


set_option autoImplicit false
@[expose] public section
namespace Light
variable {lim : Limits} {P : Program} {d : ℕ}
@[simp] def Stmt.assigns : Stmt → List ℕ
  | .skip => []
  | .set x _ => [x]
  | .store _ _ => []
  | .seq s t => s.assigns ++ t.assigns
  | .ite _ s t => s.assigns ++ t.assigns
  | .while _ s => s.assigns
  | .call _ _ x => [x]
end Light


