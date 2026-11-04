-- Prove2me | Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Pass
-- name    : Submission_ThreeSumApsp_Lang_Lib_Pass
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T07:35:23.843071+00:00
-- url     : https://prove2.me/theorems/7daf6e77-2e4e-4f1c-a983-56998fb861b4
-- title:
--   Pass
-- statement:
--   Definitions and structural lemmas for Pass, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Lib/Pass.lean

module
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Seg
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Rules
public import Theorems.Thm_Light_Ends_store

set_option autoImplicit false
@[expose] public section
namespace Light
variable {lim : Limits} {P : Program} {d : ℕ}
abbrev pass (c : ℕ) (len dst e : Expr) : Stmt := Stmt.for c len (.store (dst +' v c) e)
variable {μ : ℕ → ℤ} {dst j : ℕ} {f : ℕ → ℤ}
end Light


