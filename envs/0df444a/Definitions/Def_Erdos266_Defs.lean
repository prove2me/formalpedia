-- Prove2me | Definitions.Def_Erdos266_Defs
-- name    : Erdos266_Defs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T02:33:40.155895+00:00
-- url     : https://prove2.me/theorems/11539eae-4fe4-5e20-a2bd-21603d70e016
-- title:
--   Defs
-- statement:
--   Definitions and structural lemmas for Defs, from Ben Keene (benkeene/erdos266; Challenge statement adapted under Apache-2.0 from google-deepmind/formal-conjectures; see pinned LICENSE and README.md)'s pinned Erdos Problem 266: Kovac-Tao disproof of Stolarsky's conjecture on shifted Ahmes series development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/Defs.lean

module
public import Definitions.Def_Erdos266_Enumeration
set_option autoImplicit false
@[expose] public section
@[expose] public section
namespace Erdos266
open Finset
noncomputable def f (i : ℕ) (x : ℝ) : ℝ :=
  (∏ j ∈ range i, (x + (tSeq j : ℝ)))⁻¹
def m (i j : ℕ) : ℚ :=
  (∏ k ∈ (range i).erase j, (tSeq k - tSeq j))⁻¹
end Erdos266


