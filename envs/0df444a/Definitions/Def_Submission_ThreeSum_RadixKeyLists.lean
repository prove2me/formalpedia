-- Prove2me | Definitions.Def_Submission_ThreeSum_RadixKeyLists
-- name    : Submission_ThreeSum_RadixKeyLists
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:12:18.123973+00:00
-- url     : https://prove2.me/theorems/7c198f2a-b108-4470-b59e-8723bc960840
-- title:
--   Radix Key Lists
-- statement:
--   Definitions and structural lemmas for Radix Key Lists, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/RadixKeyLists.lean

import Definitions.Def_Submission_ThreeSum_GlobalEncoding
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.TakeDrop
set_option autoImplicit false
namespace ThreeSum.RadixKeyLists
variable {α β : Type*}
def step (p : ℤ) (base prev : List ℤ) : List ℤ :=
  base.flatMap fun x => prev.map fun y => x+p*y
def values (p : ℤ) (base : List ℤ) : ℕ → List ℤ
  | 0 => [0]
  | j+1 => step p base (values p base j)
def tuples (base : List α) : ℕ → List (List α)
  | 0 => [[]]
  | j+1 => base.flatMap fun a => (tuples base j).map (List.cons a)
end ThreeSum.RadixKeyLists


