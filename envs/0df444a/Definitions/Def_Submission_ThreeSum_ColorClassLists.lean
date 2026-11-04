-- Prove2me | Definitions.Def_Submission_ThreeSum_ColorClassLists
-- name    : Submission_ThreeSum_ColorClassLists
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:33:25.952141+00:00
-- url     : https://prove2.me/theorems/07d4794f-0144-457a-ba57-66c5d32f0c10
-- title:
--   Color Class Lists
-- statement:
--   Definitions and structural lemmas for Color Class Lists, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ColorClassLists.lean

import Definitions.Def_Submission_ThreeSum_LightClassFilter
import Definitions.Def_Submission_ThreeSum_LightColorIndex
set_option autoImplicit false
namespace ThreeSum.ColorClassLists
open LightClassFilter
def value {n : ℕ} (x : Fin n → ℤ) (i : ℕ) : ℤ := if hi : i < n then x ⟨i,hi⟩ else 0
def indexColor {n W : ℕ} (p : Coloring.Parameter W) (i : Fin n) : Fin 3 :=
  p.2 (i.val.testBit p.1.1.val,i.val.testBit p.1.2.val)
def classList {n W : ℕ} (p : Coloring.Parameter W) (x : Fin n → ℤ)
    (c : ℕ) (scale : ℤ) : List ℤ :=
  items (value x) (LightColorIndex.color p) c scale n
def witness {n W : ℕ} (p : Coloring.Parameter W) (x : Fin n → ℤ) : Prop :=
  ∃ a ∈ classList p x 0 1, ∃ b ∈ classList p x 1 1,
    ∃ c ∈ classList p x 2 (-1), a+b=c
end ThreeSum.ColorClassLists


