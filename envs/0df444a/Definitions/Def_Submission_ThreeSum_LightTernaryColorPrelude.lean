-- Prove2me | Definitions.Def_Submission_ThreeSum_LightTernaryColorPrelude
-- name    : Submission_ThreeSum_LightTernaryColorPrelude
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T12:35:59.760001+00:00
-- url     : https://prove2.me/theorems/c50ee6e5-dbb0-4ead-b0c4-964910a49f46
-- title:
--   Light Ternary Color Prelude
-- statement:
--   Definitions and structural lemmas for Light Ternary Color Prelude, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryColorPrelude.lean

import Definitions.Def_Submission_ThreeSum_LightColorBands
import Definitions.Def_Submission_ThreeSum_LightColorParametersCosts
import Definitions.Def_Submission_ThreeSum_LightColorScanHost
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set
import Theorems.Thm_Light_Ends_store
import Theorems.Thm_ThreeSum_Karatsuba_CoeffBound_mem

set_option autoImplicit false
namespace ThreeSum.LightTernaryColorPrelude
open Light ColorClassLists LightColorParametersCosts
set_option maxHeartbeats 7000000
set_option maxRecDepth 20000
def class0 (free n : ℕ) := free+n
def class1 (free n : ℕ) := class0 free n+n+1
def class2 (free n : ℕ) := class1 free n+n+1
def av (free n : ℕ) := class2 free n+n+1
def ae (free n : ℕ) := av free n+n
def bv (free n : ℕ) := ae free n+2+2*n
def be (free n : ℕ) := bv free n+n
def cv (free n : ℕ) := be free n+2+2*n
def ce (free n : ℕ) := cv free n+n
def work (free n : ℕ) := ce free n+2+2*n
def body (pColor : ℕ) : Stmt :=
  .set 5 (M (v 2) +' k 1) ;;
  .set 6 (v 4 +' v 1) ;;
  .set 7 (v 6 +' v 1 +' k 1) ;;
  .set 8 (v 7 +' v 1 +' k 1) ;;
  .set 9 (v 8 +' v 1 +' k 1) ;;
  .set 10 (v 9 +' v 1) ;;
  .set 11 (v 10 +' k 2 +' k 2 *' v 1) ;;
  .set 12 (v 11 +' v 1) ;;
  .set 13 (v 12 +' k 2 +' k 2 *' v 1) ;;
  .set 14 (v 13 +' v 1) ;;
  .set 15 (v 14 +' k 2 +' k 2 *' v 1) ;;
  .call pColor [v 0,v 1,v 5,M (v 3),M (v 3 +' k 1),M (v 3 +' k 2),
    M (v 3 +' k 3),M (v 3 +' k 4),M (v 3 +' k 5),v 4,v 6,v 7,v 8,v 1,
    v 9,v 10,v 11,v 12,v 13,v 14,v 15] 16 ;;
  .set 17 (M (v 10)) ;;
  .set 18 (M (v 12)) ;;
  .set 19 (M (v 14)) ;;
  .store (v 4) (v 9) ;;
  .store (v 4 +' k 1) (v 17) ;;
  .store (v 4 +' k 2) (v 11) ;;
  .store (v 4 +' k 3) (v 18) ;;
  .store (v 4 +' k 4) (v 13) ;;
  .store (v 4 +' k 5) (v 19) ;;
  .store (v 4 +' k 6) (v 15) ;;
  .set 0 (v 4)
def time (n : ℕ) := LightColorBands.time (width n) n n+500
def word (n U : ℕ) := LightColorBands.word (width n) n n U+width n+100
def space (free n : ℕ) := LightColorBands.space (work free n) (width n) n n
def depth (n : ℕ) := LightColorBands.depth (width n) n n+1
def header (free n : ℕ) (A B C : List ℤ) : List ℤ :=
  [av free n,A.length,bv free n,B.length,cv free n,C.length,work free n]
structure Normalized (μ : ℕ→ ℤ) (base n : ℕ) (original L : List ℤ) : Prop where
  seg : Seg μ base L
  sorted : L.Pairwise (· < ·)
  length : L.length≤ n
  mem : ∀ z, z∈L↔z∈original
def Output {n : ℕ} (μ ν : ℕ→ ℤ) (free : ℕ) (p : Coloring.Parameter (width n))
    (x : Fin n→ ℤ) (r : ℤ) : Prop :=
  r=(free:ℤ) ∧ Kept μ ν free ∧ ∃ A B C : List ℤ,
    Seg ν free (header free n A B C) ∧
    Normalized ν (av free n) n (classList p x 0 1) A ∧
    Normalized ν (bv free n) n (classList p x 1 1) B ∧
    Normalized ν (cv free n) n (classList p x 2 (-1)) C
variable {lim : Limits} {P : Program}
def program : Program := LightColorBands.program++[body 20]
def library : LightColorBands.Procs program 20 where
  pClasses:= 21
  pBands:= 0
  classes:= ⟨22,23,24,25,26,rfl,rfl,rfl,rfl,rfl,rfl⟩
  bands:= {
    pPrepare:= 1
    pEnumerate:= 12
    prepare:= ⟨2,8,9,10,11,⟨3,4,5,6,7,⟨rfl,rfl,rfl,rfl⟩,rfl,rfl⟩,rfl,rfl,rfl,rfl,rfl⟩
    enumerate:= ⟨13,⟨14,15,16,17,18,19,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩,rfl⟩
    main:= rfl }
  main:= rfl
def witness (A B C : List ℤ) : Prop :=∃ a∈A, ∃ b∈B, ∃ c∈C, c-b=a
end ThreeSum.LightTernaryColorPrelude


