-- Prove2me | Definitions.Def_Submission_ThreeSum_LightClassFilter
-- name    : Submission_ThreeSum_LightClassFilter
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:20:09.874251+00:00
-- url     : https://prove2.me/theorems/f4319fe8-7fe8-4b2d-b67f-9188106c7d9d
-- title:
--   Light Class Filter
-- statement:
--   Definitions and structural lemmas for Light Class Filter, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightClassFilter.lean

import Definitions.Def_Submission_ThreeSum_LightArray
import Theorems.Thm_Light_Ends_set
import Theorems.Thm_Light_Ends_skip
import Theorems.Thm_Light_Ends_store

set_option autoImplicit false
namespace ThreeSum.LightClassFilter
open Light
set_option maxHeartbeats 1200000
def items (x : ℕ → ℤ) (color : ℕ → ℕ) (want : ℕ) (scale : ℤ) (n : ℕ) : List ℤ :=
  ((List.range n).filter fun i => decide (color i = want)).map fun i => scale*x i
def roundBody : Stmt :=
  .ite (M (v 1 +' v 7) =' v 4)
    (.store (v 2 +' k 1 +' v 6) (v 5 *' M (v 0 +' v 7)) ;;
      .set 6 (v 6 +' k 1)) .skip
def body : Stmt :=
  .set 6 (k 0) ;;
  .for 7 (v 3) roundBody ;;
  .store (v 2) (v 6) ;;
  .set 0 (v 6)
def time (n : ℕ) : ℕ := 100*n+100
def Inv (μ : ℕ → ℤ) (x : ℕ → ℤ) (color : ℕ → ℕ)
    (src colors dst n want : ℕ) (scale : ℤ) (j : ℕ) (σ : State) : Prop :=
  ∃ ν : ℕ → ℤ,
    σ = ⟨frame [src,colors,dst,n,want,scale,(items x color want scale j).length,j],ν⟩ ∧
    Seg ν (dst+1) (items x color want scale j) ∧ SameOutside μ ν dst (n+1)
variable {lim : Limits} {P : Program} {d : ℕ}
def program : Program := [body]
end ThreeSum.LightClassFilter


