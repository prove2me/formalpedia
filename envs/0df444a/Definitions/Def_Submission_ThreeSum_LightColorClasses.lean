-- Prove2me | Definitions.Def_Submission_ThreeSum_LightColorClasses
-- name    : Submission_ThreeSum_LightColorClasses
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:37:14.486326+00:00
-- url     : https://prove2.me/theorems/0abc3c64-e1c0-4896-a5f8-06a37b43e345
-- title:
--   Light Color Classes
-- statement:
--   Definitions and structural lemmas for Light Color Classes, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightColorClasses.lean

import Definitions.Def_Submission_ThreeSum_LightColorArray
import Definitions.Def_Submission_ThreeSum_ColorClassLists
import Theorems.Thm_Light_Ends_call

set_option autoImplicit false
namespace ThreeSum.LightColorClasses
open Light ColorClassLists
set_option maxHeartbeats 1500000
set_option maxRecDepth 10000
def body (pColors pFilter : ℕ) : Stmt :=
  .call pColors [v 2,v 1,v 3,v 4,v 5,v 6,v 7,v 8,v 9,v 13] 14 ;;
  .call pFilter [v 0,v 9,v 10,v 1,k 0,k 1] 14 ;;
  .call pFilter [v 0,v 9,v 11,v 1,k 1,k 1] 14 ;;
  .call pFilter [v 0,v 9,v 12,v 1,k 2,k 0 -' k 1] 14
def time (W n : ℕ) : ℕ := LightColorArray.time W n+3*LightClassFilter.time n+200
structure Output {n W : ℕ} (p : Coloring.Parameter W) (x : Fin n → ℤ)
    (μ ν : ℕ → ℤ) (colors dst0 dst1 dst2 : ℕ) : Prop where
  colorValues : ∀ i < n, ν (colors+i) = (LightColorIndex.color p i : ℤ)
  header0 : ν dst0 = ((classList p x 0 1).length : ℤ)
  values0 : Seg ν (dst0+1) (classList p x 0 1)
  header1 : ν dst1 = ((classList p x 1 1).length : ℤ)
  values1 : Seg ν (dst1+1) (classList p x 1 1)
  header2 : ν dst2 = ((classList p x 2 (-1)).length : ℤ)
  values2 : Seg ν (dst2+1) (classList p x 2 (-1))
  kept : Kept μ ν colors
structure Procs (P : Program) (pMain : ℕ) where
  pColors : ℕ
  pPowers : ℕ
  pColor : ℕ
  pErase : ℕ
  pFilter : ℕ
  colors : P[pColors]? = some (LightColorArray.body pPowers pColor)
  powers : P[pPowers]? = some powTableBody
  color : P[pColor]? = some (LightColorIndex.body pErase)
  erase : P[pErase]? = some (LightMaskErase.body pErase)
  filter : P[pFilter]? = some LightClassFilter.body
  main : P[pMain]? = some (body pColors pFilter)
variable {lim : Limits} {P : Program} {d : ℕ}
def program : Program :=
  [body 1 5,LightColorArray.body 2 3,powTableBody,LightColorIndex.body 4,
    LightMaskErase.body 4,LightClassFilter.body]
def programProcs : Procs program 0 := ⟨1,2,3,4,5,rfl,rfl,rfl,rfl,rfl,rfl⟩
end ThreeSum.LightColorClasses


