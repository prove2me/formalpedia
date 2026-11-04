-- Prove2me | Definitions.Def_Submission_ThreeSum_LightColorBands
-- name    : Submission_ThreeSum_LightColorBands
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:51:18.978871+00:00
-- url     : https://prove2.me/theorems/76b1edfa-136d-4e64-830e-344be0134685
-- title:
--   Light Color Bands
-- statement:
--   Definitions and structural lemmas for Light Color Bands, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightColorBands.lean

import Definitions.Def_Submission_ThreeSum_LightColorClasses
import Definitions.Def_Submission_ThreeSum_ColorBandBounds
import Theorems.Thm_Light_Ends_call

set_option autoImplicit false
namespace ThreeSum.LightColorBands
open Light ColorClassLists
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
def body (pClasses pBands : ℕ) : Stmt :=
  .call pClasses [v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 7,v 8,v 9,v 10,v 11,v 12,v 20] 21 ;;
  .call pBands [v 10 +' k 1,M (v 10),v 11 +' k 1,M (v 11),
    v 12 +' k 1,M (v 12),v 13,v 14,v 15,v 16,v 17,v 18,v 19,v 20] 0
def time (W n g : ℕ) : ℕ := LightColorClasses.time W n+ColorBandBounds.time n g+300
def space (work W n g : ℕ) : ℕ := ColorBandBounds.space work n g+W+1
def word (W n g U : ℕ) : ℕ := 2^(W+1)+ColorBandBounds.word n g U+U
def depth (W n g : ℕ) : ℕ := W+ColorBandBounds.depth n g+5
structure Procs (P : Program) (pMain : ℕ) where
  pClasses : ℕ
  pBands : ℕ
  classes : LightColorClasses.Procs P pClasses
  bands : LightBandPreprocessing.Procs P pBands
  main : P[pMain]? = some (body pClasses pBands)
variable {lim : Limits} {P : Program} {d : ℕ}
def program : Program := LightBandPreprocessing.program ++
  [body 21 0,LightColorClasses.body 22 26,LightColorArray.body 23 24,powTableBody,
    LightColorIndex.body 25,LightMaskErase.body 25,LightClassFilter.body]
def programProcs : Procs program 20 where
  pClasses := 21
  pBands := 0
  classes := ⟨22,23,24,25,26,rfl,rfl,rfl,rfl,rfl,rfl⟩
  bands := {
    pPrepare := 1
    pEnumerate := 12
    prepare := ⟨2,8,9,10,11,⟨3,4,5,6,7,⟨rfl,rfl,rfl,rfl⟩,rfl,rfl⟩,rfl,rfl,rfl,rfl,rfl⟩
    enumerate := ⟨13,⟨14,15,16,17,18,19,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩,rfl⟩
    main := rfl }
  main := rfl
end ThreeSum.LightColorBands


