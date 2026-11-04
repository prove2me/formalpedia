-- Prove2me | Definitions.Def_Submission_ThreeSum_LightHashHistogram
-- name    : Submission_ThreeSum_LightHashHistogram
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:33:38.824187+00:00
-- url     : https://prove2.me/theorems/be63c09f-5526-447e-a6aa-517ac2bfe34d
-- title:
--   Light Hash Histogram
-- statement:
--   Definitions and structural lemmas for Light Hash Histogram, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightHashHistogram.lean

import Definitions.Def_Submission_ThreeSum_LightMaskHashes
import Definitions.Def_Submission_ThreeSum_LightResidues
import Definitions.Def_Submission_ThreeSum_LightHistogram
import Theorems.Thm_Light_Ends_call

set_option autoImplicit false
namespace ThreeSum.LightHashHistogram
open Light
def code (L p : ℕ) (mask w0 w1 : ℕ → ℕ) (i : ℕ) : ℕ :=
  LightResidues.residue p 1 (OneHotMask.eval w0 w1 L (mask i) : ℤ)
def body (pHashes pResidues pHist : ℕ) : Stmt :=
  .call pHashes [v 0,v 1,v 2,v 5,v 6,v 7,v 9] 10 ;;
  .call pResidues [v 2,v 3,v 5,v 8,v 9,k 1] 10 ;;
  .call pHist [v 3,v 4,v 5,v 8] 10
def time (L n p U : ℕ) : ℕ := LightMaskHashes.time L n+
  LightResidues.residuesTime n (L*U)+LightHistogram.histogramTime n p+100
def word (L p U : ℕ) : ℕ := LightOneHot.word L U+4*(L*U)+4*p+16
def space (work L U : ℕ) : ℕ := work+max (L+1) (Nat.log 2 (L*U+1)+2)
structure Procs (P : Program) (pMain : ℕ) where
  pHashes : ℕ
  pPowers : ℕ
  pOneHot : ℕ
  pResidues : ℕ
  pEmod : ℕ
  pHist : ℕ
  pFill : ℕ
  hashes : P[pHashes]? = some (LightMaskHashes.body pPowers pOneHot)
  powers : P[pPowers]? = some powTableBody
  onehot : P[pOneHot]? = some (LightOneHot.body pOneHot)
  residues : P[pResidues]? = some (LightResidues.residuesBody pEmod)
  emod : P[pEmod]? = some emodBody
  hist : P[pHist]? = some (LightHistogram.histogramBody pFill)
  fill : P[pFill]? = some fillBody
  main : P[pMain]? = some (body pHashes pResidues pHist)
variable {lim : Limits} {P : Program} {d : ℕ}
def program : Program :=
  [body 1 4 6,LightMaskHashes.body 2 3,powTableBody,LightOneHot.body 3,
    LightResidues.residuesBody 5,emodBody,LightHistogram.histogramBody 7,fillBody]
def programProcs : Procs program 0 := ⟨1,2,3,4,5,6,7,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
end ThreeSum.LightHashHistogram


