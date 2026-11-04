-- Prove2me | Definitions.Def_Submission_ThreeSum_LightSourceStages
-- name    : Submission_ThreeSum_LightSourceStages
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:43:57.725878+00:00
-- url     : https://prove2.me/theorems/ecbe393b-0216-4a3f-8e74-24aff4b86bf7
-- title:
--   Light Source Stages
-- statement:
--   Definitions and structural lemmas for Light Source Stages, from the weighted-cache deterministic 3SUM development.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSourceStages.lean

import Definitions.Def_Submission_ThreeSum_LightSourceBuild
import Definitions.Def_Submission_ThreeSum_SourceTableLayout
import Definitions.Def_Submission_ThreeSum_LightZetaStages
import Theorems.Thm_Light_Ends_call
import Definitions.Def_WeightedCache3SUM_Alias_231e42e414403f8e

set_option autoImplicit false
namespace ThreeSum.LightSourceStages
open Light SubsetAddress LightSubsetAddress LightPascal LightZetaCell
set_option maxHeartbeats 2200000
set_option maxRecDepth 12000
structure ZetaProcs (P : Program) (pMain : ℕ) where
  pSize : ℕ
  pPass : ℕ
  pEnumSetup : ℕ
  pEnum : ℕ
  pBatch : ℕ
  pCell : ℕ
  pSetup : ℕ
  pBuild : ℕ
  pFill : ℕ
  pRow : ℕ
  pLinear : ℕ
  pPowers : ℕ
  pRank : ℕ
  pOffset : ℕ
  pErase : ℕ
  main : P[pMain]? = some (LightZetaStages.body pSize pPass)
  size : P[pSize]? = some (LightDownsetSize.body pSetup pOffset)
  pass : P[pPass]? = some (LightZetaPass.body pEnumSetup pBatch)
  enumSetup : P[pEnumSetup]? = some (LightSubsetEnumerationSetup.body pPowers pEnum)
  enumeration : P[pEnum]? = some (LightSubsetEnumeration.body pEnum)
  batch : P[pBatch]? = some (LightZetaBatch.body pCell)
  cell : P[pCell]? = some (LightZetaCell.body pSetup pOffset pErase pRank)
  setup : LightSubsetSetup.Procs P pSetup pBuild pFill pRow pLinear pPowers pRank
  offset : P[pOffset]? = some LightSubsetOffset.body
  erase : P[pErase]? = some (LightMaskErase.body pErase)
variable {lim : Limits} {P : Program} {d : ℕ}
def source {L : ℕ} (μ : ℕ → ℤ) (src N p m : ℕ) (shift : ℤ)
    (endpoint : Finset (Fin L) → ℤ) (flag : Finset (Fin L) → ℕ)
    (S : Finset (Fin L)) : ℤ :=
  ((if flag S = 1 then
    LightHistogram.count (fun j => LightSourceResidues.key p m shift (μ (src+j)))
      (LightResidues.residue m 1 (endpoint S)) N else 0 : ℕ) : ℤ)
def body (pSource pZeta : ℕ) : Stmt :=
  .call pSource [v 0,v 1,v 2,v 3,v 14,v 4,v 5,v 6,v 7,v 8,v 9,v 10] 15 ;;
  .call pZeta [v 11,v 12,v 7,v 13,v 9] 15
def time (N L cut p m U D E : ℕ) : ℕ :=
  LightSourceBuild.time N (downsetCap L cut) p m U D E+LightZetaStages.time L cut+100
def space (work L p U D E : ℕ) : ℕ :=
  max (LightSourceBuild.space work p U D E) (work+tableSize L+(L+1))
def word (N L p m U D E : ℕ) : ℕ :=
  LightSourceBuild.word p m U D E+(L+1)*2^(L+1)+2^L*N
structure Procs (P : Program) (pMain : ℕ) where
  pSource : ℕ
  pZeta : ℕ
  sourceProcs : LightSourceBuild.Procs P pSource
  zeta : ZetaProcs P pZeta
  main : P[pMain]? = some (body pSource pZeta)
def program : Program :=
  [body 1 8,LightSourceBuild.body 2 7,LightSourceHistogram.body 3 5,LightSourceResidues.body 4,
    emodBody,LightHistogram.histogramBody 6,fillBody,LightSourceGather.body 4,
    LightZetaStages.body 9 10,LightDownsetSize.body 14 21,LightZetaPass.body 11 12,
    LightSubsetEnumerationSetup.body 19 23,LightZetaBatch.body 13,
    LightZetaCell.body 14 21 22 20,LightSubsetSetup.body 15 19 20,
    buildBody 16 17,fillBody,rowBody 18,LightArray.linearBody,powTableBody,
    rankBody 20,LightSubsetOffset.body,LightMaskErase.body 22,LightSubsetEnumeration.body 23]
def programProcs : Procs program 0 :=
  ⟨1,8,⟨2,7,⟨3,4,5,6,rfl,rfl,rfl,rfl,rfl⟩,rfl,rfl⟩,
    ⟨9,10,11,23,12,13,14,15,16,17,18,19,20,21,22,
      rfl,rfl,rfl,rfl,rfl,rfl,rfl,⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩,rfl,rfl⟩,rfl⟩
end ThreeSum.LightSourceStages


