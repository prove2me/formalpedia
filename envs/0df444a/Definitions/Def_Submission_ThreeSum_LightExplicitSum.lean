-- Prove2me | Definitions.Def_Submission_ThreeSum_LightExplicitSum
-- name    : Submission_ThreeSum_LightExplicitSum
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T09:18:42.77106+00:00
-- url     : https://prove2.me/theorems/20052890-9f2f-48e3-9d97-5852f016a83c
-- title:
--   Light Explicit Sum
-- statement:
--   Definitions and structural lemmas for Light Explicit Sum, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightExplicitSum.lean

import Definitions.Def_Submission_ThreeSum_ExplicitLayers
import Definitions.Def_Submission_ThreeSum_LightLeafSum
import Definitions.Def_Submission_ThreeSum_LightQueryEnumeration
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set
import Theorems.Thm_ThreeSum_LightBoxStages_program_procs
import Theorems.Thm_ThreeSum_LightDownsetAddress_program_procs
import Theorems.Thm_ThreeSum_LightDownsetSize_program_procs
import Theorems.Thm_ThreeSum_LightLeafSum_program_procs
import Theorems.Thm_ThreeSum_LightSignedLeaf_program_procs
import Theorems.Thm_ThreeSum_LightStageLookup_program_procs
import Theorems.Thm_ThreeSum_LightSubsetSetup_program_procs
import Theorems.Thm_ThreeSum_LightZetaCell_program_procs
import Theorems.Thm_ThreeSum_LightZetaPass_program_procs
import Theorems.Thm_ThreeSum_LightZetaStages_program_procs

set_option autoImplicit false
namespace ThreeSum.LightExplicitSum
open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress
open QueryCoordinates
variable {lim : Limits} {P : Program}
structure Procs (P : Program) (pEnum pSum : ℕ) where
  pWeights : ℕ
  pPowers : ℕ
  pErase : ℕ
  pCore : ℕ
  pLeaf : ℕ
  pLookup : ℕ
  pSign : ℕ
  pSize : ℕ
  pAddress : ℕ
  pSetup : ℕ
  pBuild : ℕ
  pFill : ℕ
  pRow : ℕ
  pLinear : ℕ
  pRank : ℕ
  pOffset : ℕ
  enumerate : P[pEnum]? = some (LightQueryEnumeration.body pWeights pCore)
  weights : P[pWeights]? = some (LightQueryWeights.body pPowers pErase)
  erase : P[pErase]? = some (LightMaskErase.body pErase)
  core : P[pCore]? = some (LightSubsetEnumeration.body pCore)
  sum : P[pSum]? = some (LightLeafSum.body pLeaf)
  leaf : P[pLeaf]? = some (LightSignedLeaf.body pLookup pSign)
  lookup : P[pLookup]? = some (LightStageLookup.body pSize pAddress)
  sign : P[pSign]? = some LightSign.body
  size : P[pSize]? = some (LightDownsetSize.body pSetup pOffset)
  address : P[pAddress]? = some (LightDownsetAddress.body pSetup pOffset)
  table : LightSubsetSetup.Procs P pSetup pBuild pFill pRow pLinear pPowers pRank
  offset : P[pOffset]? = some LightSubsetOffset.body
def roundBody (pEnum pSum : ℕ) : Stmt :=
  .call pEnum [v 0,v 8,v 15,v 12,v 13] 16 ;;
  .call pSum [v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 7,v 8,v 15,v 16,v 12,v 10,v 11,v 13] 17 ;;
  .set 14 (v 14 +' v 17)
def body (pEnum pSum : ℕ) : Stmt :=
  .set 14 (k 0) ;;
  .for 15 (v 9) (roundBody pEnum pSum) ;;
  .set 0 (v 14)
def roundTime (W c t : ℕ) : ℕ := 8000*(W+1)^2*(layerOffset c t+1)
def time (W c t : ℕ) : ℕ := t*(roundTime W c t+30)+40
def Inv {W : ℕ} (μ : ℕ → ℤ) (Q preL preR : Finset (Fin W))
    (f g : Finset (Fin W) → ℤ) (stage cut t baseL baseR maskBase work j : ℕ) (σ : State) : Prop :=
  ∃ (count r : ℤ) (μ' : ℕ → ℤ),
    σ = ⟨frame [W,cut,stage,preL.card,subsetMask preL,preR.card,subsetMask preR,
      Q.card,subsetMask Q,t,baseL,baseR,maskBase,work,
      ExplicitLayers.valueSum Q (SignedLeaf.value f g stage preL preR) j,j,count,r],μ'⟩ ∧
      KeptBut μ μ' work maskBase (layerOffset Q.card t)
def program : Program :=
  [body 1 4,LightQueryEnumeration.body 2 3,LightQueryWeights.body 14 17,
    LightSubsetEnumeration.body 3,LightLeafSum.body 5,LightSignedLeaf.body 6 18,
    LightStageLookup.body 7 8,LightDownsetSize.body 9 16,LightDownsetAddress.body 9 16,
    LightSubsetSetup.body 10 14 15,buildBody 11 12,fillBody,rowBody 13,LightArray.linearBody,
    powTableBody,rankBody 15,LightSubsetOffset.body,LightMaskErase.body 17,LightSign.body]
def program_procs : Procs program 1 4 where
  pWeights := 2
  pPowers := 14
  pErase := 17
  pCore := 3
  pLeaf := 5
  pLookup := 6
  pSign := 18
  pSize := 7
  pAddress := 8
  pSetup := 9
  pBuild := 10
  pFill := 11
  pRow := 12
  pLinear := 13
  pRank := 15
  pOffset := 16
  enumerate := rfl
  weights := rfl
  erase := rfl
  core := rfl
  sum := rfl
  leaf := rfl
  lookup := rfl
  sign := rfl
  size := rfl
  address := rfl
  table := ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
  offset := rfl
end ThreeSum.LightExplicitSum


