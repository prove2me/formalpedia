-- Prove2me | Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaSourceSeed
-- name    : WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaSourceSeed
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T13:12:15.296552+00:00
-- url     : https://prove2.me/theorems/cf9fa49f-5cd3-4709-ad0c-905098a16ef1
-- title:
--   TernaryArenaSourceSeed
-- statement:
--   Definitions and structural lemmas for TernaryArenaSourceSeed, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryArenaSourceSeed.lean

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaSourceCertificate
import Definitions.Def_Submission_ThreeSum_TernarySourceWeightSeed
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaSourceLayout
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaSourceControls
import Theorems.Thm_ThreeSum_LightOriginalSurvivors_sorted
import Theorems.Thm_ThreeSum_TernaryNearCanonical_sorted
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedBankCanonical_sorted
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedNearCanonical_sorted

set_option autoImplicit false
namespace WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
namespace ThreeSum.WeightedGlobalArenaSourceSeed
open Light TernaryJointType WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps
open WeightedGlobalArenaSourceSetup TernaryCanonicalDictionaries LightTernarySourceHost
open WeightedGlobalNativeCompleteFrontend
variable {p m F r : ℕ} [Fact p.Prime]
set_option maxHeartbeats 3000000
structure Canonical (S : TernarySourceExecutionFactory.Setup)
    (E : ℕ→TritWord (N m r)) : Prop where
  xy : S.ys.length=S.xs.length
  xz : S.zs.length=S.xs.length
  native : ∀ x∈S.xs, |x|≤(S.U0 : ℤ)
  words : ∀ x∈S.ys, |x|≤(S.U1 : ℤ)
  maps : ∀ x∈S.zs, |x|≤(S.U2 : ℤ)
  codeBound : ∀i<S.bank, S.codes i<2^S.W
  sorted : ∀i k, i<k→k<S.bank→S.codes i<S.codes k
  wordCode : ∀j<size S.xs S.J, dictionary S.ys S.p1 S.J j=(S.codes (S.key j) : ℤ)
  key : ∀j<size S.xs S.J, S.key j<S.bank
  groupCode : ∀j<size S.xs S.J, dictionary S.zs S.p2 S.J j=(S.group j : ℤ)
  group : ∀j<size S.xs S.J, S.group j<S.groups
  injective : ∀i j, i<S.bank→j<S.bank→E i=E j→i=j
  factorial : ∀x∈S.records, (S.factor : ℤ)=TernaryConvolution.factorial (E (S.key x.2))
structure Memory (maps : Fin F→Weight m p) (cap : ℕ) (I : Input) (right : Bool)
    (lim : Limits) (μ : ℕ→ℤ) (weight : ℕ→ℤ) : Prop where
  nonempty : 0<(localRecords maps cap right).length
  sourceBefore : (source (r := r) maps cap I right).src+(source (r := r) maps cap I right).NL≤
    (source (r := r) maps cap I right).base0
  weightsBefore : (source (r := r) maps cap I right).weightBase+(source (r := r) maps cap I right).NL≤
    (source (r := r) maps cap I right).base0
  bankBefore : I.prefixFree+nb m r≤(source (r := r) maps cap I right).base0
  powersBefore : I.prefixFree+4^(N m r)+(2*N m r+1)≤(source (r := r) maps cap I right).base0
  groupSpace : F^r*nb m r+1≤lim.space
  bankSize : nb m r<2^(2*N m r)
  input : ∀i<(source (r := r) maps cap I right).NL,
    μ ((source (r := r) maps cap I right).src+i)=(source (r := r) maps cap I right).input i
  inputBound : ∀i<(source (r := r) maps cap I right).NL,
    |(source (r := r) maps cap I right).input i|≤(p*(p+1)^r : ℕ)
  weights : ∀i<(source (r := r) maps cap I right).NL, |weight i|≤(I.weightCap : ℤ)
  codes : Seg μ I.prefixFree ((bankCodes m r).map (fun c => (c : ℤ)))
  powers : LightSubsetAddress.Powers μ (I.prefixFree+4^(N m r)) (2*N m r)
end ThreeSum.WeightedGlobalArenaSourceSeed
end
end WeightedCache3SUMRefinement_e1ae71d


