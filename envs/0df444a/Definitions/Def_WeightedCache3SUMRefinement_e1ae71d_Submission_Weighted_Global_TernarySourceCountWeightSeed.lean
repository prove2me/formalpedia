-- Prove2me | Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernarySourceCountWeightSeed
-- name    : WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernarySourceCountWeightSeed
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T11:32:57.97844+00:00
-- url     : https://prove2.me/theorems/1c67568a-4250-46e5-b8ab-8675f167cafa
-- title:
--   TernarySourceCountWeightSeed
-- statement:
--   Definitions and structural lemmas for TernarySourceCountWeightSeed, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernarySourceCountWeightSeed.lean

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_SourceCountExecutionFactory
import Definitions.Def_Submission_ThreeSum_TernarySourceWeightSeed
import Theorems.Thm_Light_MatAt_keep
import Theorems.Thm_Light_SegN_keep
import Theorems.Thm_Light_Seg_keep
import Theorems.Thm_Light_VecAt_keep
import Theorems.Thm_ThreeSum_LightTernaryBankAssembly_layout
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedBankAssembly_layout

set_option autoImplicit false
namespace WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
namespace ThreeSum.WeightedSourceCountExecutionFactory
open Light TernaryJointType
structure Seed {N : ℕ} (S : Setup N) (lim : Limits) (d boundary : ℕ) (μ : ℕ→ℤ)
    (leftWeight rightWeight : ℕ→ℤ) : Prop where
  layout : Layout S
  left : TernarySourceExecutionFactory.Seed S.left lim (d+1) μ leftWeight S.front.E.word
  right : TernarySourceExecutionFactory.Seed S.right lim (d+1) μ rightWeight S.front.E.word
  front : WeightedCountExecutionFactory.Ready S.front lim (d+1) μ (S.F leftWeight) (S.G rightWeight)
  leftInputBefore : S.left.src+S.left.NL≤boundary
  leftCodesBefore : S.left.a+S.left.bank≤boundary
  leftPowersBefore : S.left.powers+(S.left.W+1)≤boundary
  rightInputBefore : S.right.src+S.right.NL≤boundary
  rightCodesBefore : S.right.a+S.right.bank≤boundary
  rightPowersBefore : S.right.powers+(S.right.W+1)≤boundary
  frontCodesBefore : S.front.f.bank+S.front.f.nb≤boundary
  frontRecordsBefore : S.front.records+3*S.front.count≤boundary
  boundaryBefore : boundary≤S.left.base0
  depth : d<lim.depth
structure Immutable {N : ℕ} (S : Setup N) (keep : ℕ) : Prop where
  leftInput : S.left.src+S.left.NL≤keep
  leftCodes : S.left.a+S.left.bank≤keep
  leftPowers : S.left.powers+(S.left.W+1)≤keep
  rightInput : S.right.src+S.right.NL≤keep
  rightCodes : S.right.a+S.right.bank≤keep
  rightPowers : S.right.powers+(S.right.W+1)≤keep
  frontCodes : S.front.f.bank+S.front.f.nb≤keep
  frontRecords : S.front.records+3*S.front.count≤keep
end ThreeSum.WeightedSourceCountExecutionFactory
end
end WeightedCache3SUMRefinement_e1ae71d


