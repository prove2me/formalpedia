-- Prove2me | Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_SourceCountExecutionFactory
-- name    : WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_SourceCountExecutionFactory
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T11:26:59.339512+00:00
-- url     : https://prove2.me/theorems/a9347998-da17-4965-a092-bce3e8287285
-- title:
--   SourceCountExecutionFactory
-- statement:
--   Definitions and structural lemmas for SourceCountExecutionFactory, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/SourceCountExecutionFactory.lean

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_CountExecutionFactory
import Theorems.Thm_ThreeSum_LightTernaryBankAssembly_layout
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedBankAssembly_layout

set_option autoImplicit false
namespace WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
namespace ThreeSum.WeightedSourceCountExecutionFactory
open Light TernaryJointType
structure Setup (N : ℕ) where
  left : TernarySourceExecutionFactory.Setup
  right : TernarySourceExecutionFactory.Setup
  front : WeightedCountExecutionFactory.Setup N
def Setup.F {N : ℕ} (S : Setup N) (weight : ℕ→ℤ) : ℕ→TritWord N→ℤ :=
  S.left.values S.front.E.word weight
def Setup.G {N : ℕ} (S : Setup N) (weight : ℕ→ℤ) : ℕ→TritWord N→ℤ :=
  S.right.values S.front.E.word weight
def Setup.argv {N : ℕ} (S : Setup N) : List ℤ :=
  LightWeightedSourceCountHost.args S.left.argv S.right.argv S.front.argv
def Setup.program {N : ℕ} (S : Setup N) : Program :=
  LightWeightedSourceCountHost.program S.left.xs S.left.ys S.left.zs S.right.xs S.right.ys S.right.zs
def Setup.runtime {N : ℕ} (S : Setup N) : ℕ :=
  LightWeightedSourceCountHost.time S.left.runtime S.right.runtime S.front.runtime
structure Layout {N : ℕ} (S : Setup N) : Prop where
  leftBank : S.left.bank=S.front.f.nb
  rightBank : S.right.bank=S.front.f.nb
  leftGroups : S.left.groups=S.front.groups
  rightGroups : S.right.groups=S.front.groups
  leftValues : S.left.valueBase=S.front.fsource
  rightValues : S.right.valueBase=S.front.gsource
  leftBeforeRight : S.left.base0≤S.right.base0
  leftBeforeFront : S.left.base0≤S.front.keyBase
  leftValuesEnd : S.front.fsource+S.front.groups*S.front.f.nb≤S.right.base0
  rightInputBefore : S.right.src+S.right.NL≤S.left.base0
  rightWeightsBefore : S.right.weightBase+S.right.NL≤S.left.base0
  rightCodesBefore : S.right.a+S.right.bank≤S.left.base0
  rightPowersBefore : S.right.powers+(S.right.W+1)≤S.left.base0
  frontCodesBefore : S.front.f.bank+S.front.f.nb≤S.left.base0
  frontRecordsBefore : S.front.records+3*S.front.count≤S.left.base0
structure Ready {N : ℕ} (S : Setup N) (lim : Limits) (d : ℕ) (μ : ℕ→ℤ)
    (leftWeight rightWeight : ℕ→ℤ) : Prop where
  layout : Layout S
  left : TernarySourceExecutionFactory.Ready S.left lim (d+1) μ leftWeight S.front.E.word
  right : TernarySourceExecutionFactory.Ready S.right lim (d+1) μ rightWeight S.front.E.word
  front : WeightedCountExecutionFactory.Ready S.front lim (d+1) μ (S.F leftWeight) (S.G rightWeight)
  depth : d<lim.depth
end ThreeSum.WeightedSourceCountExecutionFactory
end
end WeightedCache3SUMRefinement_e1ae71d


