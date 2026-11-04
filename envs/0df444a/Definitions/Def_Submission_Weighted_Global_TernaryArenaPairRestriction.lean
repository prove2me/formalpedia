-- Prove2me | Definitions.Def_Submission_Weighted_Global_TernaryArenaPairRestriction
-- name    : Submission_Weighted_Global_TernaryArenaPairRestriction
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T15:49:36.757197+00:00
-- url     : https://prove2.me/theorems/cc634012-73cf-48ea-b362-d6adf219bc1f
-- title:
--   Ternary Arena Pair Restriction
-- statement:
--   Definitions and structural lemmas for Ternary Arena Pair Restriction, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaPairRestriction.lean

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSourceSetup
import Definitions.Def_Submission_Weighted_Global_TernaryNativeTensorScore
import Theorems.Thm_ThreeSum_TernarySourceHostModel_mem_records
import Theorems.Thm_ThreeSum_WeightedGlobalGoodOutputCatalog_mem_records
attribute [local simp] ThreeSum.TernarySourceHostModel.mem_records
attribute [local simp] ThreeSum.WeightedGlobalGoodOutputCatalog.mem_records


set_option autoImplicit false
noncomputable section
namespace ThreeSum.WeightedGlobalArenaPairRestriction
open Finset TernaryJointType WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps WeightedGlobalArenaSourceSetup
open WeightedGlobalNativePairMoments WeightedGlobalNativeTensorScore
open scoped BigOperators
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 3000000
variable {p m F r : ℕ} [Fact p.Prime]
def restrict (I : Input) (nB nC : ℕ) (fB fC : ℕ→ℕ) : Input :=
  {I with nB:=nB,nC:=nC,leftInput:=fun i => I.leftInput (fB i),rightInput:=fun i => I.rightInput (fC i)}
variable (maps : Fin F→Weight m p) (τ cap : ℕ) (Q : WeightedGlobalGoodOutputCatalog.Output m)
    (I : Input) (nB nC : ℕ) (fB fC : ℕ→ℕ)
    (hB : ∀ i<nB, fB i<I.nB) (hC : ∀ i<nC, fC i<I.nC)
abbrev full := setup (r := r) maps τ cap Q I
abbrev small := setup (r := r) maps τ cap Q (restrict I nB nC fB fC)
include hB hC
theorem source_mem (right : Bool) (a : ℕ×ℕ)
    (ha : a∈(source (r := r) maps cap (restrict I nB nC fB fC) right).records) :
    ((if right then fC a.1 else fB a.1),a.2)∈(source (r := r) maps cap I right).records := by
  have hv := (TernarySourceHostModel.mem_records _ _ _ _ _ _).mp ha
  apply (TernarySourceHostModel.mem_records _ _ _ _ _ _).mpr
  cases right
  · refine ⟨hB a.1 hv.1,hv.2.1,hv.2.2⟩
  · refine ⟨hC a.1 hv.1,hv.2.1,hv.2.2⟩
def embed {i : ℕ} (x : Pair (small (r := r) maps τ cap Q I nB nC fB fC) i) :
    Pair (full (r := r) maps τ cap Q I) i :=
  ⟨((fB x.val.1.1,x.val.1.2),(fC x.val.2.1,x.val.2.2)),by
    have hx := mem_filter.mp x.property
    have hl := mem_filter.mp (mem_product.mp hx.1).1
    have hr := mem_filter.mp (mem_product.mp hx.1).2
    apply mem_filter.mpr
    refine ⟨mem_product.mpr ⟨mem_filter.mpr ⟨source_mem maps cap I nB nC fB fC hB hC false _ hl.1,hl.2⟩,
      mem_filter.mpr ⟨source_mem maps cap I nB nC fB fC hB hC true _ hr.1,hr.2⟩⟩,hx.2⟩⟩
end ThreeSum.WeightedGlobalArenaPairRestriction


