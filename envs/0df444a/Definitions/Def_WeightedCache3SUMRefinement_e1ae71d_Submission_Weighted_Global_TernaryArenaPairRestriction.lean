-- Prove2me | Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaPairRestriction
-- name    : WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaPairRestriction
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T12:54:29.744551+00:00
-- url     : https://prove2.me/theorems/9c8d4a5a-1293-43bf-aba1-c2bce63370ca
-- title:
--   TernaryArenaPairRestriction
-- statement:
--   Definitions and structural lemmas for TernaryArenaPairRestriction, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryArenaPairRestriction.lean

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaSourceSetup
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryNativeTensorScore
import Theorems.Thm_ThreeSum_TernarySourceHostModel_mem_records
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalGoodOutputCatalog_mem_records
attribute [local simp] ThreeSum.TernarySourceHostModel.mem_records
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalGoodOutputCatalog.mem_records


set_option autoImplicit false
namespace WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
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
end
end WeightedCache3SUMRefinement_e1ae71d


