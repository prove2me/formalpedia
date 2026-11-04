-- Prove2me | Definitions.Def_Submission_ThreeSum_ReportingHostPrefixCatalog
-- name    : Submission_ThreeSum_ReportingHostPrefixCatalog
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T11:36:28.309788+00:00
-- url     : https://prove2.me/theorems/d547090a-be5a-4811-b15f-356245ade91e
-- title:
--   Reporting Host Prefix Catalog
-- statement:
--   Definitions and structural lemmas for Reporting Host Prefix Catalog, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostPrefixCatalog.lean

import Definitions.Def_Submission_ThreeSum_LightReportingSuffixBoxes
import Definitions.Def_Submission_ThreeSum_LocalGraph
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
attribute [local simp] ThreeSum.LayerCounts.mem_edgeSet
attribute [local simp] ThreeSum.LayerCounts.mem_vertices


set_option autoImplicit false
namespace ThreeSum.ReportingHostPrefixCatalog
open Finset LocalGraph LayerCounts BlockRows BlockIndex BlockIndexedQuery
open BlockEncoding BlockForced GlobalEncoding StoredReporting ReportingHostSuffix
set_option linter.unusedSectionVars false
abbrev Prefix (h k : ℕ) := Fin k → Edge (512*h) h
def leftRows {h J k : ℕ} (p : Prefix h k) : Fin J → Finset (Fin (512*h)) :=
  fun i => if hi : i.val < k then (p ⟨i.val,hi⟩).val.1 else ∅
def rightRows {h J k : ℕ} (p : Prefix h k) : Fin J → Finset (Fin (512*h)) :=
  fun i => if hi : i.val < k then (p ⟨i.val,hi⟩).val.2 else ∅
def leftSet {h J k : ℕ} (p : Prefix h k) : Finset (Fin (J*(512*h))) :=
  leftPrefix k (leftRows p)
def rightSet {h J k : ℕ} (p : Prefix h k) : Finset (Fin (J*(512*h))) :=
  leftPrefix k (rightRows p)
def ofValidPrefix {h J k : ℕ} (hk : k ≤ J) (q : GlobalOutput h J)
    (pre : List (Finset (Fin (512*h)))) (hp : ValidPrefix q k pre) : Prefix h k :=
  fun i =>
    let j : Fin J := ⟨i.val,i.isLt.trans_le hk⟩
    ⟨(prefixRows pre j,outputRows q j \ prefixRows pre j),by
      have hu := hp.2 j i.isLt
      have hQ : (outputRows q j).card = 2*h := LayerCounts.mem_vertices.mp (q j).2.property
      apply LayerCounts.mem_edgeSet.mpr
      refine ⟨hu.2,?_,disjoint_sdiff_self_right⟩
      rw [Finset.card_sdiff_of_subset hu.1,hQ,hu.2]
      omega⟩
section Sources
variable {β γ : Type*} [Fintype β] [Fintype γ] [DecidableEq β] [DecidableEq γ]
def leftSourceOf {h J : ℕ} (o : Occurrences h J) (P : ℤ) (B : Finset β) (b : β → ℤ) :
    Finset (Fin (J*(512*h))) → ℤ :=
  SubsetTransport.reindex (coordEquiv J (512*h)) (fun S => (leftWeights o P B b S : ℤ))
def rightSourceOf {h J : ℕ} (o : Occurrences h J) (P shift : ℤ) (C : Finset γ) (c : γ → ℤ) :
    Finset (Fin (J*(512*h))) → ℤ :=
  SubsetTransport.reindex (coordEquiv J (512*h)) (fun S => (rightWeights o P shift C c S : ℤ))
def leaf {h J k : ℕ} (hk : k ≤ J) (o : Occurrences h J)
    (P shift : ℤ) (B : Finset β) (C : Finset γ) (b : β → ℤ) (c : γ → ℤ) (p : Prefix h k) :
    Finset (Fin ((J-k)*(512*h))) → ℤ :=
  leafWeight (block_fit hk) (leftSourceOf o P B b) (rightSourceOf o P shift C c)
    (suffixStage J (512*h) k) (leftSet p) (rightSet p)
end Sources
end ThreeSum.ReportingHostPrefixCatalog


