-- Prove2me | Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaPrefixState
-- name    : WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaPrefixState
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T17:56:46.305862+00:00
-- url     : https://prove2.me/theorems/afbfac92-661f-4e5a-a3e7-f051d361417f
-- title:
--   TernaryArenaPrefixState
-- statement:
--   Definitions and structural lemmas for TernaryArenaPrefixState, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryArenaPrefixState.lean

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaControllerPlan
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaPrefixCommit
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryPrefixStep
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaSelectedBudgets
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryPrefixInit
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryPrefixSeedHeader
import Theorems.Thm_Light_Ends_next
import Theorems.Thm_Light_LocalsBut_update
import Theorems.Thm_Light_SegN_read
import Theorems.Thm_ThreeSum_LightTernaryCountFrontend_row
import Theorems.Thm_ThreeSum_LightTernaryCountFrontend_rows
import Theorems.Thm_ThreeSum_LightTernaryEulerMemo_Ready_next
import Theorems.Thm_ThreeSum_LightTernaryEulerScan_Stored_next
import Theorems.Thm_ThreeSum_LightTernarySourceCountHost_Reads_update
import Theorems.Thm_ThreeSum_SourceBucketView_read
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedCountFrontend_row
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedCountFrontend_rows
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedSourceCountHost_Reads_update
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaScoreScan_initial
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaScoreScan_next
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaSourceCountSeed_seed
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaSourceSeed_seed
attribute [local simp] ThreeSum.LightTernaryCountFrontend.row
attribute [local simp] ThreeSum.LightTernaryCountFrontend.rows
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedCountFrontend.row
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedCountFrontend.rows


set_option autoImplicit false
namespace WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
namespace ThreeSum.WeightedGlobalArenaPrefixState
open Light WeightedGlobalArenaLayout WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate
open WeightedGlobalArenaSeedData WeightedGlobalArenaSelectedBudgets WeightedGlobalArenaBudgetExistence WeightedGlobalArenaFamilyBudget
open LightWeightedGlobalSeedScoreFactory LightWeightedGlobalControllerFactory
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 5000000
variable {p m F N : ℕ} [Fact p.Prime]
variable {E : Type*} [Field E] [Fintype E] [DecidableEq E] [Algebra (ZMod p) E]
structure Memory (I : Input) (A : Inputs) (L R O : ℕ→Fin (A.J+2)→ℤ)
    (j : ℕ) (s : State (p := p) A) (catalog : ℕ→ℕ→ℕ) (initial μ : ℕ→ℤ) : Prop where
  immutable : Kept initial μ I.free
  B : Reads μ (addr I.free I.capacity 4) I.nB
    (fun i => TernaryExtensionEncoding.coefficientCode (hash s.row j L i))
  Cvalues : Reads μ (addr I.free I.capacity 5) I.nC
    (fun i => TernaryExtensionEncoding.coefficientCode (hash s.row j R i))
  Ovalues : Reads μ (addr I.free I.capacity 6) I.requesterCount
    (fun i => TernaryExtensionEncoding.coefficientCode (hash s.row j O i))
  represents : TernaryStoredSpan.Represents catalog (p^j)
    (s.rows.map (TernaryPhysicalDigitSpan.reversal A.J))
  bounded : ∀k<p^j,∀i<A.J,catalog k i<p
  read : ∀k<p^j,∀i<A.J,μ (addr I.free I.capacity 7+A.J*k+i)=(catalog k i:ℤ)
def extend (A : Inputs) (ℓ : E→ₗ[ZMod p] ZMod p) (j : ℕ)
    (s : State (p := p) A) (seed : E×E) : State (p := p) A :=
  ⟨Function.update s.row j (TernaryOriginalRowMenu.row (A.J+2) ℓ seed),
    TernaryPhysicalDigitSpan.digitProjection A.J (TernaryOriginalRowMenu.seedRow (A.J+2) ℓ seed)::s.rows⟩
def nextCatalog (A : Inputs) (ℓ : E→ₗ[ZMod p] ZMod p) (j : ℕ)
    (catalog : ℕ→ℕ→ℕ) (seed : E×E) : ℕ→ℕ→ℕ :=
  TernaryStoredSpan.next catalog (LightStoredSpan.rowValues
    (TernaryPhysicalDigitSpan.physicalDigits (TernaryOriginalRowMenu.seedRow (A.J+2) ℓ seed))) p (p^j)
end ThreeSum.WeightedGlobalArenaPrefixState
end
end WeightedCache3SUMRefinement_e1ae71d


