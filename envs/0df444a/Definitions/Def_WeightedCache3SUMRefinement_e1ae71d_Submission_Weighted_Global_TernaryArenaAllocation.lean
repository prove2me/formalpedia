-- Prove2me | Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaAllocation
-- name    : WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaAllocation
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T14:22:33.59879+00:00
-- url     : https://prove2.me/theorems/a2d9c420-9265-48ad-884d-8032f1d752c3
-- title:
--   TernaryArenaAllocation
-- statement:
--   Definitions and structural lemmas for TernaryArenaAllocation, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryArenaAllocation.lean

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaPrefixFootprints
import Theorems.Thm_ThreeSum_LightKaratsuba_ProductAt_bound
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaPrefixFootprints_fixed_capacity_all

set_option autoImplicit false
namespace WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
namespace ThreeSum.WeightedGlobalArenaAllocation
open WeightedGlobalArenaPrefixFootprints WeightedGlobalArenaLayout
open WeightedGlobalCoverGoodMaps
variable {p m F : ℕ} [Fact p.Prime]
structure Allocation (maps : Fin F→Weight m p) (τ cap M b K H drift scale : ℕ) where
  D : ℕ
  E : ℕ
  exponentPositive : 1≤E
  exponentConstant : E≤D
  bound : ∀ n U j, j≤Nat.clog M (n^2) →
    envelope maps τ cap M b K H drift scale n U j≤capacity D E (n+U)
def allocation (maps : Fin F→Weight m p) (τ cap M b K H drift scale : ℕ)
    (hM : 1<M) (hb : 1<b) : Allocation maps τ cap M b K H drift scale := by
  let hex := fixed_capacity_all maps τ cap K H drift scale hM hb
  let D := Classical.choose hex
  have hD := Classical.choose_spec hex
  let E := Classical.choose hD
  have hE := Classical.choose_spec hD
  refine ⟨D+E+1,E+1,by omega,by omega,fun n U j hj=>?_⟩
  have hOld : envelope maps τ cap M b K H drift scale n U j≤capacity D E (n+U) := hE n U j hj
  apply hOld.trans
  change 256*(D+1)*(n+U+1)^E≤256*(D+E+1+1)*(n+U+1)^(E+1)
  exact Nat.mul_le_mul (Nat.mul_le_mul_left 256 (by omega : D+1≤D+E+1+1))
    (Nat.pow_le_pow_right (by omega : 1≤n+U+1) (by omega : E≤E+1))
end ThreeSum.WeightedGlobalArenaAllocation
end
end WeightedCache3SUMRefinement_e1ae71d


