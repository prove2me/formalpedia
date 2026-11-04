-- Prove2me | Definitions.Def_Submission_Weighted_Global_TernaryArenaPrefixPotential
-- name    : Submission_Weighted_Global_TernaryArenaPrefixPotential
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T18:16:37.509201+00:00
-- url     : https://prove2.me/theorems/bd6a2b72-b7e0-4d89-a64d-4ea370d6f0ad
-- title:
--   Ternary Arena Prefix Potential
-- statement:
--   Definitions and structural lemmas for Ternary Arena Prefix Potential, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaPrefixPotential.lean

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPrefixPairs
import Definitions.Def_Submission_ThreeSum_TernaryPairedMinorReindex
import Definitions.Def_Submission_Weighted_Global_TernaryNativeTensorScore
import Theorems.Thm_ThreeSum_LightTernaryCountFrontend_row
import Theorems.Thm_ThreeSum_LightWeightedCountFrontend_row
attribute [local simp] ThreeSum.LightTernaryCountFrontend.row
attribute [local simp] ThreeSum.LightWeightedCountFrontend.row


set_option autoImplicit false
noncomputable section
namespace ThreeSum.WeightedGlobalArenaPrefixPotential
open Finset TernaryJointType WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps TernaryCoverLocal
open WeightedGlobalArenaSourceSetup WeightedGlobalArenaPrefixGroups WeightedGlobalArenaPrefixPairs
open WeightedGlobalNativePrefixLineage TernaryPairedPotential TernaryPairedContraction
open scoped BigOperators
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 4000000
variable {p m F Λ : ℕ} [Fact p.Prime]
variable (maps : Fin F→Weight m p) (τ cap : ℕ) (I : Input) (L R : ℕ→Fin Λ→ℤ)
    (row : ℕ→(Fin Λ→ZMod p)→ₗ[ZMod p] ZMod p) (root : ℕ→ℕ→ZMod p)
    (Q : WeightedGlobalGoodOutputCatalog.Output m)
abbrev Index (r K : ℕ) := Σ j : Fin (S (r := r) maps τ cap I L R row root Q).front.count,
  Fin K→WeightedGlobalNativePairMoments.Pair (S (r := r) maps τ cap I L R row root Q) j.val
def equiv (r K : ℕ) : Index maps τ cap I L R row root Q r K≃
    (M maps τ cap I L R row root).Index r K :=
  Equiv.sigmaCongr (groupEquiv maps τ cap I L R row root r)
    (fun j => Equiv.piCongrRight (fun _ : Fin K => pairEquiv (maps := maps) (τ := τ) (cap := cap)
      (I := I) (L := L) (R := R) (row := row) (root := root) (Q := Q) j))
def matrix {r K : ℕ} (x : Index maps τ cap I L R row root Q r K) :
    Matrix (Fin (K+K)) (Fin Λ) ℤ := fun i =>
  Sum.elim (fun k => L (x.2 k).val.1.1) (fun k => R (x.2 k).val.2.1) (finSumFinEquiv.symm i)
def value (r K : ℕ) : ℕ := potential (matrix maps τ cap I L R row root Q (r := r) (K := K))
end ThreeSum.WeightedGlobalArenaPrefixPotential


