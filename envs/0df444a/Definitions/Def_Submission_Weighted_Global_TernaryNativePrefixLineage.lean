-- Prove2me | Definitions.Def_Submission_Weighted_Global_TernaryNativePrefixLineage
-- name    : Submission_Weighted_Global_TernaryNativePrefixLineage
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T15:02:41.477658+00:00
-- url     : https://prove2.me/theorems/e8bda003-57bf-4ae9-9e80-7aab38b129de
-- title:
--   Ternary Native Prefix Lineage
-- statement:
--   Definitions and structural lemmas for Ternary Native Prefix Lineage, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryNativePrefixLineage.lean

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryNativePairedLineage
import Theorems.Thm_ThreeSum_LightTernaryCountFrontend_row
import Theorems.Thm_ThreeSum_LightWeightedCountFrontend_row
attribute [local simp] ThreeSum.LightTernaryCountFrontend.row
attribute [local simp] ThreeSum.LightWeightedCountFrontend.row


set_option autoImplicit false
noncomputable section
namespace ThreeSum.WeightedGlobalNativePrefixLineage
open Finset TernaryJointType TernaryCoverLocal TernaryCoverOutputCap
open TernaryOriginalRowMenu TernaryPairedPotential TernaryPairedContraction
open scoped BigOperators
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 3000000
variable {p Λ L F : ℕ} [Fact p.Prime] {α π : DigitType}
variable {O B C : Type*} [Fintype O] [Fintype B] [Fintype C]
abbrev Out (L F : ℕ) (π : DigitType) := Fin F×{q // q∈vertices L π}
structure Model (p Λ L F : ℕ) [Fact p.Prime] (α π : DigitType) (O B C : Type*) where
  maps : Fin F→TernaryCoverHashes.Coordinate (Fin L)→ZMod p
  originalLeft : B→Fin Λ→ℤ
  originalRight : C→Fin Λ→ℤ
  row : ℕ→(Fin Λ→ZMod p)→ₗ[ZMod p] ZMod p
  root : O→ℕ→ZMod p
  good : Fin F→Prop
  keepLeft : Fin F→TritWord L→Prop
  keepRight : Fin F→TritWord L→Prop
namespace Model
variable (M : Model p Λ L F α π O B C)
def Group (r : ℕ) := {g : O×(Fin r→Out L F π) // ∀ j,
  M.good (g.2 j).1 ∧ outputHash (M.maps (g.2 j).1) (g.2 j).2.val=M.root g.1 j.val}
instance groupFinite (r : ℕ) : Fintype (M.Group r) := by
  classical
  unfold Group
  infer_instance
def Pair {r : ℕ} (g : M.Group r) := {x : (B×C)×(Fin r→LocalEdge L α π) // ∀ j,
  output (x.2 j)=(g.val.2 j).2.val ∧
  M.row j.val (fun a => (M.originalLeft x.1.1 a : ZMod p))=leftHash (M.maps (g.val.2 j).1) (x.2 j) ∧
  M.row j.val (fun a => (M.originalRight x.1.2 a : ZMod p))=rightHash (M.maps (g.val.2 j).1) (x.2 j) ∧
  M.keepLeft (g.val.2 j).1 (left (x.2 j)) ∧ M.keepRight (g.val.2 j).1 (right (x.2 j))}
instance pairFinite {r : ℕ} (g : M.Group r) : Fintype (M.Pair g) := by
  classical
  unfold Pair
  infer_instance
abbrev Index (r K : ℕ) := Σ g : M.Group r, Fin K→M.Pair g
def parentGroup {r : ℕ} (g : M.Group (r+1)) : M.Group r :=
  ⟨(g.val.1,fun j => g.val.2 j.castSucc),fun j => g.property j.castSucc⟩
def parentPair {r : ℕ} {g : M.Group (r+1)} (x : M.Pair g) : M.Pair (M.parentGroup g) :=
  ⟨(x.val.1,fun j => x.val.2 j.castSucc),fun j => x.property j.castSucc⟩
def parent {r K : ℕ} (x : M.Index (r+1) K) : M.Index r K :=
  ⟨M.parentGroup x.1,fun i => M.parentPair (x.2 i)⟩
def child {r K : ℕ} (x : M.Index (r+1) K) : Child L K F α π :=
  ((x.1.val.2 (Fin.last r)).1,
    ⟨(x.1.val.2 (Fin.last r)).2,fun i => ⟨(x.2 i).val.2 (Fin.last r),((x.2 i).property (Fin.last r)).1⟩⟩)
def lineage {r K : ℕ} (x : M.Index (r+1) K) : M.Index r K×Child L K F α π :=
  (M.parent x,M.child x)
def matrix {r K : ℕ} (x : M.Index r K) : Matrix (Fin (K+K)) (Fin Λ) ℤ :=
  fun i => Sum.elim (fun j => M.originalLeft (x.2 j).val.1.1)
    (fun j => M.originalRight (x.2 j).val.1.2) (finSumFinEquiv.symm i)
end Model
end ThreeSum.WeightedGlobalNativePrefixLineage


