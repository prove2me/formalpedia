-- Prove2me | Definitions.Def_Submission_Weighted_Global_TernaryArenaSeedData
-- name    : Submission_Weighted_Global_TernaryArenaSeedData
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T21:11:01.616199+00:00
-- url     : https://prove2.me/theorems/640ef5c7-0ea1-4210-b037-f1649b140a95
-- title:
--   Ternary Arena Seed Data
-- statement:
--   Definitions and structural lemmas for Ternary Arena Seed Data, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaSeedData.lean

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSeedCandidate
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPrefixStep
import Definitions.Def_Submission_ThreeSum_TernaryOriginalAppendSemantics
import Theorems.Thm_ThreeSum_LightTernaryCountFrontend_row
import Theorems.Thm_ThreeSum_LightTernaryCountFrontend_rows
import Theorems.Thm_ThreeSum_LightWeightedCountFrontend_row
import Theorems.Thm_ThreeSum_LightWeightedCountFrontend_rows
attribute [local simp] ThreeSum.LightTernaryCountFrontend.row
attribute [local simp] ThreeSum.LightTernaryCountFrontend.rows
attribute [local simp] ThreeSum.LightWeightedCountFrontend.row
attribute [local simp] ThreeSum.LightWeightedCountFrontend.rows


set_option autoImplicit false
noncomputable section
namespace ThreeSum.WeightedGlobalArenaSeedData
open Finset TernaryJointType WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps WeightedGlobalArenaSourceSetup
open WeightedGlobalArenaSeedCandidate LightWeightedGlobalSeedScoreFactory TernaryExtensionEncoding
open TernaryOriginalRowMenu
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 4000000
variable {p : ℕ} [Fact p.Prime]
variable {E : Type*} [Field E] [Fintype E] [DecidableEq E] [Algebra (ZMod p) E]
def physical {J : ℕ} (v : ℕ→Fin (J+2)→ℤ) (i k : ℕ) : ℤ :=
  if hk : k<J+2 then v i (digitOrder J ⟨k,hk⟩) else 0
def root {J : ℕ} (row : ℕ→(Fin (J+2)→ZMod p)→ₗ[ZMod p] ZMod p)
    (O : ℕ→Fin (J+2)→ℤ) (i j : ℕ) : ZMod p := row j (fun t => (O i t : ZMod p))
def hash {J : ℕ} (row : ℕ→(Fin (J+2)→ZMod p)→ₗ[ZMod p] ZMod p)
    (r : ℕ) (v : ℕ→Fin (J+2)→ℤ) (i : ℕ) : Fin r→ZMod p :=
  fun j => row j.val (fun t => (v i t : ZMod p))
def data (I : Input) (A : Inputs) (r b seedOrdinal : ℕ)
    (ℓ : E→ₗ[ZMod p] ZMod p) (seed : E×E)
    (row : ℕ→(Fin (A.J+2)→ZMod p)→ₗ[ZMod p] ZMod p)
    (L R O : ℕ→Fin (A.J+2)→ℤ) (rows : List (Fin A.J→ZMod p))
    (catalog : ℕ→ℕ→ℕ) : Data (config p (r+1) I A seedOrdinal) where
  oldB:=fun i => coefficientCode (hash row r L i)
  oldC:=fun i => coefficientCode (hash row r R i)
  oldO:=fun i => coefficientCode (hash row r O i)
  B:=physical L
  Cvalues:=physical R
  O:=physical O
  coeff:=fun k => if hk : k<A.J+2 then (seedRow (A.J+2) ℓ seed (digitOrder A.J ⟨k,hk⟩)).val else 0
  position:=I.positions
  catalog:=catalog
  logicalRows:=rows
  logicalRow:=(show Fin (A.J+2)→ZMod p from seedRow (A.J+2) ℓ seed)
  bB:=b
  bC:=b
  bO:=b
end ThreeSum.WeightedGlobalArenaSeedData


