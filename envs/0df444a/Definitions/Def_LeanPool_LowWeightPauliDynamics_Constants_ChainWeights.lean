-- Prove2me | Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_ChainWeights
-- name    : LeanPool_LowWeightPauliDynamics_Constants_ChainWeights
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T06:58:58.323308+00:00
-- url     : https://prove2.me/theorems/0e8f8a43-df5b-4042-b104-b1fac28eec65
-- title:
--   Chain Weights
-- statement:
--   Definitions and structural lemmas for Chain Weights, from Jue Xu; LeanPool contributors's pinned Low-weight Pauli dynamics and truncation error development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Constants/ChainWeights.lean

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_PartFactor
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Ladder_ChainBound
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace Lean4LPD
open Finset
noncomputable def chainWeight (kh1 c a : ℝ) (m : ℕ) : ℝ :=
  a ^ m * ∏ i ∈ range m, rungW kh1 c (i + 2)
end Lean4LPD


