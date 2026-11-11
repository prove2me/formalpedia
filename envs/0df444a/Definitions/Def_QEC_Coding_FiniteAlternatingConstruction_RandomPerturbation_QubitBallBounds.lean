-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_QubitBallBounds
-- name    : QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_QubitBallBounds
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-10T23:12:26.940071+00:00
-- url     : https://prove2.me/theorems/54848c48-232f-4c45-9f49-74450184acf2
-- title:
--   Qubit Ball Bounds
-- statement:
--   Definitions and structural lemmas for Qubit Ball Bounds, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/QubitBallBounds.lean

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Density
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_PhysicalLocality
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_RandomizedEmbeddingStep
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans

set_option autoImplicit false
noncomputable section
namespace QEC.Coding.BDL26QubitBallBounds
open Classical BDL26FiniteTannerSquare BDL26DecodingGraph BDL26CSSHamiltonian
open BDL26RandomPerturbation BDL26RandomPhysicalLocality BDL26ReplacementEmbedding
open QEC.Coding.ProbabilisticConstruction.SphericalCap
def ballBudget (t R : ℝ) : Nat :=
  Nat.ceil (((2*Nat.ceil R+1 : Nat) : ℝ)^3*(2*t))
def enlargeScale {L : ℝ} (p : GeometricParameters L) : GeometricParameters L :=
  { p with
    lambda := max p.lambda 2
    lambda_one := le_trans p.lambda_one (le_max_left _ _)
    rounding := by
      have hl : (p.lambda : ℝ) ≤ (max p.lambda 2 : Nat) := by exact_mod_cast le_max_left p.lambda 2
      have hc : 0 ≤ 2*(6*(p.m : ℝ))+1 := by positivity
      exact p.rounding.trans (mul_le_mul_of_nonneg_left hl hc)
    probability := by
      exact p.probability.trans (by exact_mod_cast le_max_left p.lambda 2) }
end QEC.Coding.BDL26QubitBallBounds


