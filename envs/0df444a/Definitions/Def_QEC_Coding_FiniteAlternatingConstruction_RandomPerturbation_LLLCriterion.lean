-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_LLLCriterion
-- name    : QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_LLLCriterion
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T10:08:38.168132+00:00
-- url     : https://prove2.me/theorems/163f75f3-9054-4efa-b10c-3d8dff2ebd3f
-- title:
--   LLLCriterion
-- statement:
--   Definitions and structural lemmas for LLLCriterion, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/LLLCriterion.lean

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Parameters
import Mathlib.Algebra.Order.Ring.Pow
set_option autoImplicit false
namespace QEC.Coding.BDL26RandomPerturbation
noncomputable def lllWeight (D : ℕ) : ℝ := 1/(2*((D : ℝ)+1))
end QEC.Coding.BDL26RandomPerturbation


