-- Prove2me | Definitions.Def_QEC_Coding_QuantumTanner_ArithmeticPSLGoodness
-- name    : QEC_Coding_QuantumTanner_ArithmeticPSLGoodness
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T00:59:03.607568+00:00
-- url     : https://prove2.me/theorems/bc7427b1-30d4-47e0-8222-2ef352b26408
-- title:
--   Arithmetic PSLGoodness
-- statement:
--   Definitions and structural lemmas for Arithmetic PSLGoodness, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/ArithmeticPSLGoodness.lean

import Definitions.Def_QEC_Coding_QuantumTanner_ArithmeticPSLFamily
import Definitions.Def_QEC_Coding_QuantumTanner_SpectralFamily
import Definitions.Def_QEC_Coding_ExpanderCodes_PrimeFieldParameters
set_option autoImplicit false
noncomputable section
namespace QEC.Coding.QuantumTanner.ArithmeticPSLFamily
open Classical QEC.Coding.ExpanderCodes.QuaternionGenerators QEC.Coding.SmallSetExpansion
variable (p : ℕ) [Fact p.Prime] (hOdd : 3 ≤ p)
  (epsilon : ZMod p) (hEpsilon : epsilon ≠ 0)
def sampleFamily (rho : ℝ)
    (sample : RandomLocalCodeSample (randomRowCount rho (p + 1))
      (TorusIndex epsilon) (TorusIndex epsilon)) (n : ℕ) :=
  canonicalDataOfLocalCodeSample
    (left p hOdd epsilon hEpsilon n) (right p hOdd epsilon hEpsilon n)
    (indexedLeftInverse epsilon hEpsilon) (Equiv.refl _)
    (left_injective p hOdd epsilon hEpsilon n) (right_injective p hOdd epsilon hEpsilon n)
    (left_inverse p hOdd epsilon hEpsilon n) (right_inverse p hOdd epsilon hEpsilon n)
    (total_nonconjugacy p hOdd epsilon hEpsilon n) sample
end QEC.Coding.QuantumTanner.ArithmeticPSLFamily


