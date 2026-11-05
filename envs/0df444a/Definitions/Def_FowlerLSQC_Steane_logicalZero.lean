-- Prove2me | Definitions.Def_FowlerLSQC_Steane_logicalZero
-- name    : FowlerLSQC_Steane_logicalZero
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:36:55.509123+00:00
-- url     : https://prove2.me/theorems/f7357833-da62-4e5f-9c4a-1812a708ff52
-- title:
--   The Steane-code logical zero $|0_L\rangle$
-- statement:
--   The logical zero of the seven-qubit Steane code is the vector
--
--   $$|0_L\rangle=\frac{1}{\sqrt 8}\bigl(|0000000\rangle+|1010101\rangle+|0110011\rangle+|1100110\rangle+|0001111\rangle+|1011010\rangle+|0111100\rangle+|1101001\rangle\bigr)$$
--
--   of the $2^7$-dimensional space of seven qubits, whose leftmost digit is qubit $0$.
--
--   Together with $|1_L\rangle$ it spans the code space of the Steane code.
-- source:
--   Fowler, Towards Large-Scale Quantum Computation, arXiv:quant-ph/0506126v1, §10.2, (10.5), p.112 (PDF p.130)

import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_FowlerLSQC_Steane_bitString

namespace FowlerLSQC.Steane

open QAlgorithms

/-- Fowler, *Towards Large-Scale Quantum Computation*, arXiv:quant-ph/0506126v1, §10.2, (10.5),
p.112 (PDF p.130): the Steane-code logical zero
`|0_L⟩ = (1/√8)(|0000000⟩ + |1010101⟩ + |0110011⟩ + |1100110⟩ + |0001111⟩ + |1011010⟩ + |0111100⟩ + |1101001⟩)`,
with the eight strings in the printed order.

**Formalization Note.** A vector of `EuclideanSpace ℂ (Qubits 7)`, the whole 128-dimensional space
of seven qubits, built from the published basis vectors `QAlgorithms.ket`. The leftmost character
of each string is wire `0`. -/
noncomputable def logicalZero : EuclideanSpace ℂ (Qubits 7) :=
  ((Real.sqrt 8 : ℝ) : ℂ)⁻¹ •
    (ket (bitString ![0, 0, 0, 0, 0, 0, 0]) + ket (bitString ![1, 0, 1, 0, 1, 0, 1]) +
      ket (bitString ![0, 1, 1, 0, 0, 1, 1]) + ket (bitString ![1, 1, 0, 0, 1, 1, 0]) +
      ket (bitString ![0, 0, 0, 1, 1, 1, 1]) + ket (bitString ![1, 0, 1, 1, 0, 1, 0]) +
      ket (bitString ![0, 1, 1, 1, 1, 0, 0]) + ket (bitString ![1, 1, 0, 1, 0, 0, 1]))

end FowlerLSQC.Steane


