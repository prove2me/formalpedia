-- Prove2me | Definitions.Def_FowlerLSQC_Steane_logicalOne
-- name    : FowlerLSQC_Steane_logicalOne
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:36:50.042253+00:00
-- url     : https://prove2.me/theorems/11e0d828-f89d-4394-96be-ada0e650e78a
-- title:
--   The Steane-code logical one $|1_L\rangle$
-- statement:
--   The logical one of the seven-qubit Steane code is the vector
--
--   $$|1_L\rangle=\frac{1}{\sqrt 8}\bigl(|1111111\rangle+|0101010\rangle+|1001100\rangle+|0011001\rangle+|1110000\rangle+|0100101\rangle+|1000011\rangle+|0010110\rangle\bigr)$$
--
--   of the $2^7$-dimensional space of seven qubits, whose leftmost digit is qubit $0$.
--
--   Together with $|0_L\rangle$ it spans the code space of the Steane code.
-- source:
--   Fowler, Towards Large-Scale Quantum Computation, arXiv:quant-ph/0506126v1, §10.2, (10.6), p.112 (PDF p.130)

import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_FowlerLSQC_Steane_bitString

namespace FowlerLSQC.Steane

open QAlgorithms

/-- Fowler, *Towards Large-Scale Quantum Computation*, arXiv:quant-ph/0506126v1, §10.2, (10.6),
p.112 (PDF p.130): the Steane-code logical one
`|1_L⟩ = (1/√8)(|1111111⟩ + |0101010⟩ + |1001100⟩ + |0011001⟩ + |1110000⟩ + |0100101⟩ + |1000011⟩ + |0010110⟩)`,
with the eight strings in the printed order.

**Formalization Note.** A vector of `EuclideanSpace ℂ (Qubits 7)`, the whole 128-dimensional space
of seven qubits, built from the published basis vectors `QAlgorithms.ket`. The leftmost character
of each string is wire `0`. -/
noncomputable def logicalOne : EuclideanSpace ℂ (Qubits 7) :=
  ((Real.sqrt 8 : ℝ) : ℂ)⁻¹ •
    (ket (bitString ![1, 1, 1, 1, 1, 1, 1]) + ket (bitString ![0, 1, 0, 1, 0, 1, 0]) +
      ket (bitString ![1, 0, 0, 1, 1, 0, 0]) + ket (bitString ![0, 0, 1, 1, 0, 0, 1]) +
      ket (bitString ![1, 1, 1, 0, 0, 0, 0]) + ket (bitString ![0, 1, 0, 0, 1, 0, 1]) +
      ket (bitString ![1, 0, 0, 0, 0, 1, 1]) + ket (bitString ![0, 0, 1, 0, 1, 1, 0]))

end FowlerLSQC.Steane


