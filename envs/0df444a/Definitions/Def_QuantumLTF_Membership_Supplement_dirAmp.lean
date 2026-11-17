-- Prove2me | Definitions.Def_QuantumLTF_Membership_Supplement_dirAmp
-- name    : QuantumLTF_Membership_Supplement_dirAmp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T10:39:12.423719+00:00
-- url     : https://prove2.me/theorems/d479bc5f-ed99-4272-9a43-bbf9e47b7e8b
-- title:
--   Direction state $|w\rangle=\sum_{i<n}w_i|i\rangle$ in an $s$-qubit register
-- statement:
--   The amplitudes of the direction state $|w\rangle=\sum_{i=1}^n w_i|i\rangle$ in a register of $s$ qubits: the basis string holding the label $i<n$ in binary (most significant bit first) has amplitude $w_i$, and every other string has amplitude $0$.
--
--   **Formalization Note** Labels are $0$-based. The theorems assume $n\le2^s$, so distinct labels are distinct strings.
-- source:
--   Krivcenko, Nguyen, de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, arXiv:2609.40331, §5, p. 57 (PDF p. 58)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic

namespace QuantumLTF.Membership.Supplement

open QAlgorithms

/-- **The direction state `|w⟩ := Σ_{i<n} w_i |i⟩` in a register of `s` qubits.** Krivcenko, Nguyen, de Wolf, *Fast Quantum Algorithms for Learning Linear Threshold Functions*,
arXiv:2609.40331, §5,
p. 57 (PDF p. 58): "the unknown direction state `|w⟩ := Σ_{i=1}^n w_i|i⟩`". The amplitude of the basis
string `b` is `w_i` if `b = natToBits s i` for some `i < n`, and `0` otherwise.

**Formalization Note.** The label `i` (0-based) is written in binary, most significant bit first. The
register is meant to hold `Cⁿ`, i.e. `n ≤ 2^s`; every theorem using it assumes this, so the labels
`natToBits s i`, `i < n`, are distinct and the sum has at most one nonzero term. -/
noncomputable def dirAmp {n : ℕ} (s : ℕ) (w : EuclideanSpace ℝ (Fin n)) (b : Qubits s) : ℂ :=
  ∑ i : Fin n, if b = natToBits s i then ((w i : ℝ) : ℂ) else 0

end QuantumLTF.Membership.Supplement


