-- Prove2me | Definitions.Def_QuantumLTF_Membership_Supplement_dirTensorPow
-- name    : QuantumLTF_Membership_Supplement_dirTensorPow
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T10:39:45.331776+00:00
-- url     : https://prove2.me/theorems/8319bb5e-07a1-4c2a-8c5e-862838363f02
-- title:
--   Product state $(|w\rangle\langle w|)^{\otimes K}$
-- statement:
--   The density matrix $(|w\rangle\langle w|)^{\otimes K}$ on $K$ registers of $s$ qubits (register $k$ on qubits $ks,\dots,ks+s-1$). Its entry at $(y,y')$ is $\prod_k w(y_k)\,w(y'_k)$, where $w(b)$ is the amplitude of $|w\rangle$ at the string $b$. It is the target of band conversion (Eq. (183)) and the ideal input of tomography (Eq. (187)).
--
--   **Formalization Note** $w$ is real, so no complex conjugation appears.
-- source:
--   Krivcenko, Nguyen, de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, arXiv:2609.40331, Eq. (183), p. 67 (PDF p. 68); Eq. (187), p. 70 (PDF p. 71)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QuantumLTF_Membership_splitReg
import Definitions.Def_QuantumLTF_Membership_Supplement_dirAmp

namespace QuantumLTF.Membership.Supplement

open QAlgorithms QuantumLTF.Membership

/-- **The density matrix `(|w⟩⟨w|)^{⊗K}` on `K` registers of `s` qubits.** Krivcenko, Nguyen, de Wolf, *Fast Quantum Algorithms for Learning Linear Threshold Functions*,
arXiv:2609.40331, Eq. (183),
p. 67 (PDF p. 68), and Eq. (187), p. 70 (PDF p. 71). Register `k` occupies wires
`k s, …, k s + s − 1` (`splitReg`); entry `(y, y')` is `∏_k w(y_k) w(y'_k)` with `w(b)` the amplitude of
`|w⟩` (`dirAmp`).

**Formalization Note.** `w` is real, so no complex conjugate is needed. -/
noncomputable def dirTensorPow {n : ℕ} (s K : ℕ) (w : EuclideanSpace ℝ (Fin n)) :
    Matrix (Qubits (K * s)) (Qubits (K * s)) ℂ :=
  Matrix.of fun y y' => ∏ k : Fin K, dirAmp s w (splitReg K s y k) * dirAmp s w (splitReg K s y' k)

end QuantumLTF.Membership.Supplement


