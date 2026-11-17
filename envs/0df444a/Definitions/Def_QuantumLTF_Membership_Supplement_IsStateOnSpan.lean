-- Prove2me | Definitions.Def_QuantumLTF_Membership_Supplement_IsStateOnSpan
-- name    : QuantumLTF_Membership_Supplement_IsStateOnSpan
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T10:40:18.589073+00:00
-- url     : https://prove2.me/theorems/b2b3ffb2-c069-46e5-abf5-825b3e677eb8
-- title:
--   State on $(\mathbb C^n)^{\otimes K}$
-- statement:
--   A matrix $\rho$ on $K$ registers of $s$ qubits is a **state on $(\mathbb C^n)^{\otimes K}$** if it is positive semidefinite with trace $1$ and supported on the span of the strings whose every register holds a label $i<n$. That is, every entry $\rho(y,y')$ with $y$ or $y'$ outside that set is $0$.
--
--   **Formalization Note** $\mathbb C^n$ is embedded by the labels of `dirAmp`.
-- source:
--   Krivcenko, Nguyen, de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, arXiv:2609.40331, Theorem 5.6, p. 70 (PDF p. 71)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QuantumLTF_Membership_splitReg

namespace QuantumLTF.Membership.Supplement

open QAlgorithms QuantumLTF.Membership
open scoped ComplexOrder

/-- **`ρ` is a state on `(Cⁿ)^{⊗K}`.** Krivcenko, Nguyen, de Wolf, *Fast Quantum Algorithms for Learning Linear Threshold Functions*,
arXiv:2609.40331, Theorem 5.6, p. 70 (PDF p. 71): "let `ρ_K` be a state on
`(Cⁿ)^{⊗K}`". `ρ` is a density matrix (positive semidefinite, trace `1`) on `K` registers of `s` qubits
(register `k` on wires `k s, …, k s + s − 1`), supported on the span of the strings whose every register
holds a label `natToBits s i` with `i < n`: every entry `ρ(y, y')` with `y` or `y'` outside that set is `0`.

**Formalization Note.** `Cⁿ` is embedded in `s` qubits by the labels `|i⟩ = natToBits s i`, `i < n`,
the convention of `dirAmp`. -/
def IsStateOnSpan (n s K : ℕ) (ρ : Matrix (Qubits (K * s)) (Qubits (K * s)) ℂ) : Prop :=
  ρ.PosSemidef ∧ ρ.trace = 1 ∧
    ∀ y y' : Qubits (K * s), ρ y y' ≠ 0 →
      (∀ k : Fin K, ∃ i : Fin n, splitReg K s y k = natToBits s i) ∧
      (∀ k : Fin K, ∃ i : Fin n, splitReg K s y' k = natToBits s i)

end QuantumLTF.Membership.Supplement


