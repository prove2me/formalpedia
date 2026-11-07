-- Prove2me | Definitions.Def_QuantumHMMR_stabDim
-- name    : QuantumHMMR_stabDim
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:35:36.483993+00:00
-- url     : https://prove2.me/theorems/163d7e6e-e664-4889-b4f1-1fe44d699ce4
-- title:
--   Stabilizer dimension $\dim S(\psi)$
-- statement:
--   The **stabilizer dimension** $\dim S(\psi)$ of an $n$-qubit vector is the dimension over $\mathbb F_2$ of the binary subspace $S(\psi)$ of its Pauli stabilizer labels. It equals $n$ for stabilizer states such as $|0^n\rangle$ and is $0$ for typical states; Lemma 4.4 tests whether it is at least $n - h$.
--
--   **Formalization Note** Taken as the dimension of the $\mathbb F_2$-span of the label set, which equals the label set for nonzero $\psi$.
-- source:
--   Dujmovic–Haferkamp–Poremba, On the pseudorandomness of simple quantum processes, arXiv:2610.02100 (held version sha256 9920ec45…), Section 4.1, pp.14, 16

import Mathlib
import Definitions.Def_QuantumHMMR_stabilizerLabels

open QAlgorithms

namespace QuantumHMMR

/-- `dim S(ψ)`, the dimension over `𝔽₂` of the binary subspace of Pauli stabilizer labels of `ψ`
(Dujmovic–Haferkamp–Poremba, *On the pseudorandomness of simple quantum processes*, arXiv:2610.02100 (held version, sha256 9920ec45…4f20), §4.1, pp.14, 16).

**Formalization Note** Taken as the `ZMod 2`-dimension of the span of `stabilizerLabels ψ`. For a
nonzero `ψ` the label set is already a subspace (two Paulis that both fix `ψ` up to sign commute),
so the span changes nothing; `dim S(|0ⁿ⟩) = n`. -/
noncomputable def stabDim {n : ℕ} (ψ : EuclideanSpace ℂ (Qubits n)) : ℕ :=
  Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (stabilizerLabels ψ))

end QuantumHMMR


