-- Prove2me | Definitions.Def_QuantumHMMR_stabilizerLabels
-- name    : QuantumHMMR_stabilizerLabels
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:34:39.582339+00:00
-- url     : https://prove2.me/theorems/47ed5187-3e95-41ff-b3d6-252c5495c4ef
-- title:
--   Pauli stabilizer labels $S(\psi)$
-- statement:
--   For $x = (a, b) \in \mathbb F_2^{2n}$ let
--   $$
--   W_x = \bigotimes_{i=1}^n i^{a_i b_i} X^{a_i} Z^{b_i}
--   $$
--   be the corresponding Hermitian Pauli operator. The set of **Pauli stabilizer labels** of $\psi$ is
--   $$
--   S(\psi) = \{\, x \in \mathbb F_2^{2n} : W_x|\psi\rangle = \pm|\psi\rangle \,\}.
--   $$
--   For a nonzero $\psi$ it is a binary subspace.
--
--   **Formalization Note** $W_x$ is the published `pauliOps` with letter $I$, $X$, $Z$ or $Y = iXZ$ for $(a_i, b_i) = (0,0), (1,0), (0,1), (1,1)$, factor $i$ on wire $i$.
-- source:
--   Dujmovic–Haferkamp–Poremba, On the pseudorandomness of simple quantum processes, arXiv:2610.02100 (held version sha256 9920ec45…), Section 4.1, p.14

import Mathlib
import Definitions.Def_QAlgorithms_Defs_QECC

open QAlgorithms Stabilizer

namespace QuantumHMMR

/-- The Pauli stabilizer labels of an `n`-qubit vector (Dujmovic–Haferkamp–Poremba, *On the pseudorandomness of simple quantum processes*, arXiv:2610.02100 (held version, sha256 9920ec45…4f20), §4.1, p.14): for
`x = (a, b) ∈ 𝔽₂^{2n}` let `W_x = ⊗_i i^{a_i b_i} X^{a_i} Z^{b_i}`, and
`S(ψ) = {x : W_x |ψ⟩ = ±|ψ⟩}`.

**Formalization Note** `W_x` is the published `pauliOps` with letter `I` for `(a_i, b_i) = (0, 0)`,
`X` for `(1, 0)`, `Z` for `(0, 1)` and `Y = iXZ` for `(1, 1)`, factor `i` on wire `i`. The labels are
pairs `(a, b)` of vectors in `(ZMod 2)ⁿ`. -/
noncomputable def stabilizerLabels {n : ℕ} (ψ : EuclideanSpace ℂ (Qubits n)) :
    Set ((Fin n → ZMod 2) × (Fin n → ZMod 2)) :=
  {x | act (pauliOps fun i => if x.1 i = 0 then (if x.2 i = 0 then Pauli.I else Pauli.Z)
          else (if x.2 i = 0 then Pauli.X else Pauli.Y)) ψ = ψ ∨
       act (pauliOps fun i => if x.1 i = 0 then (if x.2 i = 0 then Pauli.I else Pauli.Z)
          else (if x.2 i = 0 then Pauli.X else Pauli.Y)) ψ = -ψ}

end QuantumHMMR


