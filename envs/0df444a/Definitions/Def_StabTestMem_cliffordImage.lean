-- Prove2me | Definitions.Def_StabTestMem_cliffordImage
-- name    : StabTestMem_cliffordImage
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T09:11:12.641706+00:00
-- url     : https://prove2.me/theorems/847bb793-b501-41a7-96c7-f2174948d363
-- title:
--   Image $C(M)$ of a set of labels under a Clifford $C$
-- statement:
--   Conjugation by a Clifford maps Paulis to Paulis up to sign: $CP_uC^\dagger=\pm P_v$ with $v=Bu$ for a symplectic matrix $B$. For a set $M$ of labels,
--
--   $$C(M)=\{v\;:\;CP_uC^\dagger\in\mathbb C\,P_v\ \text{for some } u\in M\}.$$
--
--   It maps a Lagrangian subspace $M$ to a Lagrangian subspace $C(M)$.
-- source:
--   Arunachalam, Schatzki, Optimal stabilizer testing and learning with limited quantum memory, arXiv:2607.02444 (version of 2 Nov 2026), §2.1, p. 14; p. 33

import Definitions.Def_StabTestMem_weyl

namespace StabTestMem

open QAlgorithms

/-- **The image `C(M)` of a set of Pauli labels under a Clifford `C`.** Arunachalam, Schatzki, *Optimal stabilizer testing and learning with limited quantum memory*, arXiv:2607.02444 (version of 2 Nov 2026), §2.1, p. 14 ("C P_u
C† = (−1)^{c(u)} P_v for some v ∈ F_2^{2n} … conjugation by a Clifford unitary corresponds to
multiplication by some matrix in Sp(2n, F_2). That is, u is mapped to Bu"), and p. 33: "This maps
the Lagrangian subspace M to some other subspace C(M)."

`cliffordImage C M` is the set of labels `v` such that `C P_u C†` is a scalar multiple of `P_v`
for some `u ∈ M`. For a Clifford `C` the scalar is `±1` and `v = B u`. -/
def cliffordImage {n : ℕ} (C : Matrix.unitaryGroup (Qubits n) ℂ) (M : Set (CutRankSched.Pauli n)) :
    Set (CutRankSched.Pauli n) :=
  {v | ∃ u ∈ M, ∃ c : ℂ,
    (C : Matrix (Qubits n) (Qubits n) ℂ) * weyl u * star (C : Matrix (Qubits n) (Qubits n) ℂ) =
      c • weyl v}

end StabTestMem


