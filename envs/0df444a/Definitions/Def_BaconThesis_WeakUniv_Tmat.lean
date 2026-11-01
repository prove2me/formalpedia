-- Prove2me | Definitions.Def_BaconThesis_WeakUniv_Tmat
-- name    : BaconThesis_WeakUniv_Tmat
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T16:36:43.052486+00:00
-- url     : https://prove2.me/theorems/2fb0bc03-04a8-4c39-9413-3ee843abb13e
-- title:
--   Eq. (9.4) — the two-qubit operator $T_{ij}(z_1,z_2,z_3,z_4,h)$
-- statement:
--   For real numbers $z_1,z_2,z_3,z_4$ and a complex number $h$, the two-qubit operator $T(z_1,z_2,z_3,z_4,h)$ is, in the computational basis $|00\rangle,|01\rangle,|10\rangle,|11\rangle$,
--   $$
--   T(z_1,z_2,z_3,z_4,h)=\begin{pmatrix} z_1&0&0&0\\ 0&z_2&h&0\\ 0&\bar h&z_3&0\\ 0&0&0&z_4\end{pmatrix}.
--   $$
--   It is Hermitian, preserves the number of ones of a two-bit string, and is the general form of a two-qubit Hamiltonian commuting with the collective operator $S_z$. The diagonal operators $T^P=T(1,0,0,0,0)$, $T^Q=T(0,0,0,1,0)$ and $\bar Z=T(0,0,1,0,0)$ are three of the four generators of the mission.
--
--   **Formalization Note** A two-qubit operator is indexed by pairs $(a,b)\in\{0,1\}^2$, the basis state $|ab\rangle$ with $a$ the first qubit; the book's row order is $2a+b$.
-- source:
--   Bacon, Decoherence, Control, and Symmetry in Quantum Computers, arXiv:quant-ph/0305025v1, §9.1.1, eq. (9.4), p.125 (PDF p.142)

import Mathlib

namespace BaconThesis.WeakUniv

/-- **The two-qubit operators commuting with collective `S_z`, `T_ij(z₁, z₂, z₃, z₄, h)`.**
Bacon, *Decoherence, Control, and Symmetry in Quantum Computers*, arXiv:quant-ph/0305025v1,
§9.1.1, eq. (9.4), p.125 (PDF p.142): "The most general Hamiltonian on two qubits i and j is then
of the form T_ij(z1, z2, z3, z4, h) = [[z1,0,0,0],[0,z2,h,0],[0,h*,z3,0],[0,0,0,z4]] … in the
standard computational basis".

`Tmat z₁ z₂ z₃ z₄ h` is the `4 × 4` matrix of (9.4) in the computational basis
`|00⟩, |01⟩, |10⟩, |11⟩` of two qubits: diagonal entries `z₁, z₂, z₃, z₄`, entry `h` in row `|01⟩`,
column `|10⟩`, entry `h*` in row `|10⟩`, column `|01⟩`, and zero elsewhere.

**Formalization Note.** A two-qubit operator is a `Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ`; the
pair `(a, b)` is the basis state `|ab⟩` with `a` the first qubit (`i`) and `b` the second (`j`),
so the book's row order `|00⟩, |01⟩, |10⟩, |11⟩` is `(0,0), (0,1), (1,0), (1,1)`
(`finProdFinEquiv (a, b) = 2a + b`). The diagonal entries are real, as for the book's Hamiltonians. -/
def Tmat (z₁ z₂ z₃ z₄ : ℝ) (h : ℂ) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  (!![(z₁ : ℂ), 0, 0, 0;
      0, (z₂ : ℂ), h, 0;
      0, star h, (z₃ : ℂ), 0;
      0, 0, 0, (z₄ : ℂ)] : Matrix (Fin 4) (Fin 4) ℂ).submatrix finProdFinEquiv finProdFinEquiv

end BaconThesis.WeakUniv


