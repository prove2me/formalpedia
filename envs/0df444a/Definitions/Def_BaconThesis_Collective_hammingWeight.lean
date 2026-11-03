-- Prove2me | Definitions.Def_BaconThesis_Collective_hammingWeight
-- name    : BaconThesis_Collective_hammingWeight
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:12:10.434806+00:00
-- url     : https://prove2.me/theorems/391bff4e-1691-4871-b139-d3b9c686bd8b
-- title:
--   Hamming weight $H(i)$ of a basis state
-- statement:
--   For a computational basis state $|i\rangle=|i_1\cdots i_n\rangle$ of $n$ qubits, the **Hamming weight** $H(i)$ is the number of $1$'s among $i_1,\dots,i_n$.
--
--   The weak collective decoherence DF subspaces are labelled by it (Definition 8.5.1).
--
--   **Formalization Note** Basis states are bit strings `Fin n → Fin 2` rather than binary numerals.
-- source:
--   Bacon, Decoherence, Control, and Symmetry in Quantum Computers, arXiv:quant-ph/0305025v1, §8.5, p.115 (PDF p.132)

import Mathlib

open scoped Matrix

namespace BaconThesis.Collective

/-- **The Hamming weight `H(i)` of a computational basis state.**
Bacon, *Decoherence, Control, and Symmetry in Quantum Computers*, arXiv:quant-ph/0305025v1, §8.5, p.115 (PDF p.132): "Let `H(i)` denote the Hamming length of number `i` in binary:
`H(i)` is the number of 1's in the binary expression of `i`."

For a bit string `x = (x_1, …, x_n)`, `hammingWeight x` is the number of positions `l` with
`x_l = 1`.

**Formalization Note.** Basis states are bit strings `Fin n → Fin 2` rather than binary numerals. -/
def hammingWeight {n : ℕ} (x : Fin n → Fin 2) : ℕ :=
  (Finset.univ.filter fun l => x l = 1).card

end BaconThesis.Collective


