-- Prove2me | Definitions.Def_ChapterPauliGrover
-- name    : ChapterPauliGrover
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-01T10:52:07.89247+00:00
-- url     : https://prove2.me/theorems/b0c01a3d-2b45-4003-9dac-7d7a5adaa205
-- title:
--   Chapter PauliGrover
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterPauliGrover.lean`): generated def bundle for ChapterPauliGrover. See BookProof/ChapterPauliGrover.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterPauliGrover.lean

import Definitions.Def_ChapterConditional
import Mathlib


/-!
# Chapter B §3 — a concrete unitary parametrization: the Pauli–Grover rotation

Source: the Pauli–Grover construction of `QFM.tex`
(`\section{Alternate Hamiltonian: the Pauli--Grover construction}`,
`\label{sec:pauli-grover}`), read as a concrete finite-dimensional instance of the
unitary parametrization of a regular conditional probability (`book.tex` §3 *"Any
conditional probability measure in a standard measure space is parametrized by a
unitary operator"*, formalized abstractly in `ChapterJointUnitary` and
`ChapterConditional`).  The section is `sec:pauli-grover` of `QFM.tex`, and §11 of
the book quotes it (`Book/ConditionalUnitary.lean`).

The Pauli–Grover Hamiltonian acts, for each training pair `(i, fᵢ)`, as a Pauli-X
rotation in the two-dimensional subspace `{ |i,0⟩, |i,fᵢ⟩ }`. In the ideal case
`a = 1` this rotation is exactly the swap `|0⟩ ↔ |f⟩`, so that evolving `|0⟩` for
time `τ = π/2` yields `|f⟩` up to an unobservable global phase. The readout
probability of output `f` given input `0` is therefore `1`: the unitary parametrizes
a *deterministic* regular conditional probability (a perfect classifier on the
training pair).

Here we formalize the single-input, two-output core (`X = Y = Fin 2`):

* `pauliX` — the swap (Pauli-X) matrix in the `{ |0⟩, |f⟩ }` basis;
* `pauliX_unitary` — it is a unitary, hence a valid instance of the parametrization
  of `ChapterJointUnitary`;
* `pauliX_rotates` — its action `|0⟩ ↦ |f⟩` (entry `(1,0) = 1`, entry `(0,0) = 0`);
* `pauliX_parametrizes_delta` — the Born readout of column `0` is the delta
  distribution on output `1`;
* `pauliGrover_joint_one`, `pauliGrover_marg_one`, `pauliGrover_cond_one` — through
  the `ChapterConditional` layer, the joint and marginal concentrate on the training
  pair and the regular conditional probability `p(f|0) = 1`.

Everything is `sorry`-free. The imperfect-rotation case `a < 1` (a tunable
approximation) and the many-input sum / Krylov start of `QFM.tex` are described in
the book prose; the ideal `a = 1` swap proved here is the case `QFM.tex` reports as
achieving 100% training accuracy.
-/

open scoped BigOperators Matrix ComplexConjugate
open Matrix
open BookProof.ChapterConditional

namespace BookProof.ChapterPauliGrover

/-- The Pauli-X (swap) matrix on the two-dimensional subspace `{ |0⟩, |f⟩ }`:
zero on the diagonal, one off the diagonal. This is the ideal (`a = 1`)
Pauli–Grover Hamiltonian in the `{ |0⟩, |f⟩ }` basis, which swaps `|0⟩` and
`|f⟩`. -/
noncomputable def pauliX : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => if i = j then 0 else 1

















end BookProof.ChapterPauliGrover


