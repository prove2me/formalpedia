-- Prove2me | Definitions.Def_BaconThesis_ExchangeUniv_suAlg
-- name    : BaconThesis_ExchangeUniv_suAlg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:50:12.381523+00:00
-- url     : https://prove2.me/theorems/7649aa05-1891-4a39-81ba-01a1b17e123a
-- title:
--   The Lie algebra $\mathfrak{su}(d)$ of traceless anti-Hermitian matrices
-- statement:
--   For a finite index set of size $d$, $\mathfrak{su}(d)$ is the set of $d\times d$ complex matrices $A$ with
--   $$
--   A^\dagger=-A,\qquad \operatorname{tr}A=0 .
--   $$
--   It is a real Lie algebra under the commutator; a traceless Hamiltonian $H$ corresponds to $iH\in\mathfrak{su}(d)$.
-- source:
--   Bacon, Decoherence, Control, and Symmetry in Quantum Computers, arXiv:quant-ph/0305025v1, Enlarging Lemma §D.2 and Mixing Lemma §D.3, pp.256–257 (PDF pp.273–274)

import Mathlib

open scoped Matrix

namespace BaconThesis.ExchangeUniv

/-- **The Lie algebra `su(d)` of traceless anti-Hermitian matrices.**
Bacon, *Decoherence, Control, and Symmetry in Quantum Computers*, arXiv:quant-ph/0305025v1, Mixing Lemma §D.3 and Enlarging Lemma §D.2, pp.256–257 (PDF pp.273–274): "generate su(n)".

`suAlg ι` is the set of `ι × ι` complex matrices `A` with `Aᴴ = −A` and `tr A = 0`.

**Formalization Note.** Hamiltonians `H` (Hermitian, traceless) are represented by `iH`, so
`su(d)` is the anti-Hermitian traceless matrices; it is a real Lie subalgebra of `Matrix ι ι ℂ`. -/
def suAlg (ι : Type*) [Fintype ι] : Set (Matrix ι ι ℂ) :=
  {A | Aᴴ = -A ∧ A.trace = 0}

end BaconThesis.ExchangeUniv


