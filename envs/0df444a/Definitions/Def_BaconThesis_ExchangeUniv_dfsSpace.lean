-- Prove2me | Definitions.Def_BaconThesis_ExchangeUniv_dfsSpace
-- name    : BaconThesis_ExchangeUniv_dfsSpace
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:52:33.770676+00:00
-- url     : https://prove2.me/theorems/16a82213-c5bb-49c8-bf0d-0197a5a72638
-- title:
--   The total-spin-$J$ subspace of $n$ qubits (the block carrying $\mathrm{DFS}_n(J)$)
-- statement:
--   For $n$ qubits and a real number $J$, let
--   $$
--   W_J=\{\,v\in\mathbb C^{2^n}:\ (S^{[n]})^2v=J(J+1)\,v\,\}
--   $$
--   be the eigenspace of the total angular momentum with eigenvalue $J(J+1)$. By the decomposition of Chapter 8, $W_J\cong\mathbb C^{n_J}\otimes\mathbb C^{2J+1}$, and the strong collective decoherence DFS $\mathrm{DFS}_n(J)$ is the degeneracy factor $\mathbb C^{n_J}$; operators that commute with the collective spins act on $W_J$ as $Y\otimes I_{2J+1}$, so "acting on $\mathrm{DFS}_n(J)$" means acting through this block.
--
--   **Formalization Note** The legal values are $J=n/2-r$, $r=0,\dots,\lfloor n/2\rfloor$; for any other real $J$ the set is $\{0\}$. Vectors are functions $\{0,1\}^n\to\mathbb C$.
-- source:
--   Bacon, Decoherence, Control, and Symmetry in Quantum Computers, arXiv:quant-ph/0305025v1, §8.6, (8.39)–(8.43), pp.117–118 (PDF pp.134–135); Theorem 9.3.1, p.128 (PDF p.145)

import Mathlib
import Definitions.Def_BaconThesis_ExchangeUniv_totalS2

open scoped Matrix

namespace BaconThesis.ExchangeUniv

/-- **The total-spin-`J` subspace of `n` qubits, which carries `DFS_n(J)`.**
Bacon, *Decoherence, Control, and Symmetry in Quantum Computers*, arXiv:quant-ph/0305025v1, §8.6, (8.39)–(8.43), pp.117–118 (PDF pp.134–135), and Theorem 9.3.1, p.128 (PDF p.145):
the `n`-qubit space splits as `⊕_J ℂ^(n_J) ⊗ ℂ^(2J+1)`, the block `J` being the eigenspace of
`(S^[n])²` with eigenvalue `J(J+1)`; the strong collective decoherence DFS `DFS_n(J)` is its
degeneracy factor `ℂ^(n_J)`, and "the DFS corresponding to the eigenvalue J" (Theorem C.2.1,
p.247, PDF p.264) is acted on through this block.

`dfsSpace n J` is the set of vectors `v` with `(S^[n])² v = J(J+1) v`, a complex subspace of
`ℂ^(Fin n → Fin 2)`.

**Formalization Note.** `J` is a real number; the legal values are `J = n/2 − r`,
`r = 0, …, ⌊n/2⌋`, and for any other `J` the set is `{0}`. Vectors are plain functions
`(Fin n → Fin 2) → ℂ` acted on by `Matrix.mulVec`. -/
noncomputable def dfsSpace (n : ℕ) (J : ℝ) : Set ((Fin n → Fin 2) → ℂ) :=
  {v | totalS2 n *ᵥ v = ((J * (J + 1) : ℝ) : ℂ) • v}

end BaconThesis.ExchangeUniv


