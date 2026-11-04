-- Prove2me | Definitions.Def_BaconThesis_ExchangeUniv_suOn
-- name    : BaconThesis_ExchangeUniv_suOn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:50:10.414408+00:00
-- url     : https://prove2.me/theorems/c853e206-dc98-48e3-a5d4-7bb4d2052fac
-- title:
--   $\mathfrak{su}$ acting on a subspace only, extended by zero
-- statement:
--   For a set $S$ of vectors in $\mathbb C^d$ with span $W$, let $\mathfrak{su}(W)\oplus0$ be the set of matrices $A$ with
--   $$
--   A^\dagger=-A,\qquad \operatorname{tr}A=0,\qquad Av=0\ \text{ for every } v\perp S .
--   $$
--   An anti-Hermitian $A$ annihilates $W^\perp$ exactly when its range lies in $W$, i.e. when $\Pi A\Pi=A$ for the orthogonal projector $\Pi$ onto $W$; so these are the operators acting as $\mathfrak{su}(\dim W)$ on $W$ and as zero on its orthogonal complement.
--
--   This is the book's "acting as su on the DFS … with zeroes in the matrix representation corresponding to their action on the other DFSs" and the "su(d−1) on the subspace" of the Enlarging Lemma.
--
--   **Formalization Note** Orthogonality uses the standard inner product $\langle w,v\rangle=\sum_k\overline{w_k}v_k$.
-- source:
--   Bacon, Decoherence, Control, and Symmetry in Quantum Computers, arXiv:quant-ph/0305025v1, Theorem C.2.1, p.247 (PDF p.264); Theorem 9.3.1, p.128 (PDF p.145); Enlarging Lemma §D.2, p.256 (PDF p.273)

import Mathlib

open scoped Matrix

namespace BaconThesis.ExchangeUniv

/-- **`su` acting on a subspace only, extended by zero.**
Bacon, *Decoherence, Control, and Symmetry in Quantum Computers*, arXiv:quant-ph/0305025v1, Theorem C.2.1, p.247 (PDF p.264): Hamiltonians "acting as su(d_J) on the DFS … with zeroes
in the matrix representation corresponding to their action on the other DFSs"; Theorem 9.3.1,
p.128 (PDF p.145): elements "which act nontrivial on the Jth irrep but annihilate all states outside
of this irrep"; Enlarging Lemma, §D.2, p.256 (PDF p.273): "generates su(d − 1) on the subspace".

For a set `S` of vectors of `ℂ^ι`, `suOn S` is the set of traceless anti-Hermitian matrices `A`
that annihilate every vector orthogonal to `S` (for the standard inner product
`⟨w, v⟩ = Σ_k conj(w_k) v_k`). Writing `W = span S` and `Π` for the orthogonal projector onto `W`,
an anti-Hermitian `A` kills `W^⊥` iff its range lies in `W` iff `Π A Π = A`; so `suOn S` is
`su(W) ⊕ 0_{W^⊥}`, the operators acting as `su(dim W)` on `W` and as zero outside.

**Formalization Note.** Vectors are plain functions `ι → ℂ`; orthogonality to `S` is
`∀ w ∈ S, star w ⬝ᵥ v = 0`. The range condition is not written separately since it follows from
anti-Hermiticity. -/
def suOn {ι : Type*} [Fintype ι] (S : Set (ι → ℂ)) : Set (Matrix ι ι ℂ) :=
  {A | Aᴴ = -A ∧ A.trace = 0 ∧ ∀ v : ι → ℂ, (∀ w ∈ S, star w ⬝ᵥ v = 0) → A *ᵥ v = 0}

end BaconThesis.ExchangeUniv


