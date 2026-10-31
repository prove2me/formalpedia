-- Prove2me | Definitions.Def_ObliviousRSP_maxEnt
-- name    : ObliviousRSP_maxEnt
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T15:21:05.246983+00:00
-- url     : https://prove2.me/theorems/12236116-b721-4020-ba22-e7eaf88e4b04
-- title:
--   Maximally entangled state $|\Phi_n\rangle\langle\Phi_n|$
-- statement:
--   Let $n$ be a finite index set with $|n|$ elements. The **maximally entangled state** on two copies of $\mathbb C^n$ is the pure state
--   $$
--   |\Phi_n\rangle = \frac{1}{\sqrt{|n|}}\sum_{i\in n} |i\rangle\otimes|i\rangle ,
--   $$
--   represented by its projector $|\Phi_n\rangle\langle\Phi_n|$, the matrix on $\mathbb C^n\otimes\mathbb C^n$ with entries
--   $$
--   \big(|\Phi_n\rangle\langle\Phi_n|\big)_{(i,j),(k,l)} = \begin{cases} 1/|n| & \text{if } i=j \text{ and } k=l,\\ 0 & \text{otherwise.}\end{cases}
--   $$
--
--   It is the entangled resource shared by Alice and Bob in remote state preparation (with $n$ of dimension $d'$) and the state $|\Phi_d\rangle$ on two copies of the input space used to build the modified measurement.
--
--   **Formalization Note** The index set is an arbitrary finite type with decidable equality, and the first component of a pair is the first tensor factor (Mathlib's Kronecker convention). For a nonempty index set the trace is $1$; for an empty one the matrix is empty.
-- source:
--   Leung–Shor, Oblivious remote state preparation, arXiv:quant-ph/0201008v1, p.2, definition of |Φ_d′⟩ after Fig. 1

import Mathlib

namespace ObliviousRSP

/-- Leung–Shor, *Oblivious remote state preparation*, arXiv:quant-ph/0201008v1, p.2: the maximally entangled state
`|Φ_n⟩ = n^{-1/2} (|11⟩ + ⋯ + |nn⟩)` on two copies of an `n`-dimensional system, as the
projector `|Φ_n⟩⟨Φ_n|`. Its entry at `((i, j), (k, l))` is `1/n` when `i = j` and `k = l`,
and `0` otherwise.

**Formalization Note.** The system is indexed by an arbitrary finite type `n` with decidable
equality (not `Fin n`), and the first component of the pair is the first tensor factor
(Mathlib's `⊗ₖ` convention). The normalization `(Fintype.card n)⁻¹` gives trace `1` for a
nonempty `n`; for an empty `n` the matrix is the empty matrix. -/
noncomputable def maxEnt (n : Type) [Fintype n] [DecidableEq n] : Matrix (n × n) (n × n) ℂ :=
  Matrix.of fun x y => if x.1 = x.2 ∧ y.1 = y.2 then (Fintype.card n : ℂ)⁻¹ else 0

end ObliviousRSP


