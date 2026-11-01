-- Prove2me | Definitions.Def_BaconThesis_Multilevel_PreservesSubspace
-- name    : BaconThesis_Multilevel_PreservesSubspace
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T16:36:41.937693+00:00
-- url     : https://prove2.me/theorems/917e0b9c-5821-4221-a152-48ff2694e3f4
-- title:
--   Subspace preserving Hamiltonian (Definition 5.3.2)
-- statement:
--   Let $H$ be a Hamiltonian on a finite-dimensional Hilbert space $\mathbb C^{\iota}$ and $S$ a subspace. Following Definition 5.3.2 of the thesis, $H$ **preserves** $S$ if the spectral decomposition of $H$ can be chosen compatibly with $S$: there are an orthonormal basis $(|b_k\rangle)_{k\in\iota}$ and real numbers $(h_k)_{k\in\iota}$ with
--
--   $$
--   H = \sum_{k} h_k\,|b_k\rangle\langle b_k|
--   $$
--
--   such that every $|b_k\rangle$ lies entirely within $S$ or entirely outside of $S$, i.e. is orthogonal to every vector of $S$.
--
--   Since the spectral decomposition is not unique when $H$ has a degenerate eigenvalue, the definition asks only that some decomposition be compatible with $S$. If $H$ preserves $S$, the evolution under $H$ does not take states supported on $S$ to states supported outside $S$; together with the decoherence-free condition this makes the evolution on $S$ unitary.
--
--   **Formalization Note** The Hilbert space is `ι → ℂ` for a finite type $\iota$ with inner product $\langle v|w\rangle = \sum_i \overline{v_i} w_i$. The basis is indexed by $\iota$ itself, so it has exactly $\dim$ vectors. "Entirely outside of $S$" is read as "orthogonal to $S$": the alternative reading "not in $S$" would make every Hamiltonian preserve every subspace. Only Hermitian $H$ can satisfy the definition.
-- source:
--   Bacon, Decoherence, Control, and Symmetry in Quantum Computers, arXiv:quant-ph/0305025v1, Definition 5.3.2, §5.3.3, p.74 (PDF p.91)

import Mathlib

open scoped Matrix

namespace BaconThesis.Multilevel

/-- Bacon, *Decoherence, Control, and Symmetry in Quantum Computers*, arXiv:quant-ph/0305025v1,
Definition 5.3.2 (Subspace preserving Hamiltonian), §5.3.3, p.74 (PDF p.91): a Hamiltonian `H`
**preserves** a subspace `S` if its spectral decomposition `H = Σ_k h_k |k⟩⟨k|` can be chosen so
that every eigenvector `|k⟩` lies entirely within `S` or entirely outside of `S`.

**Formalization Note.** The Hilbert space is `ι → ℂ` for a finite type `ι`, with the inner
product `⟨v|w⟩ = star v ⬝ᵥ w`. A spectral decomposition is an orthonormal basis `b k` (`k : ι`, so
exactly `dim` vectors) together with real eigenvalues `h k` such that
`H = Σ_k h_k |b_k⟩⟨b_k|`. "Entirely outside of `S`" is read as orthogonal to every vector of `S`
(the reading "not in `S`" would make the definition hold for every `H` and `S`, and §5.3.3 asks
that `H` not take states supported on `S` to states supported outside `S`). Only a Hermitian `H`
can satisfy the definition. -/
def PreservesSubspace {ι : Type} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι ℂ)
    (S : Submodule ℂ (ι → ℂ)) : Prop :=
  ∃ (b : ι → ι → ℂ) (h : ι → ℝ),
    (∀ k l, star (b k) ⬝ᵥ b l = if k = l then 1 else 0) ∧
    H = ∑ k, ((h k : ℝ) : ℂ) • Matrix.vecMulVec (b k) (star (b k)) ∧
    ∀ k, b k ∈ S ∨ ∀ v ∈ S, star v ⬝ᵥ b k = 0

end BaconThesis.Multilevel


