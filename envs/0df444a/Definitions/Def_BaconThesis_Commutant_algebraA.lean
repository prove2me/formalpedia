-- Prove2me | Definitions.Def_BaconThesis_Commutant_algebraA
-- name    : BaconThesis_Commutant_algebraA
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T16:37:18.8263+00:00
-- url     : https://prove2.me/theorems/7a0249c3-5c39-4e27-8033-e3fc92b6467a
-- title:
--   The OSR algebra in decomposed form $A\cong\bigoplus_J I_{n_J}\otimes M_{d_J}$
-- statement:
--   Let $\mathcal H=\mathbb C^{\iota}$ be the physical Hilbert space, let $(\mathcal J,n,d)$ be irrep labels, degeneracies and irrep dimensions, and let $W$ be a matrix from $\mathbb C^{\iota}$ to $\bigoplus_J\mathbb C^{n_J}\otimes\mathbb C^{d_J}$ (in every statement of this mission $W$ is unitary: it is the change to the basis $|J,\lambda,m\rangle$). Define
--   $$
--   A=\Bigl\{\,W^\dagger\Bigl(\bigoplus_{J\in\mathcal J} I_{n_J}\otimes X_J\Bigr)W \;:\; X_J\in M_{d_J}\ \text{for every } J\,\Bigr\},
--   $$
--   where each $X_J$ ranges independently over **all** $d_J\times d_J$ complex matrices. This is an algebra $A\cong\bigoplus_J I_{n_J}\otimes M_{d_J}$ in the sense of (5.30): by Theorem 5.4.1, every †-closed complex associative algebra containing the identity, in particular the OSR algebra of a system coupled to an environment, has this form for a suitable orthonormal basis.
--
--   **Formalization Note** The decomposition produced by Theorem 5.4.1 (which the book cites) is taken as the data $(\mathcal J,n,d,W)$; the set is all of $\{W^\dagger\,\mathrm{blockA}(X)\,W\}$, not a subset.
-- source:
--   Bacon, Decoherence, Control, and Symmetry in Quantum Computers, arXiv:quant-ph/0305025v1, Theorem 5.4.1, eqs. (5.30)–(5.31), pp.77–78 (PDF pp.94–95); eq. (5.38), p.80 (PDF p.97); eq. (7.2), Lemmas 7.3.1 and 7.3.2, pp.100–103 (PDF pp.117–120)

import Mathlib
import Definitions.Def_BaconThesis_Commutant_blockA

namespace BaconThesis.Commutant

/-- **The OSR (or SME) algebra in decomposed form, `A ≅ ⊕_{J∈𝒥} I_{n_J} ⊗ M_{d_J}`.**
Bacon, *Decoherence, Control, and Symmetry in Quantum Computers*, arXiv:quant-ph/0305025v1,
§5.4.1, Theorem 5.4.1, eqs. (5.30)–(5.31), pp.77–78 (PDF pp.94–95); §5.4.3, eq. (5.38), p.80
(PDF p.97); §7.3, eq. (7.2) and Lemmas 7.3.1, 7.3.2, pp.100–103 (PDF pp.117–120): "there is a basis
such that the operation of every operator `S` in a †-closed complex associative algebra acts on the
Hilbert space as `S = ⊕_J I_{n_J} ⊗ S_{d_J}` … the `S_{d_J}` span the entire space of `d_J`
dimensional operators".

The physical Hilbert space is `ℂ^ι`. The orthonormal basis change to the basis `|J, λ, m⟩` is a
matrix `W` from `ℂ^ι` to `⊕_J ℂ^{n_J} ⊗ ℂ^{d_J}` (unitary in every statement that uses it), and
`algebraA n d W` is the set of **all** operators `W† (⊕_J I_{n_J} ⊗ X_J) W` with `X_J` ranging over
every `d_J × d_J` complex matrix independently for each `J` (the full matrix algebras `M_{d_J}`).

**Formalization Note.** The decomposition produced by Theorem 5.4.1 (cited by the book) is taken as
given data `(𝒥, n, d, W)`; the irrep labels form a finite type `𝒥`. The algebra is the full set
`{W† blockA X W}`, not a subset of it: this is what "≅ ⊕ I_{n_J} ⊗ M_{d_J}" means. -/
noncomputable def algebraA {𝒥 ι : Type} [Fintype 𝒥] [DecidableEq 𝒥] [Fintype ι]
    (n d : 𝒥 → ℕ) (W : Matrix (Σ J : 𝒥, Fin (n J) × Fin (d J)) ι ℂ) : Set (Matrix ι ι ℂ) :=
  {A | ∃ X : (J : 𝒥) → Matrix (Fin (d J)) (Fin (d J)) ℂ, A = W.conjTranspose * blockA n d X * W}

end BaconThesis.Commutant


