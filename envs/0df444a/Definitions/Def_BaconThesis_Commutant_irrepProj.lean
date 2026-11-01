-- Prove2me | Definitions.Def_BaconThesis_Commutant_irrepProj
-- name    : BaconThesis_Commutant_irrepProj
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T16:37:29.942979+00:00
-- url     : https://prove2.me/theorems/3b9b269c-4f8e-440f-ba59-7d723821add4
-- title:
--   The projector $P_K$ onto the subspace of the $K$-th irrep
-- statement:
--   In the setting of $\mathrm{algebraA}$, for an irrep label $K\in\mathcal J$ define
--   $$
--   P_K=W^\dagger\Bigl(\bigoplus_{J\in\mathcal J}\delta_{JK}\,I_{n_J}\otimes I_{d_J}\Bigr)W .
--   $$
--   For unitary $W$ this is the orthogonal projector onto the subspace spanned by the vectors $W^\dagger|K,\lambda,m\rangle$, $\lambda\le n_K$, $m\le d_K$: the subspace "over which the operators act" for the irrep $K$. Information encoded into the $K$-th irrep, in particular into its degeneracy, is carried by states $\rho$ supported on this subspace, $P_K\rho P_K=\rho$.
--
--   **Formalization Note** $P_K=W^\dagger\,\mathrm{blockC}(Y)\,W$ with $Y_K=I_{n_K}$ and $Y_J=0$ for $J\ne K$.
-- source:
--   Bacon, Decoherence, Control, and Symmetry in Quantum Computers, arXiv:quant-ph/0305025v1, §5.4.1, pp.78–79 (PDF pp.95–96); Lemmas 7.3.1, 7.3.2, 7.4.1, pp.100–104 (PDF pp.117–121)

import Mathlib
import Definitions.Def_BaconThesis_Commutant_blockC

namespace BaconThesis.Commutant

/-- **The projector `P_K` onto the subspace of the `K`-th irrep.**
Bacon, *Decoherence, Control, and Symmetry in Quantum Computers*, arXiv:quant-ph/0305025v1,
§5.4.1, p.78 (PDF p.95): "Given a `J ∈ 𝒥` for an algebra `A` there is a subspace over which the
operators act", spanned by the basis vectors `|J, λ, m⟩` with `J` fixed; information "encoded into
the degeneracy of the `J`th irrep" (p.79, PDF p.96) and "information which has been encoded into a
irrep" (Lemma 7.4.1, p.104, PDF p.121) is supported on this subspace.

`irrepProj n d W K = W† (⊕_J δ_{JK} I_{n_J} ⊗ I_{d_J}) W` is the orthogonal projector (for unitary
`W`) of `ℂ^ι` onto the span of `W† |K, λ, m⟩`, `λ < n_K`, `m < d_K`.

**Formalization Note.** Built from `blockC` with `Y = Pi.single K 1` (the identity on block `K`, zero
on every other block). A state `ρ` is supported on the `K`-th irrep when
`irrepProj K * ρ * irrepProj K = ρ`. -/
noncomputable def irrepProj {𝒥 ι : Type} [Fintype 𝒥] [DecidableEq 𝒥] [Fintype ι]
    (n d : 𝒥 → ℕ) (W : Matrix (Σ J : 𝒥, Fin (n J) × Fin (d J)) ι ℂ) (K : 𝒥) :
    Matrix ι ι ℂ :=
  W.conjTranspose *
    blockC n d (Pi.single (M := fun J => Matrix (Fin (n J)) (Fin (n J)) ℂ) K 1) * W

end BaconThesis.Commutant


