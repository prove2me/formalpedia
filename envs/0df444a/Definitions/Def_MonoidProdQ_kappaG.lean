-- Prove2me | Definitions.Def_MonoidProdQ_kappaG
-- name    : MonoidProdQ_kappaG
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T04:54:14.6522+00:00
-- url     : https://prove2.me/theorems/f6310043-9cd3-4851-b321-f86a83c8227e
-- title:
--   Essential width $\kappa_G(M)$ of the subset-product summary
-- statement:
--   For a commutative monoid $M$ and $G\subseteq M$, the essential width of the subset-product summary over all word lengths is
--
--   $$\kappa_G(M)=\sup_{s\ge0}\ \sup_{x\in G^s}\ |\mathrm{Ess}_x([s])|\ \in\mathbb N\cup\{\infty\}.$$
--
--   Lemma 20 shows that it equals the product breadth $\beta_G(M)$ when $M$ is finite and aperiodic.
--
--   **Formalization Note** $[s]$ is the full index set of a word of length $s$; the value is an extended natural number.
-- source:
--   Lee–Santha, The quantum query complexity of the semigroup product problem, arXiv:2609.39974 (held version, sha256 9eec405d…ffb6), Lemma 20, Eq. (17), p.33

import Definitions.Def_MonoidProdQ_subsetEss

namespace MonoidProdQ

/-- Lee–Santha, *The quantum query complexity of the semigroup product problem*,
arXiv:2609.39974 (held version, sha256 9eec405d…ffb6), Lemma 20, Eq. (17), p.33: the essential width of the subset-product summary over all
word lengths, `κ_G(M) = sup_{s ≥ 0} sup_{x ∈ G^s} |Essₓ([s])|`.

**Formalization Note.** `[s]` is `Finset.univ : Finset (Fin s)`; the value is in `ℕ∞`, so an
unbounded supremum is `⊤`. -/
noncomputable def kappaG {M : Type*} [CommMonoid M] [DecidableEq M] (G : Finset M) : ℕ∞ :=
  ⨆ (s : ℕ) (x : Fin s → G), ((subsetEss x Finset.univ).card : ℕ∞)

end MonoidProdQ


