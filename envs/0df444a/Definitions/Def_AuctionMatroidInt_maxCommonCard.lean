-- Prove2me | Definitions.Def_AuctionMatroidInt_maxCommonCard
-- name    : AuctionMatroidInt_maxCommonCard
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:25:18.145986+00:00
-- url     : https://prove2.me/theorems/8ae266e0-e16f-4b1f-aea0-9adc1e2d5315
-- title:
--   Size $r$ of a maximum common independent set
-- statement:
--   For two matroids $M_1=(E,\mathcal I_1)$ and $M_2=(E,\mathcal I_2)$ on the same finite ground set, let $\mathrm{OPT}$ be a common independent set of maximum size and
--
--   $$
--   r=|\mathrm{OPT}|=\max\{|X| : X\in\mathcal I_1\cap\mathcal I_2\}.
--   $$
--
--   This is the parameter in which the query bounds of Theorem 1.3 are stated.
--
--   **Formalization Note** A `Finset.sup` of cardinalities over the common independent sets, a natural number ($0$ if none existed, which cannot happen for matroids since $\emptyset$ is common independent).
-- source:
--   Huang, Kobayashi, Terao, Auction-Based Algorithms for Weighted Matroid Intersection with Near-Linear Query Complexity (manuscript, sha256 2e12cb4a…), §2.1, p.10 (PDF p.12)

import Mathlib

namespace AuctionMatroidInt

open Classical in
/-- **Size `r` of a maximum common independent set.**
Huang, Kobayashi, Terao (manuscript, sha256 2e12cb4a…), §2.1, p.10: "we are given a finite set E
of size n and two matroids M₁ = (E, I₁) and M₂ = (E, I₂) over E. Let OPT be a common independent
set of maximum size, and let r = |OPT|."

`maxCommonCard I₁ I₂` is the largest cardinality of a set `X ⊆ α` with `X ∈ I₁ ∩ I₂`.

**Formalization Note.** It is a `Finset.sup` of cardinalities over the common independent sets,
a natural number; it would be `0` if no set were common independent, which cannot happen for
matroids (`∅ ∈ I₁ ∩ I₂`). -/
noncomputable def maxCommonCard {α : Type*} [Fintype α] (I₁ I₂ : Finset α → Prop) : ℕ :=
  ((Finset.univ : Finset (Finset α)).filter (fun X => I₁ X ∧ I₂ X)).sup Finset.card

end AuctionMatroidInt


