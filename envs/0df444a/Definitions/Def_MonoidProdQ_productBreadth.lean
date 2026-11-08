-- Prove2me | Definitions.Def_MonoidProdQ_productBreadth
-- name    : MonoidProdQ_productBreadth
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T04:41:49.480767+00:00
-- url     : https://prove2.me/theorems/a8219852-0be8-411c-bb2a-8610453901d2
-- title:
--   Product breadth $\beta_G(M)$
-- statement:
--   Let $M$ be a monoid and $G\subseteq M$ a finite set of allowed letters. For words $u,w\in G^*$ write $u\preceq w$ if $u$ is a **scattered subword** (subsequence) of $w$, and write $[w]$ for the product of the letters of $w$ in order, the empty word having product $1$. A **product core** of $w$ is a scattered subword $u\preceq w$ with $[u]=[w]$. The **product breadth** of $M$ over $G$ is
--
--   $$\beta_G(M)=\sup_{w\in G^*}\ \min\{\,|u| : u\preceq w,\ [u]=[w]\,\}\in\mathbb N\cup\{\infty\}.$$
--
--   Thus $\beta_G(M)$ is the smallest bound such that every word over $G$ has a product core of at most that length; it may be infinite. For a commutative monoid with $G=M$ it is the small Davenport constant. It is the parameter that governs the quantum query complexity of products in this mission.
--
--   **Formalization Note** Words are lists of elements of $M$ lying in $G$, $\preceq$ is `List.Sublist`, and $[w]$ is `List.prod`. The value is an extended natural number, so an unbounded supremum is $\infty$. The paper states the definition for aperiodic $M$, but the formula does not use aperiodicity, so it is defined for every monoid.
-- source:
--   Lee–Santha, The quantum query complexity of the semigroup product problem, arXiv:2609.39974 (held version, sha256 9eec405d…ffb6), §1, Eq. (1), p.5

import Mathlib

namespace MonoidProdQ

/-- Lee–Santha, *The quantum query complexity of the semigroup product problem*,
arXiv:2609.39974 (held version, sha256 9eec405d…ffb6), §1, Eq. (1), p.5: the product breadth of `M` over the allowed alphabet `G ⊆ M`,
`β_G(M) = sup_{w ∈ G*} min {|u| : u ⪯ w, [u] = [w]}`, where `u ⪯ w` means that `u` is a
scattered subword (subsequence) of `w` and `[w]` is the product of the letters of `w`, the empty
word having product `1`. "It may be infinite."

**Formalization Note.** A word over `G` is a list of elements of `M` all lying in `G`; `⪯` is
`List.Sublist` (order-preserving, not necessarily contiguous); `[w]` is the ordered product
`List.prod`, which is `1` on the empty list. The value is in `ℕ∞`, so an unbounded supremum is
`⊤`, not a junk value. The inner infimum ranges over a nonempty set (`u = w`), so it is attained.
The paper states the definition for an aperiodic `M`; nothing in Eq. (1) uses aperiodicity, so
it is defined for every monoid and aperiodicity stays a hypothesis of the statements. -/
noncomputable def productBreadth {M : Type*} [Monoid M] (G : Finset M) : ℕ∞ :=
  ⨆ (w : List M) (_ : ∀ a ∈ w, a ∈ G),
    ⨅ (u : List M) (_ : u.Sublist w ∧ u.prod = w.prod), (u.length : ℕ∞)

end MonoidProdQ


