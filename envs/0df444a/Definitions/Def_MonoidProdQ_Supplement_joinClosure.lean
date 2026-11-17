-- Prove2me | Definitions.Def_MonoidProdQ_Supplement_joinClosure
-- name    : MonoidProdQ_Supplement_joinClosure
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T11:08:08.778398+00:00
-- url     : https://prove2.me/theorems/fb49ee72-8e45-4110-b9f8-a93daed5b5ad
-- title:
--   Nonempty join-closure $L_G$
-- statement:
--   Let $M$ be a commutative idempotent monoid, viewed as a join-semilattice with $a\vee b=ab$. For an alphabet $G\subseteq M$, its **nonempty join-closure** is
--
--   $$L_G=\Bigl\{\bigvee H:\ \emptyset\neq H\subseteq G\Bigr\}.$$
--
--   Theorem 22 bounds the product breadth of $G$ by $\lfloor\log_2(|L_G|+1)\rfloor$.
--
--   **Formalization Note** The join of a finite set $H$ is its product $\prod_{a\in H}a$ in the monoid. $L_G$ is the finite set of these products over the nonempty subsets of $G$; it is empty when $G$ is. Idempotence is a hypothesis of the statements that use $L_G$.
-- source:
--   Lee–Santha, The quantum query complexity of the semigroup product problem, arXiv:2609.39974 (held version, sha256 9eec405d…ffb6), §5.2, Eq. (18), p.35

import Mathlib

namespace MonoidProdQ.Supplement

/-- Lee–Santha, *The quantum query complexity of the semigroup product problem*,
arXiv:2609.39974 (held version, sha256 9eec405d…ffb6), §5.2, Eq. (18), p.35: in a commutative
idempotent monoid, written as a join-semilattice (`a ∨ b = ab`),
`L_G = {⋁H : ∅ ≠ H ⊆ G}`, "the nonempty join-closure of the allowed letters".

**Formalization Note.** The join of a finite set `H` in the semilattice is its product
`∏_{a ∈ H} a` (`Finset.prod`), the operation of the monoid. `L_G` is the finset of these
products over the nonempty subsets `H ⊆ G`; it is empty when `G` is. Idempotence is a hypothesis
of the statements that use `L_G`, not part of the definition. -/
def joinClosure {M : Type*} [CommMonoid M] [DecidableEq M] (G : Finset M) : Finset M :=
  (G.powerset.filter Finset.Nonempty).image fun H => H.prod id

end MonoidProdQ.Supplement


