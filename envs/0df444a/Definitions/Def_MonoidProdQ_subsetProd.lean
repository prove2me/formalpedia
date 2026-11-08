-- Prove2me | Definitions.Def_MonoidProdQ_subsetProd
-- name    : MonoidProdQ_subsetProd
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T04:44:58.176995+00:00
-- url     : https://prove2.me/theorems/329b31af-1b6c-498f-89c1-8085ff98156b
-- title:
--   Subset product $p_x(T)$
-- statement:
--   Let $M$ be a commutative monoid, $G\subseteq M$ and $x=x_1\cdots x_s\in G^s$. For $T\subseteq[s]$ put
--
--   $$p_x(T)=\prod_{i\in T}x_i,$$
--
--   with the empty product equal to the identity. Because $M$ is commutative the product over a set is well defined; $T\mapsto p_x(T)$ is the **subset-product summary**, with update $\delta(p,a)=pa$ and final state the product of the whole word.
-- source:
--   Lee–Santha, The quantum query complexity of the semigroup product problem, arXiv:2609.39974 (held version, sha256 9eec405d…ffb6), §5.1, Eq. (15), p.33

import Mathlib

namespace MonoidProdQ

/-- Lee–Santha, *The quantum query complexity of the semigroup product problem*,
arXiv:2609.39974 (held version, sha256 9eec405d…ffb6), §5.1, Eq. (15), p.33: for a word `x ∈ G^s` and `T ⊆ [s]`,
`pₓ(T) = ∏_{i ∈ T} xᵢ`; "The empty product is the identity." Defined for a commutative monoid
(Section 5's standing assumption), where the product over a set needs no order. Positions are
`Fin s`. -/
def subsetProd {M : Type*} [CommMonoid M] {G : Finset M} {s : ℕ} (x : Fin s → G)
    (T : Finset (Fin s)) : M :=
  ∏ i ∈ T, (x i : M)

end MonoidProdQ


