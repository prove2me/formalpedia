-- Prove2me | Definitions.Def_MonoidProdQ_prodMap
-- name    : MonoidProdQ_prodMap
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T04:41:43.14506+00:00
-- url     : https://prove2.me/theorems/2b5d540f-098e-4a04-a098-2ae1a4f60005
-- title:
--   Ordered product map $\mathrm{Prod}_{M,G,n}$
-- statement:
--   Let $M$ be a monoid, $G\subseteq M$ the allowed alphabet and $n\ge 0$. The **product map** sends an input word $x=x_1x_2\cdots x_n\in G^n$ to the ordered product
--
--   $$\mathrm{Prod}_{M,G,n}(x)=x_1x_2\cdots x_n\in M.$$
--
--   It is the function whose quantum query complexity the mission studies: an algorithm may query any position $i$ and learn the whole letter $x_i$.
--
--   **Formalization Note** Positions are indexed by $\{0,\dots,n-1\}$ and letters are elements of the subtype of $M$ determined by $G$. The product is taken in index order; commutativity of $M$ is a hypothesis of the statements, not part of the definition.
-- source:
--   Lee–Santha, The quantum query complexity of the semigroup product problem, arXiv:2609.39974 (held version, sha256 9eec405d…ffb6), §3, Query model, p.21

import Mathlib

namespace MonoidProdQ

/-- Lee–Santha, *The quantum query complexity of the semigroup product problem*,
arXiv:2609.39974 (held version, sha256 9eec405d…ffb6), §3, "Query model", p.21: "We write Prod_{S,G,n} : Gⁿ → S for the ordered product
map over an allowed alphabet G ⊆ S": the input `x = x₁ ⋯ xₙ ∈ Gⁿ` is mapped to `x₁ x₂ ⋯ xₙ`.

**Formalization Note.** Positions are `Fin n` (position `i` is the paper's `i + 1`), letters are
elements of the subtype `↥G`, and the product is taken in index order (`List.ofFn`), as printed;
commutativity of `M` is a hypothesis of the statements, not part of the definition. -/
def prodMap {M : Type*} [Monoid M] (G : Finset M) (n : ℕ) : (Fin n → G) → M :=
  fun x => (List.ofFn fun i => (x i : M)).prod

end MonoidProdQ


