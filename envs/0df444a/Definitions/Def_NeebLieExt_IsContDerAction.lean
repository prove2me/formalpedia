-- Prove2me | Definitions.Def_NeebLieExt_IsContDerAction
-- name    : NeebLieExt_IsContDerAction
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T17:17:21.868235+00:00
-- url     : https://prove2.me/theorems/cf5bffcf-3254-411e-97d0-611c07ce942b
-- title:
--   Jointly continuous linear maps $S\colon\mathfrak g\to\operatorname{der}\mathfrak n$ ($C^1_c(\mathfrak g,\operatorname{der}\mathfrak n)$)
-- statement:
--   Let $\operatorname{der}\mathfrak n$ be the Lie algebra of derivations of $\mathfrak n$. A $\mathbb K$-linear map $S\colon\mathfrak g\to\operatorname{der}\mathfrak n$ belongs to $C^1_c(\mathfrak g,\operatorname{der}\mathfrak n)$ if the map
--   $$
--   \mathfrak g\times\mathfrak n\to\mathfrak n,\qquad (x,m)\mapsto S(x).m
--   $$
--   is continuous.
--
--   These are the candidates for outer actions of $\mathfrak g$ on $\mathfrak n$; the gauge group $C^1(\mathfrak g,\mathfrak n)$ acts on them by $S\mapsto S+\operatorname{ad}\circ\gamma$.
--
--   **Formalization Note** $S$ is a linear map into Mathlib's `LieDerivation K n n` (all derivations). Joint continuity forces each $S(x)$ to be continuous, so $S$ takes values in the continuous derivations, which is the paper's $\operatorname{der}\mathfrak n$.
-- source:
--   Neeb, Non-abelian extensions of topological Lie algebras, arXiv:math/0411256v1, Definition II.2, p. 11 ("a linear map S: g → der n for which the bilinear map g × n → n, (x, n) ↦ S(x).n is continuous, i.e., S ∈ C^1_c(g, der n)"); covariant differentials, p. 6

import Mathlib

namespace NeebLieExt

/-- **Continuous linear maps into the derivations**, `C¹_c(g, der n)`. Neeb,
arXiv:math/0411256v1, Definition II.2, p. 11: "a linear map S: g → der n for which the bilinear
map g × n → n, (x, n) ↦ S(x).n is continuous, i.e., S ∈ C¹_c(g, der n)"; also p. 6.

For a K-linear map `S : g → der n`, `IsContDerAction S` says that `(x, m) ↦ S(x).m` is jointly
continuous on `g × n`.

**Formalization Note** `S` is a K-linear map into Mathlib's Lie algebra of derivations
`LieDerivation K n n` (all derivations). Joint continuity makes every `S(x)` continuous, so `S`
lands in the continuous derivations `der n` of the paper; `LieDerivation` plus this predicate is
exactly `C¹_c(g, der n)`. -/
def IsContDerAction {K g n : Type*} [CommRing K] [LieRing g] [LieAlgebra K g] [LieRing n]
    [LieAlgebra K n] [TopologicalSpace g] [TopologicalSpace n]
    (S : g →ₗ[K] LieDerivation K n n) : Prop :=
  Continuous fun p : g × n => S p.1 p.2

end NeebLieExt


