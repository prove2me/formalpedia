-- Prove2me | Definitions.Def_NeebLieExt_twistedBracket
-- name    : NeebLieExt_twistedBracket
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T17:17:24.342435+00:00
-- url     : https://prove2.me/theorems/ea54efc5-1d92-4534-9e10-a044a6ad379c
-- title:
--   The twisted bracket (2.1) on $\mathfrak n\times\mathfrak g$
-- statement:
--   For a linear map $S\colon\mathfrak g\to\operatorname{der}\mathfrak n$ and $\omega\colon\mathfrak g\times\mathfrak g\to\mathfrak n$, the **twisted bracket** on $\mathfrak n\times\mathfrak g$ is
--   $$
--   [(n,x),(n',x')]:=\big([n,n']+S(x).n'-S(x').n+\omega(x,x'),\ [x,x']\big).
--   $$
--   The space $\mathfrak n\times\mathfrak g$ with the product topology and this bracket is denoted $\mathfrak n\times_{(S,\omega)}\mathfrak g$.
--
--   Every topologically split extension of $\mathfrak g$ by $\mathfrak n$ is isomorphic to such a twisted product, and for a continuous factor system $(S,\omega)$ the bracket is a continuous Lie bracket (Lemma II.4).
--
--   **Formalization Note** The twisted bracket is a function `n × g → n × g → n × g`. Mathlib's own bracket on `n × g` is the direct product, i.e. the case $S=0$, $\omega=0$, and is never used for twisted products.
-- source:
--   Neeb, Non-abelian extensions of topological Lie algebras, arXiv:math/0411256v1, (2.1), p. 10

import Mathlib

namespace NeebLieExt

/-- **The twisted bracket (2.1) on `n × g`**. Neeb, arXiv:math/0411256v1, (2.1), p. 10:
"[(n, x), (n′, x′)] := ([n, n′] + S(x).n′ − S(x′).n + ω(x, x′), [x, x′])."

For a linear `S : g → der n` and `ω : g → g → n`,
`twistedBracket S ω (a, x) (a', x') = (⁅a, a'⁆ + S(x).a' − S(x').a + ω(x, x'), ⁅x, x'⁆)`. With this
bracket `n × g` is the Lie algebra `n ×_(S,ω) g` of Lemma II.4.

**Formalization Note** Mathlib's own `⁅·, ·⁆` on `n × g` is the direct-product bracket, i.e. the
case `S = 0`, `ω = 0`; every bracket on pairs in this development is `twistedBracket S ω`, and the
topology on `n × g` is the product topology. -/
def twistedBracket {K g n : Type*} [CommRing K] [LieRing g] [LieAlgebra K g] [LieRing n]
    [LieAlgebra K n] (S : g →ₗ[K] LieDerivation K n n) (ω : g → g → n) (p p' : n × g) : n × g :=
  (⁅p.1, p'.1⁆ + S p.2 p'.1 - S p'.2 p.1 + ω p.2 p'.2, ⁅p.2, p'.2⁆)

end NeebLieExt


