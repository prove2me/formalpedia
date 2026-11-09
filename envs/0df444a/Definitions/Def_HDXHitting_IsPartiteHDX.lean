-- Prove2me | Definitions.Def_HDXHitting_IsPartiteHDX
-- name    : HDXHitting_IsPartiteHDX
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:57:56.629334+00:00
-- url     : https://prove2.me/theorems/d407c776-a6d1-4baf-a0eb-c69e771c17f0
-- title:
--   $d$-partite $\lambda$-HDX
-- statement:
--   Let a complex with top distribution $p$ be partite with colouring $c$ and colour set $S$. It is a **$d$-partite $\lambda$-HDX** if for every pair of colours $i\ne j$ in $S$ and every face $\tau$ with no vertex of colour $i$ or $j$, the bipartite graph
--   $$
--   \big(X^i_\tau(1)\sqcup X^j_\tau(1),\ X^{\{i,j\}}_\tau(2)\big)
--   $$
--   between the colour-$i$ and colour-$j$ vertices of the link of $\tau$, with weights $W_\tau(u,w)$ for $c(u)=i$, $c(w)=j$, has second singular value at most $\lambda$.
--
--   **Formalization Note** The condition is imposed for all vertex sets $\tau$ of every size, including $\tau=\emptyset$; for a non-face all weights vanish.
-- source:
--   Bafna–Tjowasi, A Hitting Set Lemma for HDX & Applications, STOC 2027 submission (manuscript sha256 60d23b0d…), Definition 2.2, p.13

import Mathlib
import Definitions.Def_HDXHitting_linkWeight
import Definitions.Def_HDXHitting_BipSingLE

namespace HDXHitting

/-- Definition 2.2 (Bafna–Tjowasi, *A Hitting Set Lemma for HDX & Applications*, STOC 2027 submission manuscript (sha256 60d23b0d…e56d3), p.13), partite part: a `d`-partite complex (coloured by `c`
with colour set `S`) is a **`d`-partite `λ`-HDX** if for every pair of colours `i ≠ j` in `S`
and every face `τ` with no vertex of colour `i` or `j`, the bipartite graph
`(X^i_τ(1) ⊔ X^j_τ(1), X^{i,j}_τ(2))` between the colour-`i` and colour-`j` vertices of the link
of `τ` has second singular value at most `λ`.

**Formalization Note** The bipartite weights are the link weights `linkWeight p τ u w`
restricted to `c u = i`, `c w = j`. The quantifier runs over all sets `τ` of every size
(including `∅`); for a non-face all weights vanish. -/
def IsPartiteHDX {V ι : Type*} [Fintype V] [DecidableEq V] [DecidableEq ι] (p : Finset V → ℝ) (c : V → ι)
    (S : Finset ι) (lam : ℝ) : Prop :=
  ∀ i ∈ S, ∀ j ∈ S, i ≠ j → ∀ τ : Finset V, (∀ v ∈ τ, c v ≠ i ∧ c v ≠ j) →
    BipSingLE (fun u w => if c u = i ∧ c w = j then linkWeight p τ u w else 0) lam

end HDXHitting


