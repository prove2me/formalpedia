-- Prove2me | Definitions.Def_NashWilliams61_TreePacking_Couples
-- name    : NashWilliams61_TreePacking_Couples
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T15:27:41.85682+00:00
-- url     : https://prove2.me/theorems/9d0794f1-c6ba-42c6-bf99-1ac2a967e8f4
-- title:
--   Couples $[G,g]$, $s$-good couples, $s$-supercouples and $\Gamma(X)$ (p. 446)
-- statement:
--   Fix a positive integer $k$ and a graph $G$ with vertex set $V$. For a function $f$ on $V$ and $S \subseteq V$ write $f\,.\,S = \sum_{\xi \in S} f(\xi)$, and write $\bar X = V \setminus X$.
--
--   1. **Couple.** $[G, g]$ is a *couple* if $g$ is a non-negative integer-valued function on $V$ and $\Delta_G(X) \ge 0$ for every non-empty $X \subseteq V$.
--   2. **$s$-good.** For a non-negative integer $s$, the couple $[G, g]$ is *$s$-good* if $g\,.\,V > 2s$ and
--   $$\Delta_G(X) \ge s - g\,.\,\bar X \quad \text{for every non-empty } X \subseteq V,$$
--   including $X = V$.
--   3. **$\Gamma$.** $\Gamma(X) = \Delta_G(X) - s + g\,.\,\bar X$ (display (2) of the paper).
--   4. **$s$-supercouple.** A couple $[H, h]$ is an *$s$-supercouple* of $[G, g]$ if $G$ is a spanning subgraph of $H$, $H$ has exactly $s$ edges not in $G$, and each vertex $\xi$ is incident in $H$ with exactly $g(\xi) - h(\xi)$ of these new edges.
--
--   Couples and supercouples are the device by which the paper reduces the vertex-deletion step of its induction to adding $s$ edges among the neighbours of a deleted vertex.
--
--   **Formalization Note** $g, h$ take values in $\mathbb N$ and all sums are in $\mathbb Z$. The supergraph $H$ has vertex type $V$ and edge type $E \oplus \mathrm{Fin}\, s$, the new edge $i$ having ends $a_i$; this builds in "$G$ is a spanning subgraph of $H$ and $|E(H) - E(G)| = s$" and guarantees that fresh edges exist. No new edge may be a loop (so $H$ is a graph in the paper's sense). "Exactly $g(\xi) - h(\xi)$" is written $\deg_{\text{new}}(\xi) + h(\xi) = g(\xi)$, with no natural-number subtraction. The paper's "$X \subset V(G)$" includes $X = V(G)$ and is read as $\subseteq$.
-- source:
--   Nash-Williams, Edge-disjoint spanning trees of finite graphs, J. London Math. Soc. 36 (1961), p. 446, Definitions (couple, s-good, s-supercouple) and Eq. (2)

import Mathlib
import Definitions.Def_NagamochiIbaraki_EdgeConn_Multigraph
import Definitions.Def_NashWilliams61_TreePacking_Graphs

namespace NashWilliams61.TreePacking

/-! Couples, `s`-good couples, `s`-supercouples and the function `Γ` of (2)
(Nash-Williams 1961, p. 446).

Throughout, `f . S = ∑_{ξ ∈ S} f(ξ)` and `X̄ = V(G) − X = Finset.univ \ X`; all arithmetic is
in `ℤ`. A supergraph `H` of `G` with `s` new edges is encoded on the same vertex type `V`
with edge type `E ⊕ Fin s` and ends `Sum.elim ends a`, where `a : Fin s → Sym2 V` lists the
ends of the new edges; `G` is then a spanning subgraph of `H` and `|E(H) − E(G)| = s`. -/

open NagamochiIbaraki.EdgeConn

variable {V E : Type*}

/-- `[G, g]` is a couple: `g` is a non-negative integer-valued function on `V(G)` (here
`g : V → ℕ`) and `Δ_G(X) ≥ 0` for every non-empty `X ⊆ V(G)`. -/
def IsCouple [Fintype E] (k : ℕ) (ends : E → Sym2 V) (_g : V → ℕ) : Prop :=
  ∀ X : Finset V, X.Nonempty → 0 ≤ Delta k ends X

/-- The couple `[G, g]` is `s`-good: it is a couple, `g . V(G) > 2s`, and
`Δ_G(X) ≥ s − g . X̄` for every non-empty `X ⊆ V(G)` (`X = V(G)` included). -/
def IsGood [Fintype V] [DecidableEq V] [Fintype E] (k : ℕ) (ends : E → Sym2 V) (g : V → ℕ)
    (s : ℕ) : Prop :=
  IsCouple k ends g ∧ 2 * (s : ℤ) < ∑ v, (g v : ℤ) ∧
    ∀ X : Finset V, X.Nonempty → (s : ℤ) - ∑ v ∈ Finset.univ \ X, (g v : ℤ) ≤ Delta k ends X

/-- `Γ(X) = Δ_G(X) − s + g . X̄`, display (2). -/
noncomputable def Gamma [Fintype V] [DecidableEq V] [Fintype E] (k : ℕ) (ends : E → Sym2 V)
    (g : V → ℕ) (s : ℕ) (X : Finset V) : ℤ :=
  Delta k ends X - (s : ℤ) + ∑ v ∈ Finset.univ \ X, (g v : ℤ)

/-- `[H, h]` is an `s`-supercouple of the couple `[G, g]`, where `H` is `G` plus the `s` new
edges with ends `a i` (edge type `E ⊕ Fin s`, ends `Sum.elim ends a`): no new edge is a loop
(so `H` is a graph), `[H, h]` is a couple, and every vertex `ξ` is incident with exactly
`g(ξ) − h(ξ)` new edges, written without subtraction as `deg_new(ξ) + h(ξ) = g(ξ)`. -/
def IsSupercouple [Fintype V] [DecidableEq V] [Fintype E] {s : ℕ} (k : ℕ)
    (ends : E → Sym2 V) (g : V → ℕ) (a : Fin s → Sym2 V) (h : V → ℕ) : Prop :=
  (∀ i, ¬ (a i).IsDiag) ∧ IsCouple k (Sum.elim ends a) h ∧
    ∀ v : V, degIn a Finset.univ v + h v = g v

end NashWilliams61.TreePacking


