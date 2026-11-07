-- Prove2me | Definitions.Def_ImplicitParityWL_WLColor
-- name    : ImplicitParityWL_WLColor
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:10:30.969417+00:00
-- url     : https://prove2.me/theorems/44a1e035-afc6-4ec0-86ae-ee8b22a8a007
-- title:
--   The $k$-WL coloring $\chi^{(r)}_k[G]$ and first distinguishing round
-- statement:
--   Fix $k$ and a colored graph $G$. For $\bar p=(p_1,\dots,p_k)\in V(G)^k$ and $q\in V(G)$, let $\bar p[q/i]$ be $\bar p$ with its $i$-th entry replaced by $q$. The **$k$-dimensional Weisfeiler–Leman algorithm** computes colorings of $V(G)^k$ by
--   $$
--   \chi^{(0)}_k[G](\bar p)=\mathrm{atp}_G(\bar p),\qquad
--   \chi^{(r+1)}_k[G](\bar p)=\Bigl(\chi^{(r)}_k[G](\bar p),\ \bigl\{\!\!\bigl\{\bigl(\chi^{(r)}_k[G](\bar p[q/1]),\dots,\chi^{(r)}_k[G](\bar p[q/k])\bigr) : q\in V(G)\bigr\}\!\!\bigr\}\Bigr),
--   $$
--   where the atomic type records the equalities, the adjacencies and the colors of the entries. Colors are syntactic, so they can be compared across graphs.
--
--   $k$-WL **distinguishes** $G$ and $H$ after $r$ rounds if some color occurs a different number of times among the $k$-tuples of $G$ and of $H$. The graphs are **first distinguished** after $T$ rounds if $T$ is the least such number.
--
--   This is the joint update: one multiset of whole $k$-vectors over $q$. The update with a separate multiset per coordinate is a different algorithm with a different dimension.
--
--   **Formalization Note** Distinguishing is the inequality of the two multisets of colors, and two multisets differ exactly when some element has different multiplicities.
-- source:
--   Curticapean, Liu, Neuen, Seppelt, Lower Bounds for the Weisfeiler–Leman Algorithm via Implicit Parity Systems (STOC 2027 submission, manuscript of November 3, 2026, sha256 6604ccc9…), §3, pp.14–15

import Mathlib
import Definitions.Def_ImplicitParityWL_ColoredGraph
universe u

namespace ImplicitParityWL

/-- The syntactic colors of the `k`-dimensional Weisfeiler–Leman algorithm at round `r`
(Curticapean, Liu, Neuen, Seppelt, *Lower Bounds for the Weisfeiler–Leman Algorithm via Implicit
Parity Systems*, manuscript of November 3, 2026, §3, pp.14–15): round `0` records the atomic type
(the equality and adjacency pattern and the colors of the entries); round `r + 1` is a pair of a
round-`r` color and a multiset of `k`-vectors of round-`r` colors.

**Formalization Note** Colors live in one type for all graphs over `K`, which is the page's
"colors of tuples in different graphs can be compared". -/
def WLColor (K : Type u) (k : ℕ) : ℕ → Type u
  | 0 => (Fin k → Fin k → Bool × Bool) × (Fin k → K)
  | r + 1 => WLColor K k r × Multiset (Fin k → WLColor K k r)

/-- The coloring `χ⁽ʳ⁾ₖ[G]` of `V(G)ᵏ` (§3, p.14): `χ⁽⁰⁾ₖ[G](p̄) = atp_G(p̄)` and
`χ⁽ʳ⁺¹⁾ₖ[G](p̄) = (χ⁽ʳ⁾ₖ[G](p̄), {{(χ⁽ʳ⁾ₖ[G](p̄[q/1]), …, χ⁽ʳ⁾ₖ[G](p̄[q/k])) : q ∈ V(G)}})`.

**Formalization Note** This is the joint ("folklore") update: one multiset of whole `k`-vectors,
indexed by `q`. `p̄[q/i]` is `Function.update p i q`. -/
noncomputable def color {K : Type u} {V : Type*} [Fintype V] (G : ColoredGraph K V) (k : ℕ) :
    (r : ℕ) → (Fin k → V) → WLColor K k r
  | 0, p => by
      classical
      exact (fun i j => (decide (p i = p j), decide (G.graph.Adj (p i) (p j))), fun i => G.χ (p i))
  | r + 1, p => (color G k r p,
      Finset.univ.val.map (fun q => fun i => color G k r (Function.update p i q)))

/-- The multiset of round-`r` colors of all `k`-tuples of `G`. -/
noncomputable def histogram {K : Type u} {V : Type*} [Fintype V] (G : ColoredGraph K V)
    (k r : ℕ) : Multiset (WLColor K k r) :=
  Finset.univ.val.map (color G k r)

/-- `k`-WL **distinguishes `G` and `H` after `r` rounds** (§3, p.15): some color occurs a different
number of times among the `k`-tuples of `G` and of `H`.

**Formalization Note** Two multisets differ exactly when some element has different multiplicities,
so the inequality of the histograms is the page's condition. -/
def DistinguishesAfter {K : Type u} {V W : Type*} [Fintype V] [Fintype W]
    (G : ColoredGraph K V) (H : ColoredGraph K W) (k r : ℕ) : Prop :=
  histogram G k r ≠ histogram H k r

/-- `G` and `H` are **first distinguished after `T` rounds** (§3, p.15): `T` is the least number of
rounds after which `k`-WL distinguishes them. -/
def FirstDistinguishedAt {K : Type u} {V W : Type*} [Fintype V] [Fintype W]
    (G : ColoredGraph K V) (H : ColoredGraph K W) (k T : ℕ) : Prop :=
  DistinguishesAfter G H k T ∧ ∀ r < T, ¬ DistinguishesAfter G H k r

end ImplicitParityWL


