-- Prove2me | Definitions.Def_BergeMatching_Core_Arrows
-- name    : BergeMatching_Core_Arrows
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T19:06:53.854771+00:00
-- url     : https://prove2.me/theorems/c10d1916-f174-48a5-b45c-81a0740cbef0
-- title:
--   The graph $\bar G$, arrows, and the classes $I$, $W$, $S$ and medium points
-- statement:
--   Let $G = (X, U)$ be a finite simple graph with a matching $V_0$, strong edges $V_0$, weak edges $U \setminus V_0$, and neutral points $N$.
--
--   1. The graph $\bar G$ is obtained from $G$ by adding a new vertex $\bar a$ and joining $\bar a$ to every neutral point. The **strong edges of $\bar G$** are the edges of $V_0$ together with all edges $\bar a n$, $n \in N$; every other edge of $\bar G$ is weak.
--   2. If there is an alternating chain of $\bar G$ (with respect to its strong edges) from $\bar a$ to a vertex $x$, with at least one edge, whose last edge is $(z, x)$, we draw an **arrow** on the edge $(z, x)$, directed from $z$ to $x$.
--   3. **$\bar a$ is inaccessible** if no arrow is directed to $\bar a$.
--   4. A vertex $x \notin N$ is **inaccessible** if no edge at $x$ carries an arrow (in either direction); the set of these is $I$.
--   5. A vertex $x \notin N$ is **weak** if some weak edge carries an arrow directed to $x$ and no strong edge does; the set of these is $W$.
--   6. A vertex $x \notin N$ is **strong** if some strong edge carries an arrow directed to $x$ and no weak edge does; the set of these is $S$.
--   7. A vertex $x \notin N$ is **medium** if some strong edge and some weak edge carry arrows directed to $x$. The paper calls this set $M$.
--
--   These labels are the bookkeeping of Berge's proof that a matching with no alternating chain between two neutral points is maximum, and of Gallai's lemma on the structure of the medium points.
--
--   **Formalization Note** $\bar G$ is a `SimpleGraph (Option V)` with $\bar a$ = `none`. An arrow requires a walk of positive length, so the trivial walk at $\bar a$ gives no arrow. The paper defines "$\bar a$ is inaccessible" only through the general phrase "not adjacent to a directed edge", which, read literally, fails for $\bar a$ whenever $N \neq \emptyset$ (every edge $\bar a n$ carries the arrow $\bar a \to n$); it is formalized as "no arrow is directed to $\bar a$", which is equivalent to the absence of an alternating chain of $G$ between two distinct neutral points, the condition of Theorem 1. In Lean the medium class is `IsMedium`, because the letter `M` names the matching.
-- source:
--   Berge, Two theorems in graph theory, Proc. Natl. Acad. Sci. USA 43 (1957), pp. 842–843, The Theorems, second paragraph (the graph Ḡ, arrows, classes I, W, S, M)

import Mathlib
import Definitions.Def_BergeMatching_Core_AlternatingChain

namespace BergeMatching.Core

/-- Adjacency of the graph `Ḡ` (p. 842) on `Option V`, where `none` is the added vertex `ā`:
two vertices of `G` are adjacent as in `G`, `ā` is adjacent exactly to the neutral points, and
`ā` has no loop. -/
def barAdj {V : Type} (G : SimpleGraph V) (M : G.Subgraph) : Option V → Option V → Prop
  | some u, some v => G.Adj u v
  | none, some n => IsNeutral M n
  | some n, none => IsNeutral M n
  | none, none => False

/-- The graph `Ḡ` (p. 842): `G` together with a new vertex `ā = none` joined to every neutral
point. -/
def barGraph {V : Type} (G : SimpleGraph V) (M : G.Subgraph) : SimpleGraph (Option V) where
  Adj := barAdj G M
  symm := ⟨fun a b h => by
    cases a <;> cases b <;> simp_all [barAdj, G.adj_comm]⟩
  loopless := ⟨fun a h => by
    cases a <;> simp_all [barAdj]⟩

/-- The strong edges of `Ḡ` (p. 842): the edges of the matching `M`, and the edges joining `ā`
to the neutral points. Every other edge of `Ḡ` is weak. -/
def barStrong {V : Type} {G : SimpleGraph V} (M : G.Subgraph) : Set (Sym2 (Option V)) :=
  Sym2.map some '' M.edgeSet ∪ {e | ∃ n, IsNeutral M n ∧ e = s(none, some n)}

/-- The arrow on the edge `(z, x)` of `Ḡ`, directed from `z` to `x` (p. 842): there is an
alternating chain of `Ḡ` (with respect to `barStrong M`) from `ā` to `x` with at least one edge,
whose last edge is `(z, x)`. -/
def Arrow {V : Type} (G : SimpleGraph V) (M : G.Subgraph) (z x : Option V) : Prop :=
  ∃ p : (barGraph G M).Walk none x,
    IsAlternatingWrt (barStrong M) p ∧ p.length ≠ 0 ∧ p.penultimate = z

/-- "`ā` is inaccessible" (pp. 842–843), read as: no arrow is directed to `ā`. -/
def AbarInaccessible {V : Type} (G : SimpleGraph V) (M : G.Subgraph) : Prop :=
  ∀ z : Option V, ¬ Arrow G M z none

/-- An *inaccessible* point (p. 842): a non-neutral vertex `x` not adjacent to a directed edge,
i.e. no edge at `x` carries an arrow in either direction. The set of these is `I`. -/
def IsInaccessible {V : Type} (G : SimpleGraph V) (M : G.Subgraph) (x : V) : Prop :=
  ¬ IsNeutral M x ∧ ∀ y : Option V, ¬ Arrow G M y (some x) ∧ ¬ Arrow G M (some x) y

/-- A *weak* point (p. 842): a non-neutral vertex `x` adjacent to a weak edge directed to `x`
and not to a strong edge directed to `x`. The set of these is `W`. -/
def IsWeakPt {V : Type} (G : SimpleGraph V) (M : G.Subgraph) (x : V) : Prop :=
  ¬ IsNeutral M x ∧
    (∃ z, Arrow G M z (some x) ∧ s(z, some x) ∉ barStrong M) ∧
    ¬ ∃ z, Arrow G M z (some x) ∧ s(z, some x) ∈ barStrong M

/-- A *strong* point (pp. 842–843): a non-neutral vertex `x` adjacent to a strong edge directed
to `x` and not to a weak edge directed to `x`. The set of these is `S`. -/
def IsStrongPt {V : Type} (G : SimpleGraph V) (M : G.Subgraph) (x : V) : Prop :=
  ¬ IsNeutral M x ∧
    (∃ z, Arrow G M z (some x) ∧ s(z, some x) ∈ barStrong M) ∧
    ¬ ∃ z, Arrow G M z (some x) ∧ s(z, some x) ∉ barStrong M

/-- A *medium* point (p. 843): a non-neutral vertex `x` adjacent to a strong edge directed to `x`
and to a weak edge directed to `x`. The paper calls the set of these `M`; here `M` is the
matching, so the class is `IsMedium`. -/
def IsMedium {V : Type} (G : SimpleGraph V) (M : G.Subgraph) (x : V) : Prop :=
  ¬ IsNeutral M x ∧
    (∃ z, Arrow G M z (some x) ∧ s(z, some x) ∈ barStrong M) ∧
    (∃ z, Arrow G M z (some x) ∧ s(z, some x) ∉ barStrong M)

end BergeMatching.Core


