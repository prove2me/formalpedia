-- Prove2me | Definitions.Def_SFLOracleLowerBound_Hardness_MatchingGraph
-- name    : SFLOracleLowerBound_Hardness_MatchingGraph
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T02:25:55.082214+00:00
-- url     : https://prove2.me/theorems/8fa0549d-f31c-43f1-b260-0ed0eae47012
-- title:
--   Matching-decomposed bipartite multigraph and truncated path metric
-- statement:
--   A graph on two disjoint sides of size $m$ is specified by $d$ perfect matchings $M_a$, each a bijection from the right side to the left. Equal endpoints at different colours remain distinct multiedges. The neighborhood of a right set $V$ is $N_G(V)=\bigcup_a M_a(V)$, and
--   $$
--   \tau(U)=\min\{|V|:U\subseteq N_G(V)\},\quad K=d^{d+3},\quad m=K^2.
--   $$
--   Local expansion means $|N_G(V)|\ge(d-2)|V|$ for $|V|\le2K$. For base vertices $x,y$ in the disjoint union, let $h(x,y)$ be the shortest number of edges of a path, and $+\infty$ if no path exists. Set
--   $$
--   \operatorname{dist}(x,y)=\min\{1,h(x,y)/d\}.
--   $$
--   A one-vertex path has length zero, and disconnected pairs have distance one for positive $d$. These definitions retain multiplicities for the graph while using ordinary neighborhoods and paths where multiplicity has no effect. Cover minima are used only at $d\ge4$, where every left vertex has a neighbor.
-- source:
--   Adam N. Elmachtoub, Bento Natura, Meike Neuwohner, Settling the Approximability of Submodular Facility Location, STOC 2027 submission #1249 (October 2026), §4.1.1, p.17; Lemma 19, p.18; Definition 24, pp.23–24; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1249.pdf

import Mathlib
import Definitions.Def_SFLOracleLowerBound_Hardness_SetFunctions

set_option autoImplicit false

noncomputable section

namespace SFLOracleLowerBound.Hardness

open Classical Finset MeasureTheory
open scoped ENNReal

/-- §4.1: a matching-decomposed regular bipartite multigraph.
Each colour is one perfect matching from the right side to the left side.
Equal endpoints at different colours remain distinct edges. -/
abbrev MatchingGraph (d m : ℕ) := Fin d → Equiv.Perm (Fin m)

def baseNeighbors {d m : ℕ} (M : MatchingGraph d m) (V : Finset (Fin m)) : Finset (Fin m) :=
  univ.biUnion (fun a => V.image (M a))

/-- §4.1.1 p.17. d>0 ensures a cover of every U exists. -/
def coverNumber {d m : ℕ} (M : MatchingGraph d m) (U : Finset (Fin m)) : ℕ :=
  sInf {k : ℕ | ∃ V : Finset (Fin m), U ⊆ baseNeighbors M V ∧ V.card = k}

def graphCap (d : ℕ) : ℕ := d^(d+3)
def graphSize (d : ℕ) : ℕ := (graphCap d)^2

def BaseExpansion {d m : ℕ} (M : MatchingGraph d m) (K : ℕ) : Prop :=
  ∀ V : Finset (Fin m), V.card ≤ 2*K →
    ((d : ℤ)-2) * V.card ≤ (baseNeighbors M V).card

/-- Adjacency forgets multiplicity only when computing neighborhoods and paths. -/
def baseAdjacent {d m : ℕ} (M : MatchingGraph d m) : Sum (Fin m) (Fin m) → Sum (Fin m) (Fin m) → Prop
  | .inl u, .inr v => ∃ a, M a v = u
  | .inr v, .inl u => ∃ a, M a v = u
  | _, _ => False

/-- Shortest-path length, +∞ when disconnected, realized in ℝ≥0∞. -/
def graphDistance {d m : ℕ} (M : MatchingGraph d m)
    (x y : Sum (Fin m) (Fin m)) : ℝ≥0∞ :=
  ⨅ p : {p : List (Sum (Fin m) (Fin m)) //
    p.head? = some x ∧ p.getLast? = some y ∧ p.IsChain (baseAdjacent M)},
    ((p.val.length - 1 : ℕ) : ℝ≥0∞)

/-- Definition 24: disconnected pairs are sent to 1, never to a default zero. -/
def baseDistance {d m : ℕ} (M : MatchingGraph d m)
    (x y : Sum (Fin m) (Fin m)) : ℝ≥0∞ := min 1 (graphDistance M x y / d)

end SFLOracleLowerBound.Hardness


