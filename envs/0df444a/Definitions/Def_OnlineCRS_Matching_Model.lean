-- Prove2me | Definitions.Def_OnlineCRS_Matching_Model
-- name    : OnlineCRS_Matching_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T20:21:28.245733+00:00
-- url     : https://prove2.me/theorems/80d4a045-c25a-40b9-b2d3-df4c2ae633ea
-- title:
--   §2.2 and proof of Theorem 2.7, p. 13 — degree relaxation P_G and the random-K greedy OCRS
-- statement:
--   Let $G=(V,E)$ be a finite graph without loops (parallel edges allowed), and for a node $u$ let $\delta(u)$ be the set of edges incident to $u$.
--
--   1. The **degree relaxation** of matching is
--   $$P_G=\Big\{x\in\mathbb R^E:\ \sum_{g\in\delta(u)}x_g\le1\ \ \forall u\in V,\quad x_g\ge0\ \ \forall g\in E\Big\}.$$
--   2. The **inclusion probability** of an edge is $q_g(x)=(1-e^{-x_g})/x_g$ for $x_g>0$ and $q_g(x)=1$ for $x_g=0$ (the limit).
--   3. For a set $K\subseteq E$ of **potential edges**, $\mathcal F_{K}$ is the family of all matchings $I\subseteq K$.
--   4. The **random-$K$ scheme** draws $K$ by putting every edge $g$ into $K$ independently with probability $q_g(x)$ and uses the family $\mathcal F_K$; its weight on a family $\mathcal F$ is $\Pr[\mathcal F_K=\mathcal F]$.
--   5. For an edge $g'$ with ends $u,v$, $D(g')=(\delta(u)\cup\delta(v))\setminus\{g'\}$ is the set of the other edges meeting $g'$.
--
--   These are the objects of the proof of Theorem 2.7: the scheme of item 4 is the one shown there to be $(b,e^{-2b})$-selectable.
--
--   **Formalization Note** The graph and the matching predicate are the published `EdmondsMatching65.Polyhedron.Graph` and `IsMatching`. The paper's ratio $(1-e^{-x_g})/x_g$ would evaluate to $0$ at $x_g=0$ in Lean, so $q$ is given its limit value $1$ there; for negative $x_g$, which never occurs for $x\in bP_G$ with $b\ge0$, $q$ is also set to $1$, so that the weight map is a probability distribution for every input vector, as the definition of a randomized greedy OCRS requires.
-- source:
--   arXiv:1508.00142v2, §2.2, p. 13 (definition of P_G) and proof of Theorem 2.7, p. 13, first paragraph

import Mathlib
import Definitions.Def_OnlineCRS_Matroid_Basics
import Definitions.Def_EdmondsMatching65_Polyhedron_Graph

namespace OnlineCRS.Matching

/-- The edges incident to a vertex in a finite loopless multigraph (§2.2, p. 13). -/
noncomputable def edgeStar {V E : Type} [Fintype E] [DecidableEq E]
    (G : EdmondsMatching65.Polyhedron.Graph V E) (u : V) : Finset E := by
  classical
  exact Finset.univ.filter (fun g => u ∈ G.ends g)

/-- The degree relaxation `P_G` (§2.2, p. 13). -/
def matchingRelax {V E : Type} [Fintype E] [DecidableEq E]
    (G : EdmondsMatching65.Polyhedron.Graph V E) : Set (E → ℝ) :=
  {x | (∀ g, 0 ≤ x g) ∧ ∀ u, ∑ g ∈ edgeStar G u, x g ≤ 1}

/-- The inclusion probability of an edge in the independently sampled set `K`.
The continuous value at zero is one. Outside the nonnegative domain the value is set to one,
so the resulting random family remains a distribution for every input. -/
noncomputable def incl {E : Type} (x : E → ℝ) (g : E) : ℝ :=
  if 0 ≤ x g then
    if x g = 0 then 1 else (1 - Real.exp (-x g)) / x g
  else 1

/-- For a sampled `K`, the greedy family consists of its matching subsets (§2.2, p. 13). -/
noncomputable def famK {V E : Type} [Fintype E] [DecidableEq E]
    (G : EdmondsMatching65.Polyhedron.Graph V E) (K : Finset E) : Finset (Finset E) := by
  classical
  exact Finset.univ.filter (fun I => I ⊆ K ∧ EdmondsMatching65.Polyhedron.IsMatching G I)

/-- The randomized greedy OCRS of the proof of Theorem 2.7. -/
noncomputable def ocrsWeight {V E : Type} [Fintype E] [DecidableEq E]
    (G : EdmondsMatching65.Polyhedron.Graph V E) (x : E → ℝ) (Fam : Finset (Finset E)) : ℝ :=
  ∑ K : Finset E, OnlineCRS.Matroid.activeProb (incl x) K * if famK G K = Fam then 1 else 0

/-- The other edges incident to either endpoint of `g` (§2.2, p. 13). -/
noncomputable def otherIncident {V E : Type} [Fintype E] [DecidableEq E]
    (G : EdmondsMatching65.Polyhedron.Graph V E) (u v : V) (g : E) : Finset E :=
  (edgeStar G u ∪ edgeStar G v) \ {g}

end OnlineCRS.Matching


