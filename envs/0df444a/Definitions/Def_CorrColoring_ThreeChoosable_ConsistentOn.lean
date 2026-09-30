-- Prove2me | Definitions.Def_CorrColoring_ThreeChoosable_ConsistentOn
-- name    : CorrColoring_ThreeChoosable_ConsistentOn
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T01:00:57.404809+00:00
-- url     : https://prove2.me/theorems/78bf2fe0-4400-483f-bb94-8567fa75b2e1
-- title:
--   Consistency of a $k$-correspondence assignment on closed walks
-- statement:
--   Let $C$ be a $k$-correspondence assignment for a graph $G$ and let $W = v_0 v_1 \dots v_m$ with $v_m = v_0$ be a closed walk of length $m$ in $G$. The assignment $C$ is **inconsistent on $W$** if there are colours $c_0, \dots, c_m \in [k]$ such that
--
--   $$(v_i, c_i)(v_{i+1}, c_{i+1}) \in E(C_{v_i v_{i+1}}) \text{ for } i = 0, \dots, m-1, \qquad\text{and}\qquad c_0 \neq c_m .$$
--
--   Otherwise $C$ is **consistent on $W$**. The assignment $C$ is **consistent** if it is consistent on every closed walk of $G$, and **consistent on closed walks of length 3** if it is consistent on every closed walk $W$ of $G$ with $|W| = 3$.
--
--   Following the matchings around a closed walk defines a partial map from colours at $v_0$ back to colours at $v_0$; consistency says this map fixes every colour it is defined on. Consistency characterizes the correspondence assignments that come from list assignments, and consistency on closed walks of length 3 is the hypothesis of the main theorem.
--
--   **Formalization Note** The walk is a Mathlib `G.Walk v v` with vertices `W.getVert i`; the paper's indices $1, \dots, m$ are shifted to $0, \dots, m-1$. Consistency depends on the starting point and direction of the walk (the paper's Figure 1(a) example; a sorry-free check of that example was compiled locally).
-- source:
--   Dvořák, Postle, Correspondence coloring and its application to list-coloring planar graphs without cycles of lengths 4 to 8, arXiv:1508.03437v2, p. 5, definition of (in)consistent on a closed walk and of a consistent correspondence assignment

import Mathlib
import Definitions.Def_CorrColoring_ThreeChoosable_KCorrAssignment

namespace CorrColoring.ThreeChoosable

variable {V : Type*} {G : SimpleGraph V} {k : ℕ}

/-- `C` is inconsistent on the closed walk `W = v₀ v₁ … v_m` (`v_m = v₀`, `m = W.length`) if
there are colours `c₀, …, c_m` with `(v_i, c_i)(v_{i+1}, c_{i+1}) ∈ E(C_{v_i v_{i+1}})` for all
`i < m` and `c₀ ≠ c_m`. -/
def InconsistentOn (C : KCorrAssignment G k) {v : V} (W : G.Walk v v) : Prop :=
  ∃ c : ℕ → Fin k,
    (∀ i < W.length, C.M (W.getVert i) (c i) (W.getVert (i + 1)) (c (i + 1))) ∧
      c 0 ≠ c W.length

/-- `C` is consistent on the closed walk `W`. -/
def ConsistentOn (C : KCorrAssignment G k) {v : V} (W : G.Walk v v) : Prop :=
  ¬ InconsistentOn C W

/-- `C` is consistent: consistent on every closed walk of `G`. -/
def Consistent (C : KCorrAssignment G k) : Prop :=
  ∀ (v : V) (W : G.Walk v v), ConsistentOn C W

/-- `C` is consistent on every closed walk of length 3 of `G`. -/
def ConsistentOnTriangles (C : KCorrAssignment G k) : Prop :=
  ∀ (v : V) (W : G.Walk v v), W.length = 3 → ConsistentOn C W

end CorrColoring.ThreeChoosable


