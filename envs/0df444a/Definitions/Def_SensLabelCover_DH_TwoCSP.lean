-- Prove2me | Definitions.Def_SensLabelCover_DH_TwoCSP
-- name    : SensLabelCover_DH_TwoCSP
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T16:35:16.690311+00:00
-- url     : https://prove2.me/theorems/e939b06b-9e15-480f-aa81-28d3d97b6016
-- title:
--   2-CSPs on a fixed multigraph with ordered endpoint incidences: value, satisfiability, relation swaps and Hamming distance
-- statement:
--   A **2-CSP** on a multigraph $(X,E)$ (finite variable set $X$, finite edge set $E$, each edge with an ordered pair of endpoint incidences $(x,y)$; parallel edges and self-loops allowed) over a finite alphabet $\Sigma$ is a family of relations $R_e\subseteq\Sigma^2$, one per edge. The degree of a variable counts endpoint incidences, so a self-loop contributes two. An assignment $a:X\to\Sigma$ satisfies $e=(x,y)$ if $(a(x),a(y))\in R_e$; its value is
--   $$\mathrm{val}_R(a)=\begin{cases}1 & E=\emptyset,\\ |\{e: (a(x_e),a(y_e))\in R_e\}|/|E| & \text{otherwise,}\end{cases}$$
--   and $R$ is satisfiable if some assignment has value $1$. A **swap** replaces one relation $R_e$ by an arbitrary relation on the same pair of incidences, and assignments are compared by the Hamming distance $d_H(a,b)=|\{x: a(x)\neq b(x)\}|$.
--
--   This is the source problem of the mission: the sensitivity lower bound for Label Cover is transferred from a family of bounded-degree 2-CSPs.
--
--   **Formalization Note** The graph is `CSPGraph X E` with `ends e = (x, y)`; an instance is `CSPInst E A := E → Set (A × A)`. `cspVal` is `1` when `Fintype.card E = 0`. `cspAdj R R'` holds when `R'` is `R` with one edge's relation replaced. `cspDist` is the Hamming distance as a real number.
-- source:
--   Fleming, Hopkins, Yoshida, Sensitivity and Locality Lower Bounds via Low-Soundness Label Cover, STOC 2027 submission (manuscript sha256 5bfe95ad…), p. 16 (PDF 19) §2.3

import Mathlib
import Definitions.Def_SensLabelCover_DH_Sensitivity

open scoped BigOperators

namespace SensLabelCover.DH

/-! Fleming, Hopkins, Yoshida, *Sensitivity and Locality Lower Bounds via Low-Soundness Label
Cover*, STOC 2027 submission (manuscript sha256 5bfe95ad…), §2.3 (p. 16, PDF p. 19): the 2-CSP
model. A 2-CSP is a multigraph `(X, E)` with a fixed ordering of the two endpoint incidences of
each edge (parallel edges and self-loops allowed), an alphabet `Σ` and a relation
`R_e ⊆ Σ²` per edge. The graph and alphabet are fixed; an instance is the family of relations,
and a swap replaces one relation. -/

noncomputable section

/-- A multigraph on variables `X` with edge index type `E`; `ends e = (x, y)` lists the two
endpoint incidences of `e` in their fixed order (`x = y` is a self-loop). -/
structure CSPGraph (X E : Type) where
  ends : E → X × X

variable {X E A : Type}

/-- Degree of a variable, counting endpoint incidences (a self-loop counts twice). -/
def CSPGraph.deg [Fintype E] [DecidableEq X] (G : CSPGraph X E) (x : X) : ℕ :=
  (Finset.univ.filter (fun e => (G.ends e).1 = x)).card +
    (Finset.univ.filter (fun e => (G.ends e).2 = x)).card

/-- A 2-CSP instance on a fixed graph with edges `E` and alphabet `A`: a relation `R e ⊆ A × A`
for each edge. -/
abbrev CSPInst (E A : Type) := E → Set (A × A)

/-- Value of an assignment `a : X → A`: `1` if `E = ∅`, otherwise the fraction of edges
`e = (x, y)` with `(a x, a y) ∈ R_e`. -/
def cspVal [Fintype E] (G : CSPGraph X E) (R : CSPInst E A) (a : X → A) : ℝ :=
  by classical exact
    if Fintype.card E = 0 then 1
    else ((Finset.univ.filter (fun e => (a (G.ends e).1, a (G.ends e).2) ∈ R e)).card : ℝ) /
      (Fintype.card E : ℝ)

/-- A 2-CSP instance is satisfiable iff some assignment has value `1`. -/
def cspSat [Fintype E] (G : CSPGraph X E) (R : CSPInst E A) : Prop :=
  ∃ a : X → A, cspVal G R a = 1

/-- One swap: replace the relation of one edge (on its fixed pair of endpoint incidences) by an
arbitrary relation. -/
def cspAdj [DecidableEq E] (R R' : CSPInst E A) : Prop :=
  ∃ (e : E) (S : Set (A × A)), R' = Function.update R e S

/-- Hamming distance of 2-CSP assignments `X → A`, as a real cost. -/
def cspDist [Fintype X] [DecidableEq A] (a b : X → A) : ℝ :=
  (hammingDist a b : ℝ)

end

end SensLabelCover.DH


