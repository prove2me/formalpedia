-- Prove2me | Definitions.Def_CostScaling_Refine_Core
-- name    : CostScaling_Refine_Core
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T04:01:49.114152+00:00
-- url     : https://prove2.me/theorems/906954e0-6629-4c27-95ab-8706e327c2a6
-- title:
--   Pseudoflows, prices, and the initialization of generic refine
-- statement:
--   Let $G=(V,E)$ be a finite symmetric directed network with real capacities $u$ and antisymmetric costs $c$. A **pseudoflow** $f$ obeys $f(v,w)\leq u(v,w)$ and $f(v,w)=-f(w,v)$ on each arc. Its **excess** is $e_f(v)=\sum_{(w,v)\in E}f(w,v)$; a vertex is active when this is positive. The **residual capacity** is $u_f(v,w)=u(v,w)-f(v,w)$, and an arc is residual when $u_f(v,w)>0$.
--
--   For prices $p:V\to\mathbb R$, the reduced cost and residual-arc form of **$\varepsilon$-optimality** are
--
--   $$
--   c_p(v,w)=c(v,w)-p(v)+p(w),\qquad f\text{ is }\varepsilon\text{-optimal w.r.t. }p\iff c_p(v,w)\geq-\varepsilon\text{ on every residual arc}.
--   $$
--
--   An arc is admissible when it is residual and its reduced cost is negative. The initial pseudoflow of Figure 4 saturates each arc with negative reduced cost, leaves other edges at the entry flow, and keeps the entry prices. These definitions provide the state on which every update and bound of the mission is stated.
--
--   **Formalization Note** The published network and circulation definitions are reused. The initialization writes both orientations of an edge so antisymmetry is maintained. The reduced-cost sign is the one in this report.
-- source:
--   Goldberg & Tarjan, MIT/LCS/TM-333 (July 1987), pp. 5–7, Section 2.1, (2)–(4), Section 2.2, (7), and p. 18, Figure 4; https://publications.csail.mit.edu/lcs/pubs/pdf/MIT-LCS-TM-333.pdf

import Mathlib
import Definitions.Def_CycleCanceling_MinMean_Network

namespace CostScaling.Refine

variable {V : Type*} [Fintype V] [DecidableEq V]

abbrev Network (V : Type*) [Fintype V] [DecidableEq V] :=
  CycleCanceling.MinMean.CircNetwork V

/-- Equations (2) and (3), on the arcs of the circulation network. -/
def IsPseudoflow (N : Network V) (f : V → V → ℝ) : Prop :=
  (∀ v w, (v, w) ∈ N.E → f v w ≤ N.u v w) ∧
  (∀ v w, (v, w) ∈ N.E → f v w = -f w v)

/-- Excess is incoming flow, with the outgoing-neighbour filter justified by symmetry. -/
def excess (N : Network V) (f : V → V → ℝ) (v : V) : ℝ :=
  ∑ w ∈ Finset.univ.filter (fun w => (v, w) ∈ N.E), f w v

def IsActive (N : Network V) (f : V → V → ℝ) (v : V) : Prop :=
  0 < excess N f v

def IsResidualArc (N : Network V) (f : V → V → ℝ) (v w : V) : Prop :=
  (v, w) ∈ N.E ∧ 0 < CycleCanceling.MinMean.resCap N f v w

/-- The sign convention of this paper is `c(v,w) - p(v) + p(w)`. -/
def reducedCost (N : Network V) (p : V → ℝ) (v w : V) : ℝ :=
  N.c v w - p v + p w

/-- Equation (7), in its residual-arc form on p. 7. -/
def IsEpsOptimal (N : Network V) (ε : ℝ) (f : V → V → ℝ) (p : V → ℝ) : Prop :=
  IsPseudoflow N f ∧
  ∀ v w, IsResidualArc N f v w → -ε ≤ reducedCost N p v w

def IsAdmissible (N : Network V) (f : V → V → ℝ) (p : V → ℝ) (v w : V) : Prop :=
  IsResidualArc N f v w ∧ reducedCost N p v w < 0

/-- The paper's pseudoflow and vertex prices at one point of the loop. -/
structure State (V : Type*) where
  f : V → V → ℝ
  p : V → ℝ

/-- Figure 4 saturation, setting both antisymmetric directions of an edge. -/
noncomputable def initialFlow (N : Network V) (f₀ : V → V → ℝ) (p₀ : V → ℝ) (v w : V) : ℝ :=
  if (v, w) ∈ N.E ∧ reducedCost N p₀ v w < 0 then N.u v w
  else if (v, w) ∈ N.E ∧ reducedCost N p₀ w v < 0 then -N.u w v
  else f₀ v w

noncomputable def initialState (N : Network V) (f₀ : V → V → ℝ) (p₀ : V → ℝ) : State V :=
  ⟨initialFlow N f₀ p₀, p₀⟩

end CostScaling.Refine


