-- Prove2me | Definitions.Def_UnitCapMCF_Excess_Setting
-- name    : UnitCapMCF_Excess_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T18:30:39.676682+00:00
-- url     : https://prove2.me/theorems/f213826e-642b-4292-9bc2-7bb3d5325b3e
-- title:
--   §2–§3, pp. 408–410 — unit capacity networks, excess, cuts, and level bands
-- statement:
--   Let $G=(V,E)$ be a finite directed network with both orientations of every arc. Each pair has one input arc of capacity one and one reverse arc of capacity zero. The number $m$ of input arcs counts only capacity-one arcs.
--
--   For an entry circulation $f'$ and a current pseudoflow $f$, let $E^+=\{(v,w)\in E:f'(v,w)>f(v,w)\}$. An **excess–deficit cut** $Y\subseteq E^+$ meets every path in $G^+=(V,E^+)$ from a vertex with positive excess to one with negative excess. Total excess is the sum of positive vertex excesses. At scale $\varepsilon>0$, the price level is $d(v)=(p(v)-p'(v))/\varepsilon$. The arc bands $A_i$ and vertex bands $N_i$ select the level ranges printed in the proof of Lemma 5.
--
--   These objects give the common setting for Lemmas 3–5 and the two counting cases.
--
--   **Formalization Note** The network, circulation, pseudoflow, excess and reduced cost are imported published definitions. Capacity and cost values are real; the theorems use no cost integrality. A cut is expressed by the absence of a reachable deficit after deleting its arcs from $G^+$. Level bands use real subtraction, including the negative endpoints when $i=1$.
-- source:
--   Goldberg, Kaplan, Hed & Tarjan, Minimum Cost Flows in Graphs with Unit Capacities, STACS 2015 (LIPIcs 30), pp. 408–410, §2 and §3; https://doi.org/10.4230/LIPIcs.STACS.2015.406

import Mathlib
import Definitions.Def_CycleCanceling_MinMean_Network
import Definitions.Def_CostScaling_Refine_Core

namespace UnitCapMCF.Excess

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Each edge pair contains one unit-capacity input arc and its zero-capacity reverse. -/
def IsUnitCapacity (N : CostScaling.Refine.Network V) : Prop :=
  ∀ v w, (v, w) ∈ N.E →
    (N.u v w = 1 ∧ N.u w v = 0) ∨ (N.u v w = 0 ∧ N.u w v = 1)

/-- The number of input arcs, excluding their reverse arcs. -/
noncomputable def numArcs (N : CostScaling.Refine.Network V) : ℕ := by
  classical
  exact (N.E.filter (fun a => N.u a.1 a.2 = 1)).card

/-- Arcs on which the entry circulation carries more flow than the current pseudoflow. -/
noncomputable def Eplus (N : CostScaling.Refine.Network V)
    (f' f : V → V → ℝ) : Finset (V × V) := by
  classical
  exact N.E.filter (fun a => f a.1 a.2 < f' a.1 a.2)

/-- An arc cut inside `G⁺`: deleting it leaves no deficit reachable from an excess. -/
def IsExcessDeficitCut (N : CostScaling.Refine.Network V)
    (f' f : V → V → ℝ) (Y : Finset (V × V)) : Prop :=
  Y ⊆ Eplus N f' f ∧
  ∀ v w, 0 < CostScaling.Refine.excess N f v →
    CostScaling.Refine.excess N f w < 0 →
    ¬ Relation.ReflTransGen
      (fun a b => (a, b) ∈ Eplus N f' f ∧ (a, b) ∉ Y) v w

/-- Sum of positive vertex excesses. -/
noncomputable def totalExcess (N : CostScaling.Refine.Network V)
    (f : V → V → ℝ) : ℝ := by
  classical
  exact ∑ v ∈ Finset.univ.filter (fun v => 0 < CostScaling.Refine.excess N f v),
    CostScaling.Refine.excess N f v

/-- The potential increase measured in units of the current scale. -/
noncomputable def dlevel (ε : ℝ) (p' p : V → ℝ) (v : V) : ℝ :=
  (p v - p' v) / ε

/-- The arc band `Aᵢ` in the first case of Lemma 5. The subtraction is real subtraction. -/
noncomputable def bandArcs (N : CostScaling.Refine.Network V)
    (f' f : V → V → ℝ) (ε : ℝ) (p' p : V → ℝ) (i : ℕ) :
    Finset (V × V) := by
  classical
  exact (Eplus N f' f).filter (fun a =>
    (dlevel ε p' p a.1 = 3 * (i : ℝ) ∨
     dlevel ε p' p a.1 = 3 * (i : ℝ) - 1 ∨
     dlevel ε p' p a.1 = 3 * (i : ℝ) - 2) ∧
    (dlevel ε p' p a.2 = 3 * (i : ℝ) - 3 ∨
     dlevel ε p' p a.2 = 3 * (i : ℝ) - 4 ∨
     dlevel ε p' p a.2 = 3 * (i : ℝ) - 5))

/-- The six-level vertex band `Nᵢ` in the second case of Lemma 5. -/
noncomputable def bandVerts (ε : ℝ) (p' p : V → ℝ) (i : ℕ) : Finset V := by
  classical
  exact Finset.univ.filter (fun v =>
    dlevel ε p' p v = 6 * (i : ℝ) ∨
    dlevel ε p' p v = 6 * (i : ℝ) - 1 ∨
    dlevel ε p' p v = 6 * (i : ℝ) - 2 ∨
    dlevel ε p' p v = 6 * (i : ℝ) - 3 ∨
    dlevel ε p' p v = 6 * (i : ℝ) - 4 ∨
    dlevel ε p' p v = 6 * (i : ℝ) - 5)

end UnitCapMCF.Excess


