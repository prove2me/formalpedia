-- Prove2me | Definitions.Def_SubquadCutReach_Faster_Graphs
-- name    : SubquadCutReach_Faster_Graphs
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T16:56:41.885203+00:00
-- url     : https://prove2.me/theorems/cb0b3e0f-3a9d-4554-acea-29c85f4939e8
-- title:
--   Labelled graphs, orientation rules and imbalance
-- statement:
--   Let $V=\{0,\ldots,n-1\}$. An oriented graph is a loopless asymmetric relation on $V$; its skeleton is a Mathlib simple graph. A rule assigns a direction to every increasing pair, including nonedges. Its induced orientation retains precisely the skeleton edges. Reachability is the reflexive transitive closure, so a length-zero path is allowed.
--
--   $$b_D(v)=\deg_D^+(v)-\deg_D^-(v),\qquad b_z(v)=\sum_{w>v}c_{vw}z(v,w)-\sum_{u<v}c_{uv}z(u,v).$$
--
--   Feasibility means existential realizability by an orientation, with no supplied witness. The file also defines both cut counts, known-pair subgraphs, finite norms, $L(n)=\log(n+2)$ and the five-thirds scale. These definitions give every target one shared graph convention.
-- source:
--   Henry Fleischmann, Sagnik Mukhopadhyay, Swagato Sanyal, STOC 2027 submission #503 (October 2026), §2, Definitions 2.1, 3.1, 3.3, 3.6; pp.3–8 (PDF pp.5–10)

import Mathlib

set_option autoImplicit false
open scoped BigOperators

namespace SubquadCutReach.Faster

/-- Source §2: the base objects are Mathlib simple graphs and finite labelled relations.
Rules contain one Boolean per ordered increasing pair, including nonedges. -/
abbrev Rule (n : ℕ) := Fin n → Fin n → Bool
abbrev Fractional (n : ℕ) := Fin n → Fin n → ℝ
abbrev Digraph (n : ℕ) := Fin n → Fin n → Prop

def Oriented {n : ℕ} (G : Digraph n) : Prop :=
  (∀ v, ¬ G v v) ∧ ∀ u v, G u v → ¬ G v u

noncomputable def skeleton {n : ℕ} (G : Digraph n) (h : Oriented G) : SimpleGraph (Fin n) where
  Adj u v := G u v ∨ G v u
  symm := ⟨fun {_ _} h => Or.symm h⟩
  loopless := ⟨fun v h' => h'.elim (h.1 v) (h.1 v)⟩

def directs {n : ℕ} (D : Rule n) (u v : Fin n) : Prop :=
  (u < v ∧ D u v = true) ∨ (v < u ∧ D v u = false)

def induced {n : ℕ} (H : SimpleGraph (Fin n)) (D : Rule n) : Digraph n :=
  fun u v => H.Adj u v ∧ directs D u v

noncomputable def outCut {n : ℕ} (G : Digraph n) (S : Finset (Fin n)) : ℕ := by
  classical
  exact ((Finset.univ ×ˢ Finset.univ).filter fun uv =>
    G uv.1 uv.2 ∧ uv.1 ∈ S ∧ uv.2 ∉ S).card

noncomputable def cut {n : ℕ} (H : SimpleGraph (Fin n)) (S : Finset (Fin n)) : ℕ := by
  classical
  exact ((Finset.univ ×ˢ Finset.univ).filter fun uv =>
    H.Adj uv.1 uv.2 ∧ uv.1 ∈ S ∧ uv.2 ∉ S).card

noncomputable def imbalance {n : ℕ} (G : Digraph n) (v : Fin n) : ℤ := by
  classical
  exact (Finset.univ.filter (G v)).card - (Finset.univ.filter fun u => G u v).card

def reachable {n : ℕ} (G : Digraph n) (s t : Fin n) : Prop := Relation.ReflTransGen G s t

def Feasible {n : ℕ} (H : SimpleGraph (Fin n)) (b : Fin n → ℤ) : Prop :=
  ∃ D : Rule n, imbalance (induced H D) = b

noncomputable def pairs {n : ℕ} (H : SimpleGraph (Fin n)) : Finset (Fin n × Fin n) := by
  classical
  exact Finset.univ.filter fun uv => uv.1 < uv.2 ∧ H.Adj uv.1 uv.2

noncomputable def subgraph {n : ℕ} (H : SimpleGraph (Fin n)) (P : Rule n) :
    SimpleGraph (Fin n) where
  Adj u v := H.Adj u v ∧ (if u < v then P u v = true else P v u = true)
  symm := ⟨by
    intro u v h
    refine ⟨h.1.symm, ?_⟩
    rcases lt_or_gt_of_ne (H.ne_of_adj h.1) with hlt | hgt
    · simpa [hlt, not_lt.mpr hlt.le] using h.2
    · simpa [hgt, not_lt.mpr hgt.le] using h.2⟩
  loopless := ⟨fun _ h => H.ne_of_adj h.1 rfl⟩

def ValidFractional {n : ℕ} (z : Fractional n) : Prop :=
  ∀ u v, u < v → -1 ≤ z u v ∧ z u v ≤ 1

noncomputable def fractionalImbalance {n : ℕ} (H : SimpleGraph (Fin n))
    (z : Fractional n) (v : Fin n) : ℝ := by
  classical
  exact (∑ w, if v < w ∧ H.Adj v w then z v w else 0) -
    ∑ u, if u < v ∧ H.Adj u v then z u v else 0

noncomputable def l1 {α : Type} [Fintype α] (x : α → ℝ) : ℝ := ∑ i, |x i|
noncomputable def l2 {α : Type} [Fintype α] (x : α → ℝ) : ℝ := Real.sqrt (∑ i, (x i)^2)

def Linfty {α : Type} (x : α → ℝ) (C : ℝ) : Prop := ∀ i, |x i| ≤ C

noncomputable def error {n : ℕ} (H : SimpleGraph (Fin n)) (D : Rule n)
    (b : Fin n → ℤ) : ℝ := l1 fun v => (imbalance (induced H D) v - b v : ℤ)

noncomputable def L (n : ℕ) : ℝ := Real.log ((n : ℝ) + 2)
noncomputable def scale (n : ℕ) : ℝ := (n : ℝ) ^ ((5 : ℝ) / 3)

end SubquadCutReach.Faster


