-- Prove2me | Definitions.Def_SublinearSteiner_ReducedTree
-- name    : SublinearSteiner_ReducedTree
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:43:07.01333+00:00
-- url     : https://prove2.me/theorems/b49bf54e-5e89-4014-bf62-0ac8da9de0fa
-- title:
--   Reduced trees: limbs, fans, good reconnections, short-core stars, fringes and promotions
-- statement:
--   The combinatorial state of the structural theorem's reduction process.
--
--   A **reduced tree** $K$ is a feasible tree in which every nonterminal has degree at least three. $E_T(K)$ are its edges joining two terminals and $E_S(K)$ the rest.
--
--   **Limbs.** At a nonterminal $v$, a *direct limb* is a tree edge $vx$ with $x\in T$; its length and cost are $r=W=w(v,x)$. A *cherry* is a nonterminal $y$ of degree three adjacent to $v$ and to two terminals $x,x'$, with $s=w(y,x)\le s'=w(y,x')$; its trunk is $z=w(v,y)$, its length $r=z+s$ and its cost $W=r+s'$. The region of a limb is the component of $K$ minus the limb's edge at $v$ that does not contain $v$. A *fan* is a nonterminal $v$ of degree three whose neighbors are a nonterminal parent $v'$ and two limbs.
--
--   **Good reconnections.** (G1), (G2), (G3) exchange one edge, a cherry, or a fan for terminal edges. *No good reconnection applies* means that in each case the added terminal edges weigh more than $\chi$ times the removed edges.
--
--   **Events.** A *short-core star* is three limbs with pairwise disjoint regions, each attached outside the regions of the other two, whose attachment points are joined by a subtree of nonterminals of weight at most $\theta_0\ell$, for $\ell$ the smallest length. A *fringe* for a root terminal is a fan with the root outside its region and no other nonterminal in its region except its cherry centers. Its promotion, if it has a cherry, is *small* if $s_j<\alpha_0r_j$ for every cherry, and *regular* if it is not small and $z\ge\delta_0(r_1+r_2)$.
--
--   **Formalization Note.** A limb is data: `direct x` or `cherry y x x'`. For a direct limb $z=r$ and $s=s'=0$, the page's own convention. The parent of a fringe is the neighbor toward the root.
-- source:
--   Mahabadi, Roghani, Tarnawski, Vakilian, Tight Bounds for Sublinear Metric Steiner Tree, STOC 2027 submission (manuscript sha256 ae133037…), Sections 3.1–3.2, pp.15–17

import Mathlib
import Definitions.Def_SublinearSteiner_Constants
import Definitions.Def_SublinearSteiner_ThresholdGraph

open scoped Classical

namespace SublinearSteiner

/-!
# Reduced trees: limbs, fans, good reconnections, short-core stars and promotions

Mahabadi, Roghani, Tarnawski, Vakilian, *Tight Bounds for Sublinear Metric Steiner Tree*, STOC 2027
submission (manuscript sha256 ae133037…), Sections 3.1–3.2, pp.15–17.

**Formalization Note.**
* A `ReducedTree` is any feasible tree in which every nonterminal has degree at least three (p.15, after cleanup). It
  need not be optimal: Lemmas 3.2 and 3.6 use only the current state of the process.
* A limb is written as data: `direct x` is the tree edge `vx`, and `cherry y x x'` is the center `y` with primary port
  `x` and second port `x'`, where `s = w(y, x) ≤ s' = w(y, x')`. For a direct limb `s = s' = 0` and the trunk is
  `z = r`, the page's convention in Lemma 3.2(iii). Then `r = z + s` and `W = r + s'` in both cases.
* "No good reconnection applies" is written out: for each move, the added terminal edges weigh more than `χ` times
  the removed edges. A "terminal edge from the region to its complement" is a pair `a, b ∈ T` with `a` in the region and
  `b` not in it. In a fan with a direct limb, the sibling edges are only those of its cherries.
* The root of a promotion is a terminal, and a fringe's parent is its neighbor toward the root: the root lies outside
  the fan's region. The page's Lemma 3.6 proof roots the tree at a group, which gives exactly this.
-/

variable {n : ℕ}

/-- A feasible tree on the terminals `T` in which every nonterminal has degree at least three (p.15). -/
structure ReducedTree (T : Finset (Fin n)) where
  /-- The vertex set. -/
  U : Finset (Fin n)
  /-- The edge set. -/
  E : Finset (Sym2 (Fin n))
  sub : T ⊆ U
  tree : IsTreeOn U E
  nonterminal_deg : ∀ v ∈ U \ T, 3 ≤ (E.filter fun e => v ∈ e).card

/-- A limb attached at a nonterminal: a direct limb, or a cherry with its center and two ports (p.16). -/
inductive Limb (n : ℕ) : Type
  /-- The tree edge `vx`. -/
  | direct (x : Fin n)
  /-- The center `y`, the primary port `x` and the other port `x'`. -/
  | cherry (y x x' : Fin n)

namespace Limb

/-- The neighbor of the attachment point on the limb. -/
def head : Limb n → Fin n
  | direct x => x
  | cherry y _ _ => y

/-- The primary port. -/
def port : Limb n → Fin n
  | direct x => x
  | cherry _ x _ => x

/-- Whether the limb is a cherry. -/
def IsCherry : Limb n → Prop
  | direct _ => False
  | cherry _ _ _ => True

/-- The trunk `z`; for a direct limb `z = r` (p.16). -/
def trunk (w : FinMetric n) (v : Fin n) (l : Limb n) : ℝ := w.d v l.head

/-- The shorter arm `s`, and `0` for a direct limb. -/
def armS (w : FinMetric n) : Limb n → ℝ
  | direct _ => 0
  | cherry y x _ => w.d y x

/-- The longer arm `s'`, and `0` for a direct limb. -/
def armL (w : FinMetric n) : Limb n → ℝ
  | direct _ => 0
  | cherry y _ x' => w.d y x'

/-- The length `r = z + s`. -/
def length (w : FinMetric n) (v : Fin n) (l : Limb n) : ℝ := l.trunk w v + l.armS w

/-- The cost `W = r + s'`. -/
def cost (w : FinMetric n) (v : Fin n) (l : Limb n) : ℝ := l.length w v + l.armL w

/-- The weight of the sibling edge `xx'` of a cherry, and `0` for a direct limb. -/
def siblingWeight (w : FinMetric n) : Limb n → ℝ
  | direct _ => 0
  | cherry _ x x' => w.d x x'

end Limb

namespace ReducedTree

variable {T : Finset (Fin n)}

/-- The degree of a vertex. -/
noncomputable def deg (K : ReducedTree T) (v : Fin n) : ℕ := (K.E.filter fun e => v ∈ e).card

/-- `E_T(K)`: the edges joining two terminals (p.15). -/
noncomputable def termEdges (K : ReducedTree T) : Finset (Sym2 (Fin n)) :=
  K.E.filter fun e => ∀ x ∈ e, x ∈ T

/-- `E_S(K)`: the remaining edges (p.15). -/
noncomputable def steinerEdges (K : ReducedTree T) : Finset (Sym2 (Fin n)) :=
  K.E.filter fun e => ¬ ∀ x ∈ e, x ∈ T

/-- The graph of `K` minus the edge `e`. -/
noncomputable def minusEdge (K : ReducedTree T) (e : Sym2 (Fin n)) : SimpleGraph (Fin n) :=
  edgeGraph (K.E.erase e)

/-- `G_a(T) ∪ E_T(K)`. -/
noncomputable def augGraph (K : ReducedTree T) (w : FinMetric n) (a : ℝ) : SimpleGraph (Fin n) :=
  thresholdGraph w T a ⊔ edgeGraph K.termEdges

/-- The limb `l` is attached at the nonterminal `v` of `K` (p.16). -/
def IsLimbAt (K : ReducedTree T) (w : FinMetric n) (v : Fin n) : Limb n → Prop
  | .direct x => v ∈ K.U ∧ v ∉ T ∧ x ∈ T ∧ s(v, x) ∈ K.E
  | .cherry y x x' =>
      v ∈ K.U ∧ v ∉ T ∧ y ∈ K.U ∧ y ∉ T ∧ K.deg y = 3 ∧ s(v, y) ∈ K.E ∧ s(y, x) ∈ K.E ∧
        s(y, x') ∈ K.E ∧ x ∈ T ∧ x' ∈ T ∧ x ≠ x' ∧ w.d y x ≤ w.d y x'

/-- The region of a limb: the vertex set of the component of `K` minus the limb's edge at `v` that does not contain
`v` (p.16). -/
noncomputable def region (K : ReducedTree T) (v : Fin n) (l : Limb n) : Finset (Fin n) :=
  K.U.filter fun u => (K.minusEdge s(v, l.head)).Reachable u l.head

/-- The region of a fan `v` with parent `v'`: the component of `K − vv'` containing `v` (p.16). -/
noncomputable def fanRegion (K : ReducedTree T) (v v' : Fin n) : Finset (Fin n) :=
  K.U.filter fun u => (K.minusEdge s(v, v')).Reachable u v

/-- A fan: a nonterminal `v` of degree three whose neighbors are a nonterminal `v'` and two limbs attached at `v`
(p.16). -/
structure IsFan (K : ReducedTree T) (w : FinMetric n) (v v' : Fin n) (l₁ l₂ : Limb n) : Prop where
  v_mem : v ∈ K.U
  v_nonterminal : v ∉ T
  deg_three : K.deg v = 3
  parent_mem : v' ∈ K.U
  parent_nonterminal : v' ∉ T
  parent_edge : s(v, v') ∈ K.E
  limb₁ : K.IsLimbAt w v l₁
  limb₂ : K.IsLimbAt w v l₂
  heads_ne : l₁.head ≠ l₂.head
  head₁_ne : l₁.head ≠ v'
  head₂_ne : l₂.head ≠ v'

/-- No good reconnection applies: none of (G1), (G2), (G3) has its added terminal edges weighing at most `χ` times
the removed edges (p.16). -/
structure NoGoodReconnection (K : ReducedTree T) (w : FinMetric n) : Prop where
  /-- (G1): one edge `e ∈ E_S(K)` and a terminal edge joining the two components of `K − e`. -/
  g1 : ∀ e ∈ K.steinerEdges, ∀ x ∈ T, ∀ x' ∈ T, ¬ (K.minusEdge e).Reachable x x' →
    chi * w.edgeLen e < w.d x x'
  /-- (G2): a cherry, its sibling edge, and a terminal edge from its region to the complement. -/
  g2 : ∀ (v y x x' : Fin n), K.IsLimbAt w v (.cherry y x x') →
    ∀ a ∈ T, a ∈ K.region v (.cherry y x x') → ∀ b ∈ T, b ∉ K.region v (.cherry y x x') →
      chi * (Limb.cherry y x x').cost w v - w.d x x' < w.d a b
  /-- (G3): a fan, the sibling edges of its cherries, the edge between its primary ports, and a terminal edge from its
  region to the complement. -/
  g3 : ∀ (v v' : Fin n) (l₁ l₂ : Limb n), K.IsFan w v v' l₁ l₂ →
    ∀ a ∈ T, a ∈ K.fanRegion v v' → ∀ b ∈ T, b ∉ K.fanRegion v v' →
      chi * (w.d v v' + l₁.cost w v + l₂.cost w v)
        - (l₁.siblingWeight w + l₂.siblingWeight w + w.d l₁.port l₂.port) < w.d a b

/-- A short-core star: three limbs with pairwise disjoint regions, each attached outside the regions of the other
two, whose attachment points are joined by a subtree of nonterminals of weight at most `θ0 ℓ`, where `ℓ` is the
smallest of the three lengths (p.17). -/
structure IsShortCoreStar (K : ReducedTree T) (w : FinMetric n) (v₁ v₂ v₃ : Fin n)
    (l₁ l₂ l₃ : Limb n) : Prop where
  limb₁ : K.IsLimbAt w v₁ l₁
  limb₂ : K.IsLimbAt w v₂ l₂
  limb₃ : K.IsLimbAt w v₃ l₃
  disjoint₁₂ : Disjoint (K.region v₁ l₁) (K.region v₂ l₂)
  disjoint₁₃ : Disjoint (K.region v₁ l₁) (K.region v₃ l₃)
  disjoint₂₃ : Disjoint (K.region v₂ l₂) (K.region v₃ l₃)
  outside₁₂ : v₁ ∉ K.region v₂ l₂
  outside₁₃ : v₁ ∉ K.region v₃ l₃
  outside₂₁ : v₂ ∉ K.region v₁ l₁
  outside₂₃ : v₂ ∉ K.region v₃ l₃
  outside₃₁ : v₃ ∉ K.region v₁ l₁
  outside₃₂ : v₃ ∉ K.region v₂ l₂
  core : ∃ (CV : Finset (Fin n)) (CE : Finset (Sym2 (Fin n))),
    CE ⊆ K.E ∧ CV ⊆ K.U \ T ∧ IsTreeOn CV CE ∧ v₁ ∈ CV ∧ v₂ ∈ CV ∧ v₃ ∈ CV ∧
      w.weight CE ≤ theta0 * min (min (l₁.length w v₁) (l₂.length w v₂)) (l₃.length w v₃)

/-- A fringe for the root terminal `root`: a fan whose region does not contain the root and contains no nonterminal
other than the fan and its cherry centers (p.17). -/
structure IsFringe (K : ReducedTree T) (w : FinMetric n) (root v v' : Fin n) (l₁ l₂ : Limb n) : Prop where
  fan : K.IsFan w v v' l₁ l₂
  root_outside : root ∉ K.fanRegion v v'
  no_other : ∀ u ∈ K.fanRegion v v', u ∉ T → u = v ∨ u = l₁.head ∨ u = l₂.head

/-- A fringe with at least one cherry whose promotion is small: `s_j < α0 r_j` for every cherry (p.17). -/
def IsSmallPromotion (w : FinMetric n) (v : Fin n) (l₁ l₂ : Limb n) : Prop :=
  (l₁.IsCherry ∨ l₂.IsCherry) ∧
    (l₁.IsCherry → l₁.armS w < alpha0 * l₁.length w v) ∧
    (l₂.IsCherry → l₂.armS w < alpha0 * l₂.length w v)

/-- A fringe with at least one cherry whose promotion is regular: it is not small, and its parent edge has
`z ≥ δ0 R_f`, where `R_f = r₁ + r₂` (p.17). -/
def IsRegularPromotion (w : FinMetric n) (v v' : Fin n) (l₁ l₂ : Limb n) : Prop :=
  (l₁.IsCherry ∨ l₂.IsCherry) ∧ ¬ IsSmallPromotion w v l₁ l₂ ∧
    delta0 * (l₁.length w v + l₂.length w v) ≤ w.d v v'

end ReducedTree

end SublinearSteiner


