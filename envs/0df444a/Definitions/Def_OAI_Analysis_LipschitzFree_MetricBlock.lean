-- Prove2me | Definitions.Def_OAI_Analysis_LipschitzFree_MetricBlock
-- name    : OAI_Analysis_LipschitzFree_MetricBlock
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T09:04:34.406582+00:00
-- url     : https://prove2.me/theorems/3336f1d4-2355-4bf4-bc15-56052833be79
-- title:
--   Metric blocks: a coloured port graph with label anchors and an integer shortest-path metric
-- statement:
--   This file builds, from a coloured port graph, the countable metric space (*metric block*) used in the construction.
--
--   The data are: a port graph with vertex set $X$ and port set $D$, i.e. an involution $e\mapsto\bar e$ of $D$ and moves $(x,e)\mapsto x\cdot e$ with $(x\cdot e)\cdot\bar e=x$; a finite set $C$ of colours with a colouring $\chi:X\to C$; and natural numbers $\mathrm{cap}$ and $R$. Box labels are functions $C\to\{0,\dots,\mathrm{cap}\}$, with the supremum distance $\rho(a,b)=\max_{i\in C}|a_i-b_i|$.
--
--   1. **Labels.** The original label of a vertex $x$ is the box label $\lambda(x)$ whose coordinate $\lambda_i(x)$ is the length of a shortest walk (sequence of moves) from $x$ to a vertex of colour $i$, truncated at $\mathrm{cap}$.
--   2. **Anchors and points.** The anchors are the box labels that occur, $\mathcal{A}=\{\lambda(x):x\in X\}$, a finite set. The point set of the block is the disjoint union $P=X\sqcup\mathcal{A}$, which is countable when $X$ is. Every point carries a label: $\lambda(x)$ for a vertex $x$ and $a$ itself for an anchor $a$; the anchor of a vertex $x$ is $\lambda(x)\in\mathcal{A}$.
--   3. **Adjacency.** Vertices $x,y$ are adjacent if $y=x\cdot e$ for some port $e$; this relation is symmetric.
--   4. **Weights.** The weight $w:P\times P\to\mathbb{N}$ is $w(u,u)=0$ and, for $u\neq v$,
--   $$w(u,v)=\begin{cases}1, & u,v\in X \text{ adjacent},\\ R, & \{u,v\}=\{x,\lambda(x)\} \text{ for a vertex } x \text{ and its anchor},\\ 2R+\rho(a,b), & u=a,\ v=b \text{ both anchors},\\ 4R+\mathrm{cap}, & \text{otherwise (non-adjacent vertices, or a vertex and an anchor other than its label)}.\end{cases}$$
--   It is symmetric, and strictly positive on pairs of distinct points when $R>0$.
--   5. **Metric.** For $R>0$ the metric block is $P$ with the shortest-path metric of $w$,
--   $$d(u,v)=\min\bigl\{\,w(u,z_1)+w(z_1,z_2)+\cdots+w(z_k,v)\ :\ k\ge0,\ z_1,\dots,z_k\in P\,\bigr\},$$
--   an integer-valued metric; in particular distinct points satisfy $d(u,v)\ge1$.
--
--   With the graph, colouring and parameters chosen in terms of the norm bound $p$, these blocks are the countable $1$-separated metric spaces of bounded diameter in the block statement: distinct adjacent vertices are at distance $1$, every vertex is joined by an edge of length $R$ to the anchor recording its label, and anchors are spaced according to the distance of their labels, which makes the label map a $1$-Lipschitz map from the block to the box of labels.
--
--   **Formalization Note** `Point G color cap R` is `X ⊕ Anchor G color cap`, where `Anchor` is the subtype of `BoxLabel C cap` given by the range of `originalLabel`; $R$ appears in the type only so that the `MetricSpace` instance can depend on it, which requires `Fact (0 < R)`. `metric` is `NatMetricClosure.metricSpace` applied to `weight`, and `separated` is the bound $1\le d(u,v)$. The private lemma `ite_eq_right` is a local compatibility helper.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/LipschitzFree/MetricBlock.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/LipschitzFree/MetricBlock.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the DiscreteLipschitzFree mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_DiscreteLipschitzFree
import Definitions.Def_OAI_Analysis_LipschitzFree_PortGraphs
import Definitions.Def_OAI_Analysis_LipschitzFree_RenormingModel
import Definitions.Def_OAI_Analysis_LipschitzFree_Model
import Definitions.Def_OAI_Analysis_LipschitzFree_Parameters
import Definitions.Def_OAI_Analysis_LipschitzFree_BoxLabels
import Definitions.Def_OAI_Analysis_LipschitzFree_MetricClosure

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

/-!
# Metric blocks obtained by adjoining finite label anchors
-/

noncomputable section
open scoped BigOperators ENNReal

noncomputable section
namespace DiscreteFree.MetricBlock
open scoped Classical
variable {X D C : Type*} [Fintype C] (G : PortGraph X D) (color : X → C) (cap R : ℕ)

def originalLabel (x : X) : BoxLabel C cap :=
  fun i => ⟨G.label color cap i x, Nat.lt_succ_of_le (G.label_le color cap i x)⟩

def Anchor := {a : BoxLabel C cap // a ∈ Set.range (originalLabel G color cap)}

instance : Fintype (Anchor G color cap) := inferInstanceAs (Fintype {a : BoxLabel C cap // a ∈ Set.range (originalLabel G color cap)})

def Point (_R : ℕ) := X ⊕ Anchor G color cap

instance [Countable X] : Countable (Point G color cap R) := inferInstanceAs (Countable (X ⊕ Anchor G color cap))

def ofVertex (x : X) : Point G color cap R := Sum.inl x

def ofAnchor (a : Anchor G color cap) : Point G color cap R := Sum.inr a

def anchorOf (x : X) : Anchor G color cap := ⟨originalLabel G color cap x, x, rfl⟩

def label : Point G color cap R → BoxLabel C cap
  | Sum.inl x => originalLabel G color cap x
  | Sum.inr a => a.val

def Adj (x y : X) : Prop := ∃ e, G.move x e = y

theorem adj_symm {x y : X} (h : Adj G x y) : Adj G y x := by
  obtain ⟨e, rfl⟩ := h
  exact ⟨G.reverse e, G.move_reverse x e⟩

theorem adj_comm (x y : X) : Adj G x y ↔ Adj G y x := ⟨adj_symm G, adj_symm G⟩

def weight (u v : Point G color cap R) : ℕ :=
  if u = v then 0 else match u, v with
  | Sum.inl x, Sum.inl y => if Adj G x y then 1 else 4*R+cap
  | Sum.inl x, Sum.inr a => if originalLabel G color cap x = a.val then R else 4*R+cap
  | Sum.inr a, Sum.inl x => if originalLabel G color cap x = a.val then R else 4*R+cap
  | Sum.inr a, Sum.inr b => 2*R + BoxLabel.distance a.val b.val

@[simp] theorem weight_self (u : Point G color cap R) : weight G color cap R u u = 0 := by
  simp [weight]

theorem weight_symm (u v : Point G color cap R) : weight G color cap R u v = weight G color cap R v u := by
  by_cases h : u = v
  · subst v; rfl
  · cases u <;> cases v <;>
      simp only [weight, ite_eq_right h, ite_eq_right (Ne.symm h)]
    · rw [adj_comm]
    · rw [BoxLabel.distance_comm]

theorem weight_pos (hR : 0 < R) {u v : Point G color cap R} (huv : u ≠ v) :
    0 < weight G color cap R u v := by
  cases u <;> cases v <;> simp only [weight, ite_eq_right huv]
  · split_ifs <;> omega
  · split_ifs <;> omega
  · split_ifs <;> omega
  · omega

theorem weight_zero (hR : 0 < R) (u v : Point G color cap R)
    (h : weight G color cap R u v = 0) : u = v := by
  by_contra hne
  have hp := weight_pos G color cap R hR hne
  omega

abbrev metric (hR : 0 < R) : MetricSpace (Point G color cap R) :=
  NatMetricClosure.metricSpace (weight G color cap R) (weight_self G color cap R)
    (weight_symm G color cap R) (weight_zero G color cap R hR)

instance [Fact (0 < R)] : MetricSpace (Point G color cap R) := metric G color cap R Fact.out

variable [Fact (0 < R)]

theorem separated {u v : Point G color cap R} (h : u ≠ v) : 1 ≤ dist u v :=
  NatMetricClosure.separated (weight G color cap R) (weight_self G color cap R)
    (weight_symm G color cap R) (weight_zero G color cap R Fact.out) h

end DiscreteFree.MetricBlock
end

end

end OAI


