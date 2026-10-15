-- Prove2me | Definitions.Def_OAI_Analysis_ForestSpace_Segments
-- name    : OAI_Analysis_ForestSpace_Segments
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T03:48:44.913032+00:00
-- url     : https://prove2.me/theorems/08a10929-ce50-4e6c-8a20-db65df07617e
-- title:
--   Forest orders, gates of ancestral sets, and restriction of disjoint-segment test bounds
-- statement:
--   Throughout, $(V,\le)$ is a partially ordered set, viewed as a forest whose roots are its minimal elements, and $u:V\to\mathbb{R}$ is an arbitrary real function on its vertices. The file builds on the following base notions. A *segment* is a finite set $S\subseteq V$ that is a chain (any two of its elements are comparable) and is order-convex ($a,b\in S$ and $a\le c\le b$ imply $c\in S$). The empty set counts as a segment. The *segment sum* is $\Sigma_S u=\sum_{v\in S}u(v)$. For $C\in\mathbb{R}$, $u$ *satisfies the test bound with constant $C$* if
--
--   $$
--   \sum_{i=1}^{m}\bigl(\Sigma_{S_i}u\bigr)^2\le C
--   $$
--
--   for every finite family $S_1,\dots,S_m$ ($m\ge0$) of pairwise disjoint segments. A set $H\subseteq V$ is *ancestral* if it is a lower set: $v\le w$ and $w\in H$ imply $v\in H$.
--
--   The file introduces three notions.
--
--   1. **Forest order.** $V$ is a *forest order* if for all $a,b,c\in V$ with $a\le c$ and $b\le c$ one has $a\le b$ or $b\le a$. Equivalently, for every vertex $c$ the set $\{a\in V: a\le c\}$ of its predecessors is a chain.
--   2. **Gates.** For $H\subseteq V$, a vertex $g$ is a *gate* of $H$ if $g\notin H$ and every $v<g$ belongs to $H$. In other words, $g$ is a minimal element of $V\setminus H$. When $H$ is ancestral, these are the first vertices outside $H$, including any roots of $V$ that are not in $H$.
--   3. **Support.** $u$ is *supported on* $H\subseteq V$ if $u(v)=0$ for every $v\notin H$.
--
--   The file also records the elementary facts used throughout the construction:
--
--   - the empty set and every singleton $\{v\}$ are segments;
--   - segment sums are linear in $u$: $\Sigma_\emptyset u=0$, $\Sigma_S 0=0$, $\Sigma_S(u\pm w)=\Sigma_S u\pm\Sigma_S w$ and $\Sigma_S(au)=a\,\Sigma_S u$ for $a\in\mathbb{R}$;
--   - if $u$ satisfies the test bound with constant $C$, then it also satisfies it with every $D\ge C$, necessarily $C\ge0$, and $(\Sigma_S u)^2\le C$ for every single segment $S$;
--   - if $S$ is a segment and $H$ is ancestral, then $S\cap H$ and $S\setminus H$ are segments;
--   - if $u$ satisfies the test bound with constant $C$ and $H$ is ancestral, then the restrictions $\mathbf 1_H u$ and $\mathbf 1_{V\setminus H}u$ (extended by $0$) satisfy it with the same constant $C$.
--
--   The last fact shows that cutting a vector into its *head* (the part on an ancestral set) and its *tail* (the part off it) does not increase the disjoint-segment norm. Gates are the vertices where a tail attaches to a head, and the paired estimate places its correction terms exactly there. Forest orders are the setting in which that estimate is proved.
--
--   **Formalization Note** The three definitions are `ForestOrder V`, `Gate H g` and `SupportedOn u H`. Ancestral sets are Mathlib's `IsLowerSet`. In `TestBound`, families of segments are indexed by an arbitrary finite type rather than by $\{1,\dots,m\}$. The recorded facts are `isSegment_empty`, `isSegment_singleton`, the `segSum` simplification lemmas, `TestBound.mono`, `TestBound.nonneg`, `TestBound.single`, `IsSegment.head`, `IsSegment.tail`, `TestBound.restrict` and `TestBound.restrict_compl`. In the last two, the restrictions are written with `Set.indicator`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/ForestSpace/Segments.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/ForestSpace/Segments.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the ForestSpace mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_ForestSpace
import Definitions.Def_OAI_Analysis_ForestSpace_Moduli

namespace OAI

open scoped BigOperators
open Finset

namespace ForestSpace

noncomputable section
attribute [local instance] Classical.propDecidable

/-- Every ancestral cone is a chain, the order-theoretic forest condition. -/
def ForestOrder (V : Type) [PartialOrder V] : Prop :=
  ∀ a b c : V, a ≤ c → b ≤ c → a ≤ b ∨ b ≤ a

section Basic
variable {V : Type} [PartialOrder V]

@[simp] theorem isSegment_empty : IsSegment (∅ : Finset V) := by
  simp [IsSegment]

@[simp] theorem isSegment_singleton (v : V) : IsSegment ({v} : Finset V) := by
  constructor
  · intro a ha b hb
    simp only [mem_singleton] at ha hb
    subst a
    subst b
    exact Or.inl le_rfl
  · intro a ha b hb c hac hcb
    simp only [mem_singleton] at ha hb ⊢
    subst a
    subst b
    exact le_antisymm hcb hac

omit [PartialOrder V] in
@[simp] theorem segSum_empty [PartialOrder V] (u : V → ℝ) : segSum u ∅ = 0 := by simp [segSum]
omit [PartialOrder V] in
@[simp] theorem segSum_zero [PartialOrder V] (S : Finset V) : segSum (0 : V → ℝ) S = 0 := by
  simp [segSum]
omit [PartialOrder V] in
@[simp] theorem segSum_add [PartialOrder V] (u v : V → ℝ) (S : Finset V) :
    segSum (u + v) S = segSum u S + segSum v S := by
  simp [segSum, Finset.sum_add_distrib]
omit [PartialOrder V] in
@[simp] theorem segSum_sub [PartialOrder V] (u v : V → ℝ) (S : Finset V) :
    segSum (u - v) S = segSum u S - segSum v S := by
  simp [segSum, Finset.sum_sub_distrib]
omit [PartialOrder V] in
@[simp] theorem segSum_smul [PartialOrder V] (a : ℝ) (u : V → ℝ) (S : Finset V) :
    segSum (a • u) S = a * segSum u S := by
  simp [segSum, Finset.mul_sum]

 theorem TestBound.mono {u : V → ℝ} {C D : ℝ} (h : TestBound u C) (hCD : C ≤ D) :
    TestBound u D := fun ι inst S hs hd => (h ι inst S hs hd).trans hCD

 theorem TestBound.nonneg {u : V → ℝ} {C : ℝ} (h : TestBound u C) : 0 ≤ C := by
  simpa using h PEmpty inferInstance PEmpty.elim (by simp) (by simp [Pairwise])

 theorem TestBound.single {u : V → ℝ} {C : ℝ} (h : TestBound u C)
    {S : Finset V} (hS : IsSegment S) : segSum u S ^ 2 ≤ C := by
  simpa using h Unit inferInstance (fun _ => S) (fun _ => hS)
    (by simp [Pairwise])

/-- Cutting a segment by an ancestral set produces another segment. -/
 theorem IsSegment.head {S : Finset V} (hS : IsSegment S) (H : Set V)
    (hH : IsLowerSet H) [DecidablePred (· ∈ H)] :
    IsSegment (S.filter (· ∈ H)) := by
  constructor
  · intro a ha b hb
    exact hS.1 a (mem_filter.mp ha).1 b (mem_filter.mp hb).1
  · intro a ha b hb c hac hcb
    exact mem_filter.mpr ⟨hS.2 a (mem_filter.mp ha).1 b (mem_filter.mp hb).1 c hac hcb,
      hH hcb (mem_filter.mp hb).2⟩

 theorem IsSegment.tail {S : Finset V} (hS : IsSegment S) (H : Set V)
    (hH : IsLowerSet H) [DecidablePred (· ∈ H)] :
    IsSegment (S.filter (· ∉ H)) := by
  classical
  constructor
  · intro a ha b hb
    exact hS.1 a (mem_filter.mp ha).1 b (mem_filter.mp hb).1
  · intro a ha b hb c hac hcb
    exact mem_filter.mpr ⟨hS.2 a (mem_filter.mp ha).1 b (mem_filter.mp hb).1 c hac hcb,
      fun hc => (mem_filter.mp ha).2 (hH hac hc)⟩

 theorem TestBound.restrict {u : V → ℝ} {C : ℝ} (hu : TestBound u C)
    (H : Set V) (hH : IsLowerSet H) : TestBound (H.indicator u) C := by
  classical
  intro ι inst S hS hd
  have h := hu ι inst (fun i => (S i).filter (· ∈ H))
    (fun i => (hS i).head H hH)
    (fun i j hij => (hd hij).mono (filter_subset _ _) (filter_subset _ _))
  simpa [segSum, Finset.sum_filter, Set.indicator_apply] using h

 theorem TestBound.restrict_compl {u : V → ℝ} {C : ℝ} (hu : TestBound u C)
    (H : Set V) (hH : IsLowerSet H) : TestBound (Hᶜ.indicator u) C := by
  classical
  intro ι inst S hS hd
  have h := hu ι inst (fun i => (S i).filter (· ∉ H))
    (fun i => (hS i).tail H hH)
    (fun i j hij => (hd hij).mono (filter_subset _ _) (filter_subset _ _))
  simpa [segSum, Finset.sum_filter, Set.indicator_apply] using h

end Basic

section Geometry
variable {V : Type} [PartialOrder V]

/-- A first vertex outside an ancestral set (including unattached roots). -/
def Gate (H : Set V) (g : V) : Prop := g ∉ H ∧ ∀ v, v < g → v ∈ H

/-- A coordinate vector supported on a specified set. -/
def SupportedOn (u : V → ℝ) (H : Set V) : Prop := ∀ v, v ∉ H → u v = 0

end Geometry

end

end ForestSpace

end OAI


