-- Prove2me | Definitions.Def_OAI_Analysis_SegmentLenses_TreeGeometry
-- name    : OAI_Analysis_SegmentLenses_TreeGeometry
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-14T20:53:10.650061+00:00
-- url     : https://prove2.me/theorems/8a511f4a-d285-4330-9e16-cd871e642651
-- title:
--   Tree orders with interval segments, the prefix tree and forest, gates and boundary sums
-- statement:
--   Let $V$ be partially ordered by an ancestry relation $\le$, where $a\le b$ reads "$a$ is an ancestor of $b$".
--
--   1. **Tree order.** The order is a *tree order* if any two ancestors of a common vertex are comparable: $a\le c$ and $b\le c$ imply $a\le b$ or $b\le a$.
--   2. **Interval segments.** A segment system on $V$ has *interval segments* if its segments are exactly the order intervals. That is, a finite set $S\subseteq V$ is a segment iff there are $a\le b$ with
--   $$
--   S=[a,b]=\{v\in V:\ a\le v\le b\}.
--   $$
--   3. **The infinite tree.** Let $\mathbb{N}^{<\omega}$ be the set of finite words over $\mathbb{N}$, ordered by the prefix relation. This is a partial order and a tree order. With the base segment system, whose segments are the prefix intervals, it has interval segments. It is also locally finite: $[a,b]$ consists of the prefixes of $b$ that extend $a$.
--   4. **The forest.** Let the forest vertices be the pairs $(n,w)$ with $n\ge1$ and $w\in\mathbb{N}^{<\omega}$ of length at most $n$. Order them by $(n,w)\le(m,w')$ iff $n=m$ and $w$ is a prefix of $w'$. This is the disjoint union, over $n\ge1$, of the $\mathbb{N}$-branching rooted trees of depth $n$. The same four structures hold: a partial order, a tree order, interval segments, and local finiteness.
--   5. **Gates.** For a finite $H\subseteq V$, a vertex $g$ is a *gate* of $H$ if $g\notin H$ and every strict ancestor $v<g$ lies in $H$.
--   6. **Endpoints of segments.** Now let $V$ be a locally finite tree order with decidable equality and interval segments. For a segment family $\mathcal F$ (pairwise disjoint segments) and a member $S\in\mathcal F$, a chosen pair $\mathrm{first}(S)\le\mathrm{last}(S)$ satisfies $S=[\mathrm{first}(S),\mathrm{last}(S)]$.
--   7. **Boundary sums.** For a finitely supported $p:V\to\mathbb{R}$ and $g\in V$, the boundary sum is
--   $$
--   \partial_{\mathcal F}p(g)=\sum_{S\in\mathcal F,\ g\in S}\ \sum_{v\in S}p(v).
--   $$
--   Since the members of $\mathcal F$ are disjoint, this is the total of $p$ over the member containing $g$, or $0$ if no member contains $g$.
--
--   The two concrete structures are the vertex sets of the main midpoint-lens theorem. The abstract classes let every later estimate be proved once, for an arbitrary locally finite tree order with interval segments. In a tree order every interval $[a,b]$ is a chain, so segments are pieces of ancestral paths. The gates of an ancestral set $H$ are the vertices immediately outside $H$, where such paths leave $H$.
--
--   **Formalization Note** `TreeOrder` and `IntervalSegments` are `Prop`-valued classes. The instances for words (`List ℕ`) are `infiniteOrder`, `infiniteTreeOrder`, `infiniteIntervalSegments` and `infiniteLocallyFinite`; the forest analogues are prefixed `forest`. `IntervalSegments` holds by `Iff.rfl` because the base segment systems are defined through `IsInterval`. `presentation` uses choice to pick the endpoints; `first`, `last` and `repr` expose them. `Gate` and `boundary` are defined in a section whose variables carry the tree-setting assumptions.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/SegmentLenses/TreeGeometry.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/SegmentLenses/TreeGeometry.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the MidpointLenses mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_MidpointLenses
import Definitions.Def_OAI_Analysis_SegmentLenses_Basic

namespace OAI

/-!
# Ancestry, segment splitting, and opposite crossings
-/

noncomputable section

open scoped BigOperators
open Finset

namespace SegmentLenses

class TreeOrder (V : Type*) [PartialOrder V] : Prop where
  lower_chain : ∀ {a b c : V}, a ≤ c → b ≤ c → a ≤ b ∨ b ≤ a

class IntervalSegments (V : Type*) [PartialOrder V] [SegmentSystem V] : Prop where
  iff_interval : ∀ S : Finset V, SegmentSystem.isSegment S ↔ IsInterval (· ≤ ·) S

instance infiniteOrder : PartialOrder InfiniteVertex where
  le := List.IsPrefix
  lt := fun a b => a.IsPrefix b ∧ ¬b.IsPrefix a
  le_refl := List.prefix_refl
  le_trans := fun _ _ _ => List.IsPrefix.trans
  le_antisymm := fun _ _ => prefix_antisymm

instance infiniteTreeOrder : TreeOrder InfiniteVertex where
  lower_chain := List.prefix_or_prefix_of_prefix

instance infiniteIntervalSegments : IntervalSegments InfiniteVertex where
  iff_interval _ := Iff.rfl

instance infiniteLocallyFinite : LocallyFiniteOrder InfiniteVertex := by
  classical
  exact LocallyFiniteOrder.ofIcc InfiniteVertex
    (fun a b => b.inits.toFinset.filter (fun v => a.IsPrefix v))
    (fun a b v => by simp [List.mem_inits, and_comm, LE.le])

instance forestOrder : PartialOrder ForestVertex where
  le := ForestAncestor
  lt := fun a b => ForestAncestor a b ∧ ¬ForestAncestor b a
  le_refl := forestAncestor_refl
  le_trans := fun _ _ _ hab hbc => ⟨hab.1.trans hbc.1, hab.2.trans hbc.2⟩
  le_antisymm := fun _ _ => forestAncestor_antisymm

instance forestTreeOrder : TreeOrder ForestVertex where
  lower_chain := by
    intro a b c hac hbc
    rcases List.prefix_or_prefix_of_prefix hac.2 hbc.2 with hab | hba
    · exact Or.inl ⟨hac.1.trans hbc.1.symm, hab⟩
    · exact Or.inr ⟨hbc.1.trans hac.1.symm, hba⟩

instance forestIntervalSegments : IntervalSegments ForestVertex where
  iff_interval _ := Iff.rfl

instance forestLocallyFinite : LocallyFiniteOrder ForestVertex :=
  LocallyFiniteOrder.ofFiniteIcc (by
    intro a b
    apply Set.Finite.of_injOn (f := fun v : ForestVertex => v.val.2)
      (t := {w : List ℕ | w.IsPrefix b.val.2})
    · intro v hv
      exact hv.2.2
    · intro v hv w hw he
      apply Subtype.ext
      exact Prod.ext (hv.2.1.trans hw.2.1.symm) he
    · exact b.val.2.inits.finite_toSet.subset (by
        intro w hw
        exact (List.mem_inits w b.val.2).mpr hw))

section TreeGeometry
variable {V : Type*} [decidableEqV : DecidableEq V] [partialOrderV : PartialOrder V] [locallyFiniteOrderV : LocallyFiniteOrder V] [treeOrderV : TreeOrder V]
  [segmentSystemV : SegmentSystem V] [intervalSegmentsV : IntervalSegments V]

def Gate (H : Finset V) (g : V) : Prop :=
  g ∉ H ∧ ∀ v, v < g → v ∈ H

namespace SegmentFamily

def presentation (F : SegmentFamily V) (S : F.sets) :
    {q : V × V // q.1 ≤ q.2 ∧ S.val = Finset.Icc q.1 q.2} := by
  classical
  have hs := (IntervalSegments.iff_interval S.val).mp (F.segment S.val S.property)
  apply Classical.choice
  obtain ⟨a, b, hab, hs⟩ := hs
  exact ⟨⟨(a, b), hab, Finset.ext (fun v => by simpa only [Finset.mem_Icc] using hs v)⟩⟩

def first (F : SegmentFamily V) (S : F.sets) : V := (F.presentation S).val.1

def last (F : SegmentFamily V) (S : F.sets) : V := (F.presentation S).val.2

theorem repr (F : SegmentFamily V) (S : F.sets) :
    S.val = Finset.Icc (F.first S) (F.last S) := by
  have _ := decidableEqV
  have _ := treeOrderV
  exact (F.presentation S).property.2

def boundary (F : SegmentFamily V) (p : V →₀ ℝ) (g : V) : ℝ :=
  ∑ S ∈ F.sets, if g ∈ S then ∑ v ∈ S, p v else 0

end SegmentFamily

end TreeGeometry

end SegmentLenses

end

end OAI


