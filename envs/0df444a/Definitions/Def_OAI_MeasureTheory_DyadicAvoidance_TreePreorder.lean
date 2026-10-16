-- Prove2me | Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_TreePreorder
-- name    : OAI_MeasureTheory_DyadicAvoidance_TreePreorder
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-16T03:51:36.93999+00:00
-- url     : https://prove2.me/theorems/41e4ffc0-a375-4d4b-ae01-5a861540a52b
-- title:
--   Depth-first preorder enumeration of the edges of a complete ordered tree
-- statement:
--   Fix natural numbers $q$ (the number of children of each internal vertex) and $d$ (the depth). The vertices of the complete ordered $q$-ary tree of depth $d$ are the words over the alphabet $\{0,1,\dots,q-1\}$ of length at most $d$, the empty word being the root and $pi$ being the child of $p$ with label $i$. The edge entering a non-root vertex is identified with that vertex, so the edges are the nonempty words of length at most $d$.
--
--   1. **Edge paths in preorder.** The list $\mathcal{P}_d$ of words is defined by letting $\mathcal{P}_0$ be the empty list and, writing $\mathcal{P}_d=(p_1,\dots,p_{N_d})$,
--   $$\mathcal{P}_{d+1}=B_0\,\Vert\,B_1\,\Vert\cdots\Vert\,B_{q-1},\qquad B_i=\big(i,\ i\,p_1,\ i\,p_2,\ \dots,\ i\,p_{N_d}\big),$$
--   where $\Vert$ is concatenation of lists, $i$ stands for the one-letter word and $i\,p$ for the word $p$ with the letter $i$ prepended. This is the depth-first preorder of the edges: each edge is followed by the contiguous block of all edges below it, and siblings appear in increasing order of their labels.
--   2. **Edge count.** $N_0=0$ and $N_{d+1}=q\,(1+N_d)$; hence $N_d=q+q^2+\cdots+q^d$.
--   3. **The edge type.** $\mathrm{Edge}(q,d)$ is the finite set of words occurring in $\mathcal{P}_d$. Any nonempty word $p$ with $|p|\le d$ defines an edge, and for a word $P$ with $|P|<d$ and a label $i$ the child edge of $P$ with label $i$ is the word $Pi$ obtained by appending $i$.
--   4. **Canonical enumeration.** The bijection $\mathrm{Edge}(q,d)\to\{0,1,\dots,N_d-1\}$ sends an edge to its position in the list $\mathcal{P}_d$.
--
--   The file proves that a word $p$ occurs in $\mathcal{P}_d$ if and only if $p$ is nonempty and $|p|\le d$, that $\mathcal{P}_d$ has length $N_d$ and no repeated entries, and that every word in the block $B_i$ begins with the letter $i$; consequently $\mathrm{Edge}(q,d)$ has exactly $N_d$ elements and every edge is a nonempty word.
--
--   In the construction of a compact set avoiding the affine copies $\{x+s\,2^{-n}:n\ge1\}$, $s\neq0$, of the dyadic sequence, index windows are attached to the edges of a routing tree in this order. Because every edge is immediately followed by the block of its descendants, the windows of a subtree occupy one contiguous stretch of indices, and the edges on the path from the root to that subtree come earlier.
--
--   **Formalization Note** Words are lists `List (Fin q)`. The objects are `edgePaths q d` (built with `List.flatMap` over `List.finRange q`), `edgeCount q d`, the subtype `Edge q d` with its `Fintype` instance, `mkEdge`, `childEdge P hP i` (the word `P ++ [i]`, requiring `P.length < d`) and `edgeEquivFin q d : Edge q d ≃ Fin (edgeCount q d)`, built from `List.Nodup.getEquiv`. The facts are `mem_edgePaths_iff`, `length_edgePaths`, `nodup_edgePaths`, `mem_childBlock_prefix`, `edge_nonempty`, `card_Edge`, `mkEdge_val` and `childEdge_val`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/DyadicAvoidance/TreePreorder.lean

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/DyadicAvoidance/TreePreorder.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the DyadicAvoidance mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_DyadicAvoidance
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_PeriodicBasic
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_GridSeparation
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_FiniteTableModel
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_OrderedRouting
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_RoutingPath
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_CenterRouteExposure
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_ExceptionalCenters
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_CenterFailureBound
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_FirstDefault
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_ConcreteLabelMeasures
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_CenterFirstDefault
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_RandomSetDensity
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_RoutedSetDensity
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_RoutedExposure
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_FirstDefaultSelection
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_FiniteLocalPredicate
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_WindowData
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_WindowTableModel
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_StableRoutingBridge
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_WindowExceptionalTransfer
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_TrialAddresses
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_WindowTrialAddresses
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_ConcreteWindowAtom
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_PeriodicEnvelope
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_GlobalFromPeriodic
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_GridGeometry
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_GridMeasure
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_GridStability
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_WindowPlacement
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_WindowRecursion
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_PackedWindowSpan

namespace OAI

noncomputable section

namespace Problem310.TreePreorder

/-- Edge paths in the complete ordered `q`-ary tree, in depth-first preorder. -/
def edgePaths (q : ℕ) : ℕ → List (List (Fin q))
  | 0 => []
  | d + 1 => (List.finRange q).flatMap fun i =>
      [i] :: (edgePaths q d).map (List.cons i)

/-- Number of edges in the complete tree. -/
def edgeCount (q : ℕ) : ℕ → ℕ
  | 0 => 0
  | d + 1 => q * (1 + edgeCount q d)

@[simp] theorem edgePaths_zero (q : ℕ) : edgePaths q 0 = [] := rfl

@[simp] theorem edgePaths_succ (q d : ℕ) :
    edgePaths q (d + 1) = (List.finRange q).flatMap (fun i =>
      [i] :: (edgePaths q d).map (List.cons i)) := rfl

/-- Exactly the nonempty paths of length at most the tree depth occur. -/
theorem mem_edgePaths_iff (q d : ℕ) (p : List (Fin q)) :
    p ∈ edgePaths q d ↔ p ≠ [] ∧ p.length ≤ d := by
  induction d generalizing p with
  | zero => simp [edgePaths]
  | succ d ih =>
      cases p with
      | nil => simp [edgePaths]
      | cons i p =>
          simp only [edgePaths, List.mem_flatMap, List.mem_finRange, true_and,
            List.mem_cons, List.cons.injEq, List.mem_map, List.length_cons,
            ]
          constructor
          · rintro ⟨j, h | ⟨p', hp', h⟩⟩
            · rcases h with ⟨rfl, rfl⟩
              simp
            · rcases h with ⟨rfl, rfl⟩
              have hlen := (ih p').mp hp'
              exact ⟨by simp, Nat.succ_le_succ hlen.2⟩
          · intro hp
            by_cases he : p = []
            · subst p
              exact ⟨i, Or.inl ⟨rfl, rfl⟩⟩
            · exact ⟨i, Or.inr ⟨p, (ih p).mpr ⟨he, by omega⟩, ⟨rfl, rfl⟩⟩⟩

@[simp] theorem length_edgePaths (q d : ℕ) :
    (edgePaths q d).length = edgeCount q d := by
  induction d with
  | zero => rfl
  | succ d ih =>
      simp [edgePaths, edgeCount, List.length_flatMap, ih, add_comm]

/-- Each child block consists entirely of paths with that child as first entry. -/
theorem mem_childBlock_prefix (q d : ℕ) (i : Fin q) (p : List (Fin q))
    (hp : p ∈ [i] :: (edgePaths q d).map (List.cons i)) :
    ∃ s, p = i :: s := by
  rcases List.mem_cons.mp hp with h | h
  · exact ⟨[], h⟩
  · obtain ⟨s, hs, h⟩ := List.mem_map.mp h
    exact ⟨s, h.symm⟩

/-- The preorder contains no duplicate edge path. -/
theorem nodup_edgePaths (q d : ℕ) : (edgePaths q d).Nodup := by
  induction d with
  | zero => simp [edgePaths]
  | succ d ih =>
      rw [edgePaths_succ, List.nodup_flatMap]
      constructor
      · intro i hi
        rw [List.nodup_cons]
        constructor
        · intro hm
          obtain ⟨p, hp, heq⟩ := List.mem_map.mp hm
          have hp0 : p = [] := (List.cons.inj heq).2
          subst p
          simp [mem_edgePaths_iff] at hp
        · exact ih.map (by intro a b h; exact (List.cons.inj h).2)
      · apply (List.nodup_finRange q).imp
        intro i j hij p hp hq
        obtain ⟨s, rfl⟩ := mem_childBlock_prefix q d i p hp
        obtain ⟨t, heq⟩ := mem_childBlock_prefix q d j (i :: s) hq
        exact hij (List.cons.inj heq).1

/-- The finite type of tree edges, represented by nonempty bounded-depth paths. -/
def Edge (q d : ℕ) := {p : List (Fin q) // p ∈ edgePaths q d}

instance (q d : ℕ) : Fintype (Edge q d) := by
  classical
  unfold Edge
  exact Fintype.ofFinset (edgePaths q d).toFinset (by intro p; exact List.mem_toFinset)

@[simp] theorem edge_nonempty {q d : ℕ} (e : Edge q d) : e.val ≠ [] :=
  ((mem_edgePaths_iff q d e.val).mp e.property).1

/-- Convert a nonempty bounded path into the finite edge type. -/
def mkEdge {q d : ℕ} (p : List (Fin q)) (hne : p ≠ []) (hlen : p.length ≤ d) :
    Edge q d := ⟨p, (mem_edgePaths_iff q d p).mpr ⟨hne, hlen⟩⟩

@[simp] theorem mkEdge_val {q d : ℕ} (p : List (Fin q))
    (hne : p ≠ []) (hlen : p.length ≤ d) :
    (mkEdge p hne hlen).val = p := rfl

/-- The preorder gives the canonical enumeration of finite tree edges. -/
def edgeEquivFin (q d : ℕ) : Edge q d ≃ Fin (edgeCount q d) :=
  (List.Nodup.getEquiv (edgePaths q d) (nodup_edgePaths q d)).symm.trans
    (finCongr (length_edgePaths q d))

@[simp] theorem card_Edge (q d : ℕ) : Fintype.card (Edge q d) = edgeCount q d := by
  rw [Fintype.card_congr (edgeEquivFin q d), Fintype.card_fin]

/-- Edges corresponding to appending a child at a strict internal node. -/
def childEdge {q d : ℕ} (P : List (Fin q)) (hP : P.length < d) (i : Fin q) :
    Edge q d := mkEdge (P ++ [i]) (by simp) (by simp; omega)

@[simp] theorem childEdge_val {q d : ℕ} (P : List (Fin q))
    (hP : P.length < d) (i : Fin q) : (childEdge P hP i).val = P ++ [i] := rfl

end Problem310.TreePreorder

end

end OAI


