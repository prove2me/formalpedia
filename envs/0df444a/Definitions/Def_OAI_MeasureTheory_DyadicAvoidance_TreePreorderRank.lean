-- Prove2me | Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_TreePreorderRank
-- name    : OAI_MeasureTheory_DyadicAvoidance_TreePreorderRank
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-16T03:53:16.560393+00:00
-- url     : https://prove2.me/theorems/17e08750-206e-42e4-8890-86836016b758
-- title:
--   Preorder ranks of nodes in a complete $K$-ary tree and contiguity of subtrees
-- statement:
--   This file assigns to every node of a finite complete ordered tree its position in depth-first preorder by an explicit arithmetic formula, and proves that every subtree occupies an interval of consecutive ranks. Fix $K\in\mathbb{N}$. A node is encoded by its path from the root, a finite word $p=(p_1,\dots,p_m)$ over the alphabet $\{0,\dots,K-1\}$ of child labels, with length $|p|=m$. The root is the empty word $\varnothing$, the children of $p$ are the words $(p_1,\dots,p_m,i)$, and $p$ is an ancestor of $q$ or equal to it exactly when $p$ is a prefix of $q$. The complete tree of depth $d$ consists of all words of length at most $d$. Concatenation of words is written $pq$, and $Pip$ denotes the word $P$ followed by the label $i$ and then by the word $p$.
--
--   1. **Tree size.** $S_K(0)=1$ and $S_K(d+1)=1+K\,S_K(d)$, so that $S_K(d)=1+K+\dots+K^d$ is the number of nodes of the complete $K$-ary tree of depth $d$.
--
--   2. **Preorder rank.** $\operatorname{rank}_0(p)=0$ for every word $p$, $\operatorname{rank}_{d+1}(\varnothing)=0$, and
--   $$\operatorname{rank}_{d+1}\bigl((i,p_2,\dots,p_m)\bigr)=1+i\,S_K(d)+\operatorname{rank}_d\bigl((p_2,\dots,p_m)\bigr).$$
--   Unwinding the recursion, $\operatorname{rank}_d(p)=\sum_{k=1}^{m}\bigl(1+p_k\,S_K(d-k)\bigr)$ whenever $|p|=m\le d$; this is the zero-based position of $p$ in the root-first depth-first traversal of the depth-$d$ tree that visits the children of each node in increasing label order.
--
--   3. **Edge rank.** $\operatorname{erank}_d(p)=\operatorname{rank}_d(p)-1$, truncated at $0$. Identifying each edge with the path to its lower endpoint, this is the zero-based preorder position among the nonempty words, i.e. among the edges.
--
--   For words of length at most $d$ the file proves the following facts.
--
--   - $\operatorname{rank}_d(p)<S_K(d)$, and $\operatorname{rank}_d(p)>0$ when $p\ne\varnothing$.
--   - If $|p|\le d$, then $\operatorname{rank}_d(pq)=\operatorname{rank}_d(p)+\operatorname{rank}_{d-|p|}(q)$ for every word $q$, and $\operatorname{rank}_d(p)+S_K(d-|p|)\le S_K(d)$. If $|pq|\le d$, then $\operatorname{rank}_d(p)\le\operatorname{rank}_d(pq)<\operatorname{rank}_d(p)+S_K(d-|p|)$.
--   - Sibling order: if $i<j$ are labels and $|p|,|q|\le d$, then $\operatorname{rank}_{d+1}(ip)<\operatorname{rank}_{d+1}(jq)$; more generally, for every common prefix $P$, if $|Pip|\le d$ and $|Pjq|\le d$ then $\operatorname{rank}_d(Pip)<\operatorname{rank}_d(Pjq)$.
--   - Injectivity: if $|p|,|q|\le d$ and $\operatorname{rank}_d(p)=\operatorname{rank}_d(q)$, then $p=q$.
--   - Subtrees are intervals: for $|p|,|q|\le d$,
--   $$p\ \text{is a prefix of}\ q\iff\operatorname{rank}_d(p)\le\operatorname{rank}_d(q)<\operatorname{rank}_d(p)+S_K(d-|p|).$$
--   - The same holds for edge ranks of nonempty words of length at most $d$: $\operatorname{erank}_d(p)+1=\operatorname{rank}_d(p)$; $\operatorname{erank}_d$ is injective; $\operatorname{erank}_d(Pip)<\operatorname{erank}_d(Pjq)$ under the sibling hypotheses above; and $p$ is a prefix of $q$ if and only if $\operatorname{erank}_d(p)\le\operatorname{erank}_d(q)<\operatorname{erank}_d(p)+S_K(d-|p|)$.
--
--   These ranks turn the tree structure into arithmetic on natural numbers. If objects are laid out consecutively in the order of the edge ranks, every subtree automatically occupies one block of consecutive positions, the subtree of an earlier sibling lies entirely before that of a later sibling, and every edge comes before all edges below it.
--
--   **Formalization Note** Words are `List (Fin K)` whose head is the first step from the root, and prefixes are `List.IsPrefix`. The definitions are `size`, `rank` and `edgeRank`; `size_zero`, `size_succ`, `rank_nil` and `rank_cons` are the defining equations as simp lemmas. Natural-number subtraction truncates, so the edge rank of the root is $0$, and `rank d p` only reads the first $d$ letters of $p$; all results carry explicit length bounds.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/DyadicAvoidance/TreePreorderRank.lean

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/DyadicAvoidance/TreePreorderRank.lean by skeleton subtraction
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
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_TreePreorder

namespace OAI

namespace Problem310.TreePreorderRank

/-- Number of nodes, including the root, in the complete `K`-ary tree of depth `d`. -/
def size (K : ℕ) : ℕ → ℕ
  | 0 => 1
  | d + 1 => 1 + K * size K d

/-- Preorder rank of a path. On paths of length at most `d`, this is the usual
zero-based root-first rank in the complete tree. -/
def rank {K : ℕ} : ℕ → List (Fin K) → ℕ
  | 0, _ => 0
  | _ + 1, [] => 0
  | d + 1, i :: p => 1 + i.val * size K d + rank d p

@[simp] theorem size_zero (K : ℕ) : size K 0 = 1 := rfl
@[simp] theorem size_succ (K d : ℕ) : size K (d + 1) = 1 + K * size K d := rfl
@[simp] theorem rank_nil {K : ℕ} (d : ℕ) : rank d ([] : List (Fin K)) = 0 := by
  cases d <;> rfl
@[simp] theorem rank_cons {K : ℕ} (d : ℕ) (i : Fin K) (p : List (Fin K)) :
    rank (d + 1) (i :: p) = 1 + i.val * size K d + rank d p := rfl

/-- Every valid node has rank strictly below the total number of nodes. -/
theorem rank_lt_size {K d : ℕ} {p : List (Fin K)} (hp : p.length ≤ d) :
    rank d p < size K d := by
  induction d generalizing p with
  | zero => simp [rank, size]
  | succ d ih =>
    cases p with
    | nil => simp [rank, size]
    | cons i p =>
      have hp' : p.length ≤ d := by simpa using hp
      have hr := ih hp'
      have hi : i.val + 1 ≤ K := i.isLt
      have hm := Nat.mul_le_mul_right (size K d) hi
      simp only [rank_cons, size_succ]
      nlinarith

/-- A nonroot valid node has positive rank. -/
theorem rank_pos {K d : ℕ} {p : List (Fin K)}
    (hp : p.length ≤ d) (hne : p ≠ []) : 0 < rank d p := by
  cases p with
  | nil => exact (hne rfl).elim
  | cons i p =>
    cases d with
    | zero => simp at hp
    | succ d => simp [rank]

/-- Descending into a node adds the local preorder rank in that node's subtree. -/
theorem rank_append {K d : ℕ} {p : List (Fin K)} (hp : p.length ≤ d)
    (q : List (Fin K)) :
    rank d (p ++ q) = rank d p + rank (d - p.length) q := by
  induction p generalizing d with
  | nil => simp
  | cons i p ih =>
    cases d with
    | zero => simp at hp
    | succ d =>
      have hp' : p.length ≤ d := by simpa using hp
      simp only [List.cons_append, rank_cons, List.length_cons, Nat.add_sub_add_right]
      rw [ih hp']
      omega

/-- A subtree occupies one contiguous interval of the preorder ranks. -/
theorem rank_append_bounds {K d : ℕ} {p q : List (Fin K)}
    (hpq : (p ++ q).length ≤ d) :
    rank d p ≤ rank d (p ++ q) ∧
      rank d (p ++ q) < rank d p + size K (d - p.length) := by
  have hp : p.length ≤ d := by simp only [List.length_append] at hpq; omega
  have hq : q.length ≤ d - p.length := by simp only [List.length_append] at hpq; omega
  rw [rank_append hp]
  exact ⟨Nat.le_add_right _ _, Nat.add_lt_add_left (rank_lt_size hq) _⟩

/-- The entire subtree of an earlier child precedes the entire subtree of a later child. -/
theorem rank_cons_lt_rank_cons {K d : ℕ} {i j : Fin K} {p q : List (Fin K)}
    (hij : i < j) (hp : p.length ≤ d) (_hq : q.length ≤ d) :
    rank (d + 1) (i :: p) < rank (d + 1) (j :: q) := by
  have hr := rank_lt_size hp
  have hi : i.val + 1 ≤ j.val := hij
  have hm := Nat.mul_le_mul_right (size K d) hi
  simp only [rank_cons]
  nlinarith

/-- Ordered sibling subtrees remain ordered after any common ancestral prefix. -/
theorem rank_sibling_descendants_lt {K d : ℕ} {P p q : List (Fin K)} {i j : Fin K}
    (hij : i < j) (hp : (P ++ i :: p).length ≤ d)
    (hq : (P ++ j :: q).length ≤ d) :
    rank d (P ++ i :: p) < rank d (P ++ j :: q) := by
  have hP : P.length ≤ d := by simp only [List.length_append, List.length_cons] at hp; omega
  rw [rank_append hP, rank_append hP]
  cases heq : d - P.length with
  | zero => simp only [List.length_append, List.length_cons] at hp; omega
  | succ k =>
    have hp' : p.length ≤ k := by simp only [List.length_append, List.length_cons] at hp; omega
    have hq' : q.length ≤ k := by simp only [List.length_append, List.length_cons] at hq; omega
    exact Nat.add_lt_add_left (rank_cons_lt_rank_cons hij hp' hq') _

/-- Preorder ranks distinguish every two valid paths. -/
theorem rank_injective_on {K d : ℕ} {p q : List (Fin K)}
    (hp : p.length ≤ d) (hq : q.length ≤ d) (heq : rank d p = rank d q) : p = q := by
  induction d generalizing p q with
  | zero =>
    have hp0 : p = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hp)
    have hq0 : q = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hq)
    exact hp0.trans hq0.symm
  | succ d ih =>
    cases p with
    | nil =>
      cases q with
      | nil => rfl
      | cons j q => simp only [rank_nil, rank_cons] at heq; omega
    | cons i p =>
      cases q with
      | nil => simp [rank] at heq
      | cons j q =>
        have hp' : p.length ≤ d := by simpa using hp
        have hq' : q.length ≤ d := by simpa using hq
        have hij : i = j := by
          rcases lt_trichotomy i j with h | h | h
          · exact False.elim ((rank_cons_lt_rank_cons h hp' hq').ne heq)
          · exact h
          · exact False.elim ((rank_cons_lt_rank_cons h hq' hp').ne heq.symm)
        subst j
        have heq' : rank d p = rank d q := by simpa only [rank_cons, Nat.add_left_cancel_iff] using heq
        exact congrArg (List.cons i) (ih hp' hq' heq')

/-- The interval occupied by a subtree is contained in the whole tree's interval. -/
theorem subtree_end_le_size {K d : ℕ} {p : List (Fin K)} (hp : p.length ≤ d) :
    rank d p + size K (d - p.length) ≤ size K d := by
  induction d generalizing p with
  | zero => simp [rank, size]
  | succ d ih =>
    cases p with
    | nil => simp
    | cons i p =>
      have hp' : p.length ≤ d := by simpa using hp
      have he := ih hp'
      have hi : i.val + 1 ≤ K := i.isLt
      have hm := Nat.mul_le_mul_right (size K d) hi
      simp only [rank_cons, List.length_cons, Nat.add_sub_add_right, size_succ]
      nlinarith

/-- The descendants of a path are exactly a contiguous half-open interval of ranks. -/
theorem isPrefix_iff_rank_bounds {K d : ℕ} {p q : List (Fin K)}
    (hp : p.length ≤ d) (hq : q.length ≤ d) :
    List.IsPrefix p q ↔ rank d p ≤ rank d q ∧
      rank d q < rank d p + size K (d - p.length) := by
  constructor
  · rintro ⟨s, rfl⟩
    exact rank_append_bounds hq
  · intro h
    induction d generalizing p q with
    | zero =>
      have hp0 : p = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hp)
      subst p
      exact List.nil_prefix
    | succ d ih =>
      cases p with
      | nil => exact List.nil_prefix
      | cons i p =>
        cases q with
        | nil =>
          have hpos := rank_pos hp (by simp)
          simp only [rank_nil] at h
          omega
        | cons j q =>
          have hp' : p.length ≤ d := by simpa using hp
          have hq' : q.length ≤ d := by simpa using hq
          have hpEnd := subtree_end_le_size hp'
          have hrq := rank_lt_size hq'
          simp only [rank_cons, List.length_cons, Nat.add_sub_add_right] at h
          have hij : i = j := by
            rcases lt_trichotomy i j with hij | hij | hji
            · have hi : i.val + 1 ≤ j.val := hij
              have hm := Nat.mul_le_mul_right (size K d) hi
              exfalso
              nlinarith [h.2]
            · exact hij
            · have hi : j.val + 1 ≤ i.val := hji
              have hm := Nat.mul_le_mul_right (size K d) hi
              exfalso
              nlinarith [h.1]
          subst j
          apply List.cons_prefix_cons.mpr
          refine ⟨rfl, ih hp' hq' ?_⟩
          omega

/-- Zero-based rank among edges, obtained by removing the root's rank. -/
def edgeRank {K : ℕ} (d : ℕ) (p : List (Fin K)) : ℕ := rank d p - 1

theorem edgeRank_add_one {K d : ℕ} {p : List (Fin K)}
    (hp : p.length ≤ d) (hne : p ≠ []) : edgeRank d p + 1 = rank d p := by
  have := rank_pos hp hne
  unfold edgeRank
  omega

theorem edgeRank_injective_on {K d : ℕ} {p q : List (Fin K)}
    (hp : p.length ≤ d) (hq : q.length ≤ d) (hp0 : p ≠ []) (hq0 : q ≠ [])
    (heq : edgeRank d p = edgeRank d q) : p = q := by
  apply rank_injective_on hp hq
  rw [← edgeRank_add_one hp hp0, ← edgeRank_add_one hq hq0, heq]

theorem edgeRank_sibling_descendants_lt {K d : ℕ} {P p q : List (Fin K)} {i j : Fin K}
    (hij : i < j) (hp : (P ++ i :: p).length ≤ d)
    (hq : (P ++ j :: q).length ≤ d) :
    edgeRank d (P ++ i :: p) < edgeRank d (P ++ j :: q) := by
  have hlt := rank_sibling_descendants_lt hij hp hq
  have hpos := rank_pos hp (by simp)
  unfold edgeRank
  omega

/-- Edge ranks give the same exact contiguous-subtree characterization without the root slot. -/
theorem isPrefix_iff_edgeRank_bounds {K d : ℕ} {p q : List (Fin K)}
    (hp : p.length ≤ d) (hq : q.length ≤ d) (hp0 : p ≠ []) (hq0 : q ≠ []) :
    List.IsPrefix p q ↔ edgeRank d p ≤ edgeRank d q ∧
      edgeRank d q < edgeRank d p + size K (d - p.length) := by
  rw [isPrefix_iff_rank_bounds hp hq]
  have hpR := edgeRank_add_one hp hp0
  have hqR := edgeRank_add_one hq hq0
  omega

end Problem310.TreePreorderRank

end OAI


