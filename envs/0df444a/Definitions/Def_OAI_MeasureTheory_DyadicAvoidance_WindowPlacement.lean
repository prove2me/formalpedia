-- Prove2me | Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_WindowPlacement
-- name    : OAI_MeasureTheory_DyadicAvoidance_WindowPlacement
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-16T03:47:41.895779+00:00
-- url     : https://prove2.me/theorems/6cf61956-747e-4bd2-9892-3c415fb9f1dc
-- title:
--   Placing index windows in sequence with gaps of $g$ unused indices
-- statement:
--   This file places a sequence of finite windows of natural-number indices one after another, starting at index $3$, with exactly $g$ unused indices between consecutive windows. Let $\ell=(\ell_i)_{i\in\mathbb{N}}$ be a sequence of window lengths in $\mathbb{N}$ and $g\in\mathbb{N}$ a gap size.
--
--   1. **Start indices.** $s_0=3$ and $s_{i+1}=s_i+\ell_i+g$, so that
--   $$s_i=3+\sum_{k=0}^{i-1}(\ell_k+g).$$
--   2. **End indices and windows.** $f_i=s_i+\ell_i-1$ and
--   $$W_i=\{n\in\mathbb{N}: s_i\le n\le f_i\}=\{s_i,s_i+1,\dots,s_i+\ell_i-1\},$$
--   a block of $\ell_i$ consecutive integers (empty when $\ell_i=0$).
--   3. **Length lookup.** For a finite list $L=(L_0,\dots,L_{m-1})$ of natural numbers, $\ell^L_i=L_i$ for $i<m$ and $\ell^L_i=0$ for $i\ge m$; this converts a finite list of lengths into a length sequence.
--
--   The file proves the elementary placement facts: $s$ is nondecreasing and $s_i\ge3$; $f_i+1=s_i+\ell_i$; $f$ is nondecreasing even if some lengths vanish; $s_{i+1}=f_i+g+1$, and more generally $f_i+g<s_j$ whenever $i<j$; $n\in W_i$ if and only if $s_i\le n\le f_i$; $W_i$ has exactly $\ell_i$ elements; and for all $i,m\in\mathbb{N}$
--   $$s_{i+m}=s_i+\sum_{k=0}^{m-1}(\ell_{i+k}+g),\qquad f_{i+m}+g+1=s_i+\sum_{k=0}^{m}(\ell_{i+k}+g).$$
--   Consequently, if $\sum_{k=0}^{m}(\ell_{i+k}+g)\le2r+g$ for some $r\in\mathbb{N}$, then $f_{i+m}+1\le s_i+2r$. For the lookup it proves $\sum_{i<m}\ell^L_i=\sum_jL_j$; that for a list $X$ with $i$-th entry $x$ and a map $\varphi$ into $\mathbb{N}$, the lookup of the mapped list $\varphi(X)$ at position $i$ is $\varphi(x)$ (in particular at the position of the first occurrence of $x$); and that for a concatenated list $L=A\,B\,C$ one has $\ell^L_{|A|+k}=\ell^B_k$ for $k<|B|$, hence $\sum_{k<|B|}(\ell^L_{|A|+k}+g)=\sum_{r\in B}(r+g)$.
--
--   In the construction of a compact set avoiding the affine copies $\{x+s\,2^{-n}:n\ge1\}$, $s\neq0$, of the dyadic sequence, these windows are attached to the edges of a finite tree listed in depth-first preorder. The gaps of size $g$ separate every window from all later ones, which lets small dyadic translations indexed by a later window leave the grid keys of earlier windows unchanged, and the block bound controls the last index of a contiguous block of windows by twice a prescribed length.
--
--   **Formalization Note** The objects are `start len g`, `finish len g` (defined with natural-number subtraction, which never truncates because $s_i\ge3$), `window len g i` as the finite interval `Finset.Icc`, and `lengthAt L i = L[i]?.getD 0`. The listed facts are `start_mono`, `three_le_start`, `finish_add_one`, `finish_mono`, `consecutive_gap`, `gap_of_lt`, `mem_window`, `card_window`, `start_add`, `block_endpoint`, `block_endpoint_le`, `sum_lengthAt`, `lengthAt_map_of_getElem?`, `lengthAt_map_idxOf`, `lengthAt_segment` and `sum_lengthAt_segment`. Two private lemmas `ite_eq_left` and `ite_eq_right` are compatibility shims.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/DyadicAvoidance/WindowPlacement.lean

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/DyadicAvoidance/WindowPlacement.lean by skeleton subtraction
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

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

universe u_α

open scoped BigOperators

namespace Problem310.WindowPlacement

/-- Place windows in preorder, reserving `g` unused indices after each window. -/
def start (len : ℕ → ℕ) (g : ℕ) : ℕ → ℕ
  | 0 => 3
  | i + 1 => start len g i + len i + g

def finish (len : ℕ → ℕ) (g i : ℕ) : ℕ := start len g i + len i - 1

def window (len : ℕ → ℕ) (g i : ℕ) : Finset ℕ :=
  Finset.Icc (start len g i) (finish len g i)

/-- Extract a window length from a finite preorder list, using zero outside the list. -/
def lengthAt (L : List ℕ) (i : ℕ) : ℕ := L[i]?.getD 0

theorem lengthAt_map_of_getElem? {α : Type u_α} (f : α → ℕ)
    {L : List α} {i : ℕ} {x : α} (h : L[i]? = some x) :
    lengthAt (L.map f) i = f x := by
  simp only [lengthAt, List.getElem?_map, h, Option.map_some, Option.getD_some]

theorem lengthAt_map_idxOf {α : Type u_α} [BEq α] [LawfulBEq α]
    (f : α → ℕ) {L : List α} {x : α} (hx : x ∈ L) :
    lengthAt (L.map f) (L.idxOf x) = f x :=
  lengthAt_map_of_getElem? f (List.getElem?_idxOf hx)

theorem sum_lengthAt (L : List ℕ) :
    (∑ i ∈ Finset.range L.length, lengthAt L i) = L.sum := by
  induction L with
  | nil => simp [lengthAt]
  | cons a L ih =>
      simp only [List.length_cons, Finset.sum_range_succ', lengthAt,
        List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some,
        List.sum_cons]
      change (∑ i ∈ Finset.range L.length, lengthAt L i) + a = a + L.sum
      rw [ih, Nat.add_comm]

theorem lengthAt_segment (pre block post : List ℕ) {k : ℕ} (hk : k < block.length) :
    lengthAt (pre ++ block ++ post) (pre.length + k) = lengthAt block k := by
  simp only [lengthAt, List.append_assoc, List.getElem?_append]
  rw [ite_eq_right (by omega)]
  simp only [Nat.add_sub_cancel_left]
  rw [ite_eq_left hk]

/-- Translate a consecutive preorder block's list sum into the prefix-sum
interface used by the endpoint and resolution lemmas. -/
theorem sum_lengthAt_segment (pre block post : List ℕ) (g : ℕ) :
    (∑ k ∈ Finset.range block.length,
      (lengthAt (pre ++ block ++ post) (pre.length + k) + g)) =
      (block.map (fun r => r + g)).sum := by
  calc
    _ = ∑ k ∈ Finset.range block.length, (lengthAt block k + g) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [lengthAt_segment pre block post (Finset.mem_range.mp hk)]
    _ = block.sum + block.length * g := by
      rw [Finset.sum_add_distrib, sum_lengthAt]
      simp
    _ = _ := by
      induction block with
      | nil => simp
      | cons a block ih =>
          simp only [List.sum_cons, List.length_cons, List.map_cons]
          rw [← ih]
          simp only [Nat.add_mul, Nat.one_mul]
          omega

@[simp] theorem start_zero (len : ℕ → ℕ) (g : ℕ) : start len g 0 = 3 := rfl

@[simp] theorem start_succ (len : ℕ → ℕ) (g i : ℕ) :
    start len g (i + 1) = start len g i + len i + g := rfl

theorem start_mono (len : ℕ → ℕ) (g : ℕ) : Monotone (start len g) := by
  apply monotone_nat_of_le_succ
  intro i
  simp only [start_succ]
  omega

theorem three_le_start (len : ℕ → ℕ) (g i : ℕ) : 3 ≤ start len g i := by
  simpa using start_mono len g (Nat.zero_le i)

theorem finish_add_one (len : ℕ → ℕ) (g i : ℕ) :
    finish len g i + 1 = start len g i + len i := by
  have := three_le_start len g i
  unfold finish
  omega

/-- Endpoints are nondecreasing even if some windows have length zero. -/
theorem finish_mono (len : ℕ → ℕ) (g : ℕ) : Monotone (finish len g) := by
  apply monotone_nat_of_le_succ
  intro i
  have hi := finish_add_one len g i
  have hj := finish_add_one len g (i + 1)
  rw [start_succ] at hj
  omega

theorem consecutive_gap (len : ℕ → ℕ) (g i : ℕ) :
    start len g (i + 1) = finish len g i + g + 1 := by
  rw [start_succ]
  have := finish_add_one len g i
  omega

/-- Every later window starts strictly beyond the earlier endpoint and its gap. -/
theorem gap_of_lt (len : ℕ → ℕ) (g : ℕ) {i j : ℕ} (hij : i < j) :
    finish len g i + g < start len g j := by
  have hm := start_mono len g (Nat.succ_le_of_lt hij)
  rw [consecutive_gap] at hm
  omega

@[simp] theorem mem_window {len : ℕ → ℕ} {g i n : ℕ} :
    n ∈ window len g i ↔ start len g i ≤ n ∧ n ≤ finish len g i :=
  Finset.mem_Icc

@[simp] theorem card_window (len : ℕ → ℕ) (g i : ℕ) :
    (window len g i).card = len i := by
  rw [window, Nat.card_Icc]
  have := finish_add_one len g i
  omega

/-- Prefix-sum formula relative to any incoming edge. -/
theorem start_add (len : ℕ → ℕ) (g i m : ℕ) :
    start len g (i + m) = start len g i +
      ∑ k ∈ Finset.range m, (len (i + k) + g) := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Nat.add_succ, start_succ, ih, Finset.sum_range_succ]
      omega

/-- A consecutive child block's endpoint is exactly its total window and gap budget. -/
theorem block_endpoint (len : ℕ → ℕ) (g i m : ℕ) :
    finish len g (i + m) + g + 1 = start len g i +
      ∑ k ∈ Finset.range (m + 1), (len (i + k) + g) := by
  rw [← consecutive_gap]
  simpa only [Nat.add_assoc] using start_add len g i (m + 1)

theorem block_endpoint_le {len : ℕ → ℕ} {g i m r : ℕ}
    (hbudget : (∑ k ∈ Finset.range (m + 1), (len (i + k) + g)) ≤ 2 * r + g) :
    finish len g (i + m) + 1 ≤ start len g i + 2 * r := by
  have := block_endpoint len g i m
  omega

end Problem310.WindowPlacement

end OAI


