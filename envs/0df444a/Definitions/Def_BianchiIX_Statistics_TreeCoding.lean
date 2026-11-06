-- Prove2me | Definitions.Def_BianchiIX_Statistics_TreeCoding
-- name    : BianchiIX_Statistics_TreeCoding
-- status  : Definition
-- author  : @trppppp
-- created : 2026-11-04T17:34:56.947684+00:00
-- url     : https://prove2.me/theorems/3972b782-656b-4492-87e5-37a6a7bcdebe
-- title:
--   Digit coding of surviving branch-tree points
-- statement:
--   Let $T$ be an inverse-branch tree with open root
--   $R\subset\mathbb R$. For every finite positive-digit word $v$ and digit $a$,
--   let $U_{v,a}\subset\mathbb R$ be open and let $h_{v,a}:\mathbb R\to\mathbb R$
--   be continuous and injective on $U_{v,a}$. For fixed $v$, assume the images
--   $h_{v,a}(U_{v,a})$ are pairwise disjoint. Define
--   $$K_\varnothing=R,\qquad K_{va}=U_{v,a}\cap h_{v,a}^{-1}(K_v),$$
--   $$H_\varnothing=\mathrm{id},\qquad H_{va}=H_v\circ h_{v,a},\qquad C_v=H_v(K_v),$$
--   $$D_v=K_v\setminus\bigcup_a h_{v,a}(U_{v,a}),\qquad S_n=\bigcup_{|v|=n}C_v.$$
--   Here $va$ denotes appending the digit $a$ to $v$.
--
--   Let $S=\bigcap_nS_n$ be the surviving set. For $x\in S$, denote its unique
--   length-$n$ cell word by $v_n(x)$ and define $a_n(x)$ by
--   $v_{n+1}(x)=v_n(x)a_n(x)$. Let $g_b(t)=1/(b+t)$ and
--   $G_v=g_{v_0}\circ\cdots\circ g_{v_{|v|-1}}$, with the empty composition the
--   identity. The code is
--   $$\kappa(x)=\lim_{n\to\infty}G_{v_n(x)}(0).$$
--   For a Borel measure $\mu$ on $\mathbb R$, write $\mu_S$ for its pullback
--   to the measurable subtype $S$ by the inclusion into $\mathbb R$.
--
--   The finite words and their next digits are defined by choice from the
--   corresponding existence proofs. The existence proofs and the word length
--   and cell membership properties needed by the digit definition are included.
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Statistics/TreeCoding.lean

import Definitions.Def_BianchiIX_Statistics_GaussCoding
import Definitions.Def_BianchiIX_Statistics_StoppedMass
import Definitions.Def_BianchiIX_Statistics_BranchTree
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.List.Induction
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Data.PNat.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.Data.Rat.Floor
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Order.OrderIsoNat
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Group.MeasurableEquiv
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Function.JacobianOneDim

section
open Set MeasureTheory
open BianchiIX
open BianchiIX.InverseBranchTree
variable (T : InverseBranchTree)

@[simp] private theorem BianchiIX.InverseBranchTree.terminal_nil : T.terminal [] = T.root := by
  simp [terminal, List.reverseRecOn]

end

section
open Set MeasureTheory
open BianchiIX
open BianchiIX.InverseBranchTree
variable (T : InverseBranchTree)

@[simp] private theorem BianchiIX.InverseBranchTree.terminal_append (w : List ℕ+) (a : ℕ+) :
    T.terminal (w ++ [a]) = T.domain w a ∩ T.branch w a ⁻¹' T.terminal w := by
  simp [terminal, List.reverseRecOn]

end

section
open Set MeasureTheory
open BianchiIX
open BianchiIX.InverseBranchTree
variable (T : InverseBranchTree)

@[simp] private theorem BianchiIX.InverseBranchTree.toRoot_nil : T.toRoot [] = id := by
  simp [toRoot, List.reverseRecOn]

end

section
open Set MeasureTheory
open BianchiIX
open BianchiIX.InverseBranchTree
variable (T : InverseBranchTree)

@[simp] private theorem BianchiIX.InverseBranchTree.toRoot_append (w : List ℕ+) (a : ℕ+) :
    T.toRoot (w ++ [a]) = T.toRoot w ∘ T.branch w a := by
  simp [toRoot, List.reverseRecOn]

end

section
open Set MeasureTheory
open BianchiIX
open BianchiIX.InverseBranchTree
variable (T : InverseBranchTree)

private theorem BianchiIX.InverseBranchTree.toRoot_injective (w : List ℕ+) : InjOn (T.toRoot w) (T.terminal w) := by
  induction w using List.reverseRecOn with
  | nil => simp
  | append_singleton w a ih =>
    rw [toRoot_append, terminal_append]
    intro x hx y hy hxy
    exact T.branch_injective w a hx.1 hy.1 (ih hx.2 hy.2 hxy)

end

section
open Set MeasureTheory
open BianchiIX
open BianchiIX.InverseBranchTree
variable (T : InverseBranchTree)

private theorem BianchiIX.InverseBranchTree.cell_append (w : List ℕ+) (a : ℕ+) :
    T.cell (w ++ [a]) = T.toRoot w ''
      (T.terminal w ∩ T.branch w a '' T.domain w a) := by
  ext x
  simp only [cell, toRoot_append, terminal_append, mem_image, mem_inter_iff,
    mem_preimage, Function.comp_apply]
  constructor
  · rintro ⟨y, ⟨hy, hK⟩, rfl⟩
    exact ⟨T.branch w a y, ⟨hK, y, hy, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨hK, y, hy, rfl⟩, rfl⟩
    exact ⟨y, ⟨hy, hK⟩, rfl⟩

end

section
open Set MeasureTheory
open BianchiIX
open BianchiIX.InverseBranchTree
variable (T : InverseBranchTree)

private theorem BianchiIX.InverseBranchTree.cell_child_subset (w : List ℕ+) (a : ℕ+) : T.cell (w ++ [a]) ⊆ T.cell w := by
  rw [cell_append]
  exact image_mono inter_subset_left

end

section
open Set MeasureTheory
open BianchiIX
open BianchiIX.InverseBranchTree
variable (T : InverseBranchTree)

private theorem BianchiIX.InverseBranchTree.cell_siblings_disjoint (w : List ℕ+) :
    Pairwise (fun a b => Disjoint (T.cell (w ++ [a])) (T.cell (w ++ [b]))) := by
  intro a b hab
  rw [T.cell_append, T.cell_append, Set.disjoint_left]
  rintro x ⟨u, ⟨hu, ha⟩, hux⟩ ⟨v, ⟨hv, hb⟩, hvx⟩
  have huv := T.toRoot_injective w hu hv (hux.trans hvx.symm)
  exact Set.disjoint_left.mp (T.branch_disjoint w hab) ha (huv ▸ hb)

end

section
open Set MeasureTheory
open BianchiIX
open BianchiIX.InverseBranchTree
variable (T : InverseBranchTree)

private theorem BianchiIX.InverseBranchTree.cell_unique {v w : List ℕ+} (hlen : v.length = w.length)
    {x : ℝ} (hv : x ∈ T.cell v) (hw : x ∈ T.cell w) : v = w := by
  induction v using List.reverseRecOn generalizing w with
  | nil =>
    have : w = [] := List.length_eq_zero_iff.mp hlen.symm
    exact this.symm
  | append_singleton v a ih =>
    induction w using List.reverseRecOn with
    | nil => simp at hlen
    | append_singleton w b _ =>
      have hvw : v = w := ih (by simpa using hlen)
        (T.cell_child_subset v a hv) (T.cell_child_subset w b hw)
      subst w
      have hab : a = b := by
        by_contra h
        exact Set.disjoint_left.mp (T.cell_siblings_disjoint v h) hv hw
      exact congrArg (fun c => v ++ [c]) hab

end

section
open Set MeasureTheory
open BianchiIX
open BianchiIX.InverseBranchTree
variable (T : InverseBranchTree)

private theorem BianchiIX.InverseBranchTree.mem_level {n : ℕ} {x : ℝ} :
    x ∈ T.level n ↔ ∃ w : List ℕ+, w.length = n ∧ x ∈ T.cell w := by
  simp [level]

end


/-! Measurable symbolic coding of the surviving points of an actual inverse-branch tree. -/

open Set MeasureTheory
open scoped NNReal ENNReal

namespace BianchiIX
namespace InverseBranchTree

variable (T : InverseBranchTree)

def survivors : Set ℝ := survivingSet T.level



private theorem exists_word (x : T.survivors) (n : ℕ) :
    ∃ w : List ℕ+, w.length = n ∧ x.val ∈ T.cell w :=
  T.mem_level.mp (mem_iInter.mp x.property n)

noncomputable def word (x : T.survivors) (n : ℕ) : List ℕ+ :=
  (T.exists_word x n).choose

theorem word_length (x : T.survivors) (n : ℕ) : (T.word x n).length = n :=
  (T.exists_word x n).choose_spec.1

theorem mem_word_cell (x : T.survivors) (n : ℕ) : x.val ∈ T.cell (T.word x n) :=
  (T.exists_word x n).choose_spec.2



private theorem exists_next_digit (x : T.survivors) (n : ℕ) :
    ∃ a : ℕ+, T.word x (n + 1) = T.word x n ++ [a] := by
  have hl := T.word_length x (n + 1)
  have hx := T.mem_word_cell x (n + 1)
  generalize T.word x (n + 1) = w at hl hx ⊢
  induction w using List.reverseRecOn with
  | nil => simp at hl
  | append_singleton w a _ =>
    have hw : w = T.word x n := T.cell_unique (by simpa [T.word_length] using hl)
      (T.cell_child_subset w a hx) (T.mem_word_cell x n)
    exact ⟨a, congrArg (fun v => v ++ [a]) hw⟩

noncomputable def digits (x : T.survivors) (n : ℕ) : ℕ+ :=
  (T.exists_next_digit x n).choose











noncomputable def code (x : T.survivors) : ℝ := gaussCode (T.digits x)











end InverseBranchTree
end BianchiIX


