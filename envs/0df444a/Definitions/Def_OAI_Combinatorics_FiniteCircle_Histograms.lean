-- Prove2me | Definitions.Def_OAI_Combinatorics_FiniteCircle_Histograms
-- name    : OAI_Combinatorics_FiniteCircle_Histograms
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T13:18:00.63507+00:00
-- url     : https://prove2.me/theorems/6b14e2f7-1374-4a63-9e13-0ffbdb66076e
-- title:
--   Label histograms of lists, their $\ell^1$ distance, and weighted histogram coordinates
-- statement:
--   Let $\lambda:X\to Y$ be a labelling and $x=(x_1,\dots,x_n)$ a finite list of elements of $X$.
--
--   1. **Histogram.** The histogram of $x$ under $\lambda$ counts how often each label occurs,
--   $$
--   h_\lambda(x)(y)=\#\{k\le n:\ \lambda(x_k)=y\}=\sum_{k=1}^{n}[\lambda(x_k)=y]\in\mathbb{R},\qquad y\in Y .
--   $$
--   The module records that the histogram of the empty list is $0$; that histograms are additive under concatenation, $h_\lambda(xx')=h_\lambda(x)+h_\lambda(x')$, in particular when one element is prepended; that they are nonnegative; that the total mass is $\sum_{y\in Y}h_\lambda(x)(y)=n$ when $Y$ is finite; and that $h_\lambda(x)(y)=0$ if no entry of $x$ has label $y$.
--
--   2. **Histogram distance.** For finite $Y$ and two lists $x,x'$,
--   $$
--   d_\lambda(x,x')=\sum_{y\in Y}\bigl|h_\lambda(x)(y)-h_\lambda(x')(y)\bigr| ,
--   $$
--   the $\ell^1$ distance between the two histograms. It vanishes for $x'=x$; it equals $|x|+|x'|$ when no entry of $x$ has the same label as an entry of $x'$; and for one-element lists $d_\lambda([u],[v])$ is $0$ if $\lambda(u)=\lambda(v)$ and $2$ otherwise.
--
--   3. **Weighted histogram coordinates.** Given a finite law $\mu$ on a finite set $\Omega$ (nonnegative weights $\mu(\omega)$ summing to $1$) and a family of labellings $\lambda_\omega:X\to Y$ indexed by $\omega\in\Omega$, a list $x$ is mapped to the vector indexed by $\Omega\times Y$ with entries
--   $$
--   H(x)(\omega,y)=\mu(\omega)\,h_{\lambda_\omega}(x)(y).
--   $$
--
--   Since the weights are nonnegative, the $\ell^1$ distance between $H(x)$ and $H(x')$ is the expected histogram distance $\sum_{\omega}\mu(\omega)\,d_{\lambda_\omega}(x,x')$. Applied to the lists of window words of a word and to random partition labels, this turns probability estimates for individual windows into distance bounds for an embedding of words into $\ell^1$.
--
--   **Formalization Note** `histogram label xs y` is real valued; `histogram_nil`, `histogram_cons`, `histogram_append`, `histogram_nonneg`, `histogram_mass` (which needs `[Fintype Y]`) and `histogram_eq_zero` are the facts of item 1. `histDist` requires `[Fintype Y]`, with lemmas `histDist_self`, `histDist_disjoint` and `histDist_singleton`. `histMap μ label xs` is the function on `Ω × Y` of item 3. The private lemmas `ite_eq_left` and `ite_eq_right` are rewriting aliases for if-then-else expressions.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/FiniteCircle/Histograms.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/FiniteCircle/Histograms.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the FiniteCircle mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_FiniteCircle
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Model
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Edit
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Matching
import Definitions.Def_OAI_Combinatorics_FiniteCircle_TaggedRows
import Definitions.Def_OAI_Combinatorics_FiniteCircle_PhaseCost
import Definitions.Def_OAI_Combinatorics_FiniteCircle_CircleWords
import Definitions.Def_OAI_Combinatorics_FiniteCircle_MaskSeparation
import Definitions.Def_OAI_Combinatorics_FiniteCircle_ExcludedSeparation
import Definitions.Def_OAI_Combinatorics_FiniteCircle_MaskDescent
import Definitions.Def_OAI_Combinatorics_FiniteCircle_ExcludedDescent
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Primes
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Fourier
import Definitions.Def_OAI_Combinatorics_FiniteCircle_DyadicShifts
import Definitions.Def_OAI_Combinatorics_FiniteCircle_MaskBranching
import Definitions.Def_OAI_Combinatorics_FiniteCircle_TreeBranching
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Translations
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Distortion
import Definitions.Def_OAI_Combinatorics_FiniteCircle_BlockMatching
import Definitions.Def_OAI_Combinatorics_FiniteCircle_OffsetRecovery
import Definitions.Def_OAI_Combinatorics_FiniteCircle_RandomCodes
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Codes
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Lower
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Windows
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Partitions

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

namespace FiniteCircle

open scoped BigOperators List
open scoped ComplexConjugate
open RCLike Module
open Classical

noncomputable def histogram {X Y : Type*} (label : X → Y) (xs : List X) (y : Y) : ℝ := by
  classical
  exact (xs.map (fun x => if label x = y then (1 : ℝ) else 0)).sum

@[simp] theorem histogram_nil {X Y : Type*} (label : X → Y) (y : Y) :
    histogram label [] y = 0 := by simp [histogram]

@[simp] theorem histogram_cons {X Y : Type*} [DecidableEq Y] (label : X → Y) (x : X) (xs : List X) (y : Y) :
    histogram label (x :: xs) y = (if label x = y then 1 else 0) + histogram label xs y := by
  classical
  simp [histogram]

@[simp] theorem histogram_append {X Y : Type*} (label : X → Y) (xs ys : List X) (y : Y) :
    histogram label (xs ++ ys) y = histogram label xs y + histogram label ys y := by
  simp [histogram]

theorem histogram_nonneg {X Y : Type*} (label : X → Y) (xs : List X) (y : Y) :
    0 ≤ histogram label xs y := by
  classical
  induction xs with
  | nil => simp
  | cons x xs ih =>
    rw [histogram_cons]
    split <;> linarith

theorem histogram_mass {X Y : Type*} [Fintype Y] (label : X → Y) (xs : List X) :
    ∑ y, histogram label xs y = xs.length := by
  classical
  induction xs with
  | nil => simp
  | cons x xs ih => simp [histogram_cons, Finset.sum_add_distrib, ih, Nat.cast_add, add_comm]

theorem histogram_eq_zero {X Y : Type*} (label : X → Y) (xs : List X) (y : Y)
    (h : ∀ x ∈ xs, label x ≠ y) : histogram label xs y = 0 := by
  classical
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [histogram_cons, ite_eq_right (h x (by simp)), zero_add]
    exact ih (fun z hz => h z (by simp [hz]))

noncomputable def histDist {X Y : Type*} [Fintype Y] (label : X → Y) (xs ys : List X) : ℝ :=
  ∑ y, |histogram label xs y - histogram label ys y|

@[simp] theorem histDist_self {X Y : Type*} [Fintype Y] (label : X → Y) (xs : List X) :
    histDist label xs xs = 0 := by simp [histDist]

theorem histDist_disjoint {X Y : Type*} [Fintype Y] (label : X → Y) (xs ys : List X)
    (h : ∀ x ∈ xs, ∀ y ∈ ys, label x ≠ label y) :
    histDist label xs ys = xs.length + ys.length := by
  classical
  calc
    _ = ∑ y, (histogram label xs y + histogram label ys y) := by
      apply Finset.sum_congr rfl
      intro y _
      by_cases he : ∃ x ∈ xs, label x = y
      · obtain ⟨x, hx, rfl⟩ := he
        rw [histogram_eq_zero label ys _ (fun z hz => Ne.symm (h x hx z hz))]
        simp [abs_of_nonneg (histogram_nonneg label xs (label x))]
      · rw [histogram_eq_zero label xs _ (fun x hx heq => he ⟨x, hx, heq⟩)]
        simp [abs_of_nonneg (histogram_nonneg label ys y)]
    _ = _ := by rw [Finset.sum_add_distrib, histogram_mass, histogram_mass]

@[simp] theorem histDist_singleton {X Y : Type*} [Fintype Y] [DecidableEq Y] (label : X → Y) (x y : X) :
    histDist label [x] [y] = if label x = label y then 0 else 2 := by
  classical
  by_cases h : label x = label y
  · rw [ite_eq_left h]
    unfold histDist
    apply Finset.sum_eq_zero
    intro z _
    by_cases hz : label y = z <;> simp [histogram, h, hz]
  · rw [ite_eq_right h, histDist_disjoint label [x] [y] (by simpa using h)]
    norm_num

noncomputable def histMap {X Ω Y : Type*} [Fintype Ω] (μ : FiniteLaw Ω)
    (label : Ω → X → Y) (xs : List X) (i : Ω × Y) : ℝ :=
  μ.weight i.1 * histogram (label i.1) xs i.2

end FiniteCircle

end OAI


