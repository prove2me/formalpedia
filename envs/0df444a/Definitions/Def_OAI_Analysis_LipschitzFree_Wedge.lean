-- Prove2me | Definitions.Def_OAI_Analysis_LipschitzFree_Wedge
-- name    : OAI_Analysis_LipschitzFree_Wedge
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T09:40:32.142215+00:00
-- url     : https://prove2.me/theorems/0a638bbf-55b1-4e6f-958f-4686422a05ec
-- title:
--   The metric wedge of a sequence of pointed metric spaces, with component inclusions and retractions
-- statement:
--   Let $(M_n,o_n)_{n\in\mathbb{N}}$ be a sequence of pointed metric spaces with metrics $d_n$. Their wedge $W=\bigvee_{n}(M_n,o_n)$ glues all base points into one point $*$: its points are $*$ together with the points of $M_n\setminus\{o_n\}$ for every $n$, and two points of the same component keep their distance while points of different components are joined through $*$.
--
--   1. **Points.** $W=\{*\}\sqcup\bigsqcup_{n\in\mathbb{N}}\bigl(M_n\setminus\{o_n\}\bigr)$ with base point $*$; $W$ is countable when every $M_n$ is.
--   2. **Metric.** For $x\in M_n\setminus\{o_n\}$ and $y\in M_m\setminus\{o_m\}$,
--   $$
--   d(*,*)=0,\qquad d(x,*)=d(*,x)=d_n(x,o_n),\qquad d(x,y)=\begin{cases} d_n(x,y) & \text{if } n=m,\\ d_n(x,o_n)+d_m(y,o_m) & \text{if } n\neq m.\end{cases}
--   $$
--   This $d$ is a metric on $W$: it vanishes exactly on the diagonal, is symmetric and satisfies the triangle inequality.
--   3. **Inclusions.** $\iota_n\colon M_n\to W$ with $\iota_n(o_n)=*$ and $\iota_n(x)=x$ for $x\neq o_n$. Each $\iota_n$ is an isometric embedding.
--   4. **Retractions.** $r_n\colon W\to M_n$ with $r_n(*)=o_n$, $r_n(x)=x$ for $x\in M_n\setminus\{o_n\}$, and $r_n(y)=o_n$ for points $y$ of other components. Each $r_n$ is $1$-Lipschitz, $r_n\circ\iota_n=\mathrm{id}_{M_n}$, and $r_n\circ\iota_m$ is constant equal to $o_n$ when $m\neq n$.
--   5. **Finite retentions.** For a finite set $F\subseteq\mathbb{N}$, $\rho_F\colon W\to W$ fixes $*$ and the points of the components $M_n$ with $n\in F$ and sends the points of all other components to $*$. It is $1$-Lipschitz, $\rho_F(*)=*$, and $\rho_F(\iota_n(x))$ equals $\iota_n(x)$ if $n\in F$ and $*$ otherwise.
--
--   The wedge combines a sequence of spaces into one space in which each component sits isometrically and is the image of a $1$-Lipschitz retraction. After linearization, each Lipschitz-free space $\mathcal{F}(M_n,o_n)$ becomes a norm-one complemented subspace of the free space of the wedge, and the maps $\rho_F$ cut the wedge down to finitely many components; both facts are used to build a free space with the approximation property but without the bounded approximation property.
--
--   **Formalization Note** The point type is `Point M o := Option (Σ n, {x : M n // x ≠ o n})` with `none` as the base point `base M o`; the metric is `distance M o`, with `distance_self`, `distance_comm`, `distance_triangle`, `eq_of_distance_zero` giving the metric space instance. The maps are `inclusion`, `retraction` and `retain`, with the lemmas `inclusion_isometry`, `retraction_lipschitz`, `retain_lipschitz` and the simp lemmas of items 3 to 5; `dite_eq_right` is a private backport.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/LipschitzFree/Wedge.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/LipschitzFree/Wedge.lean by skeleton subtraction
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
import Definitions.Def_OAI_Analysis_LipschitzFree_MetricBlock
import Definitions.Def_OAI_Analysis_LipschitzFree_Attachment
import Definitions.Def_OAI_Analysis_LipschitzFree_Words
import Definitions.Def_OAI_Analysis_LipschitzFree_StatePaths
import Definitions.Def_OAI_Analysis_LipschitzFree_SignedTests
import Definitions.Def_OAI_Analysis_LipschitzFree_GraphWalks
import Definitions.Def_OAI_Analysis_LipschitzFree_Evaluation
import Definitions.Def_OAI_Analysis_LipschitzFree_Coordinates
import Definitions.Def_OAI_Analysis_LipschitzFree_AffineWeights
import Definitions.Def_OAI_Analysis_LipschitzFree_LabelBumps
import Definitions.Def_OAI_Analysis_LipschitzFree_ScalarTests
import Definitions.Def_OAI_Analysis_LipschitzFree_FiniteQuotients
import Definitions.Def_OAI_Analysis_LipschitzFree_GraphGirth
import Definitions.Def_OAI_Analysis_LipschitzFree_ColorCounting
import Definitions.Def_OAI_Analysis_LipschitzFree_GraphColoring
import Definitions.Def_OAI_Analysis_LipschitzFree_BlockObstruction
import Definitions.Def_OAI_Analysis_LipschitzFree_Functor

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem dite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t : c → α} {e : ¬c → α} : (dite c t e) = e hc := @dif_neg c h hc α t e

namespace OAI

/-!
# Metric wedges and their contractive component retractions
-/

noncomputable section
open scoped BigOperators ENNReal

noncomputable section
namespace DiscreteFree.MetricWedge
open scoped Classical
universe u
variable (M : ℕ → Type u) [∀ n, MetricSpace (M n)] (o : ∀ n, M n)

def Point := Option (Σ n, {x : M n // x ≠ o n})

instance [∀ n, Countable (M n)] : Countable (Point M o) :=
  inferInstanceAs (Countable (Option (Σ n, {x : M n // x ≠ o n})))

def base : Point M o := none

def distance : Point M o → Point M o → ℝ
  | none, none => 0
  | none, some ⟨n,x⟩ => dist x.val (o n)
  | some ⟨n,x⟩, none => dist x.val (o n)
  | some ⟨n,x⟩, some ⟨m,y⟩ =>
      if h : n = m then dist (h ▸ x.val) y.val else dist x.val (o n) + dist y.val (o m)

theorem distance_self (x : Point M o) : distance M o x x = 0 := by
  rcases x with _ | ⟨n,x⟩ <;> simp [distance]

theorem distance_comm (x y : Point M o) : distance M o x y = distance M o y x := by
  rcases x with _ | ⟨n,x⟩ <;> rcases y with _ | ⟨m,y⟩ <;> try rfl
  by_cases h : n = m
  · subst m; simp [distance,dist_comm]
  · simp [distance,h,Ne.symm h,add_comm]

theorem distance_triangle (x y z : Point M o) : distance M o x z ≤ distance M o x y + distance M o y z := by
  rcases x with _ | ⟨i,x⟩ <;> rcases y with _ | ⟨j,y⟩ <;> rcases z with _ | ⟨k,z⟩
  · simp [distance]
  · simp [distance]
  · simp only [distance]
    positivity
  · by_cases h : j = k
    · subst k
      simpa [distance,dist_comm,add_comm] using dist_triangle z.val y.val (o j)
    · simp only [distance,dite_eq_right h]
      have := dist_nonneg (x := y.val) (y := o j)
      linarith
  · simp [distance]
  · by_cases h : i = k
    · subst k
      simpa [distance,dist_comm] using dist_triangle x.val (o i) z.val
    · simp [distance,h]
  · by_cases h : i = j
    · subst j
      simpa [distance] using dist_triangle x.val y.val (o i)
    · simp only [distance,dite_eq_right h]
      have := dist_nonneg (x := y.val) (y := o j)
      linarith
  · by_cases hij : i = j
    · subst j
      by_cases hik : i = k
      · subst k
        simpa [distance] using dist_triangle x.val y.val z.val
      · simp only [distance,dite_true,dite_eq_right hik]
        have := dist_triangle x.val y.val (o i)
        linarith
    · by_cases hik : i = k
      · subst k
        simp only [distance,dite_true,dite_eq_right hij,dite_eq_right (Ne.symm hij)]
        have := dist_triangle x.val (o i) z.val
        have := dist_nonneg (x := y.val) (y := o j)
        rw [dist_comm (o i) z.val] at *
        linarith
      · by_cases hjk : j = k
        · subst k
          simp only [distance,dite_eq_right hij,dite_true]
          have := dist_triangle z.val y.val (o j)
          rw [dist_comm z.val y.val] at *
          linarith
        · simp only [distance,dite_eq_right hij,dite_eq_right hik,dite_eq_right hjk]
          have := dist_nonneg (x := y.val) (y := o j)
          linarith

theorem eq_of_distance_zero (x y : Point M o) (h : distance M o x y = 0) : x = y := by
  rcases x with _ | ⟨n,x⟩ <;> rcases y with _ | ⟨m,y⟩
  · rfl
  · exact False.elim (y.property (dist_eq_zero.mp h))
  · exact False.elim (x.property (dist_eq_zero.mp h))
  · by_cases hnm : n = m
    · subst m
      simp only [distance,dite_true] at h
      have he : x = y := Subtype.ext (dist_eq_zero.mp h)
      subst y
      rfl
    · simp only [distance,dite_eq_right hnm] at h
      have hx : 0 < dist x.val (o n) := dist_pos.mpr x.property
      have hy : 0 ≤ dist y.val (o m) := dist_nonneg
      linarith

instance : MetricSpace (Point M o) where
  dist := distance M o
  dist_self := distance_self M o
  dist_comm := distance_comm M o
  dist_triangle := distance_triangle M o
  eq_of_dist_eq_zero := eq_of_distance_zero M o _ _

def inclusion (n : ℕ) (x : M n) : Point M o :=
  if h : x = o n then none else some ⟨n,⟨x,h⟩⟩

def retraction (n : ℕ) : Point M o → M n
  | none => o n
  | some ⟨m,y⟩ => if h : m = n then h ▸ y.val else o n

omit [∀ n, MetricSpace (M n)] in
@[simp] theorem inclusion_base (n : ℕ) : inclusion M o n (o n) = base M o := by
  simp [inclusion,base]
  rfl

omit [∀ n, MetricSpace (M n)] in
@[simp] theorem retraction_base (n : ℕ) : retraction M o n (base M o) = o n := rfl

omit [∀ n, MetricSpace (M n)] in
@[simp] theorem retraction_inclusion (n : ℕ) (x : M n) :
    retraction M o n (inclusion M o n x) = x := by
  by_cases h : x = o n
  · simp [inclusion,h,retraction]
  · simp [inclusion,h,retraction]

omit [∀ n, MetricSpace (M n)] in
@[simp] theorem retraction_other {n m : ℕ} (h : n ≠ m) (x : M m) :
    retraction M o n (inclusion M o m x) = o n := by
  by_cases hx : x = o m <;> simp [inclusion,hx,retraction,Ne.symm h]

theorem inclusion_isometry (n : ℕ) : Isometry (inclusion M o n) := by
  apply isometry_iff_dist_eq.mpr
  intro x y
  change distance M o _ _ = dist x y
  by_cases hx : x = o n <;> by_cases hy : y = o n <;> simp [inclusion,hx,hy,distance,dist_comm]

theorem retraction_lipschitz (n : ℕ) : LipschitzWith 1 (retraction M o n) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [NNReal.coe_one,one_mul]
  change dist _ _ ≤ distance M o x y
  rcases x with _ | ⟨i,x⟩ <;> rcases y with _ | ⟨j,y⟩
  · simp [distance,retraction]
  · by_cases h : j = n
    · subst j; simp [distance,retraction,dist_comm]
    · simp [distance,retraction,h]
  · by_cases h : i = n
    · subst i; simp [distance,retraction]
    · simp [distance,retraction,h]
  · by_cases hi : i = n
    · subst i
      by_cases hj : j = n
      · subst j; simp [distance,retraction]
      · simp [distance,retraction,hj,Ne.symm hj,dist_nonneg]
    · by_cases hj : j = n
      · subst j
        simp [distance,retraction,hi,dist_comm,dist_nonneg]
      · simp only [retraction,dite_eq_right hi,dite_eq_right hj,dist_self]
        exact @dist_nonneg (Point M o) _ (some ⟨i,x⟩) (some ⟨j,y⟩)

def retain (F : Finset ℕ) : Point M o → Point M o
  | none => none
  | some ⟨n,x⟩ => if n ∈ F then some ⟨n,x⟩ else none

omit [∀ n, MetricSpace (M n)] in
@[simp] theorem retain_base (F : Finset ℕ) : retain M o F (base M o) = base M o := rfl

omit [∀ n, MetricSpace (M n)] in
@[simp] theorem retain_inclusion (F : Finset ℕ) (n : ℕ) (x : M n) :
    retain M o F (inclusion M o n x) = if n ∈ F then inclusion M o n x else base M o := by
  by_cases hx : x = o n <;> by_cases hn : n ∈ F <;> simp [inclusion,hx,retain,hn,base] <;> rfl

theorem retain_lipschitz (F : Finset ℕ) : LipschitzWith 1 (retain M o F) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [NNReal.coe_one,one_mul]
  change distance M o _ _ ≤ distance M o x y
  rcases x with _ | ⟨i,x⟩ <;> rcases y with _ | ⟨j,y⟩
  · simp [retain,distance]
  · by_cases h : j ∈ F <;> simp [retain,h,distance,dist_nonneg]
  · by_cases h : i ∈ F <;> simp [retain,h,distance,dist_nonneg]
  · by_cases hi : i ∈ F <;> by_cases hj : j ∈ F
    · simp [retain,hi,hj]
    · have hn : i ≠ j := by rintro rfl; exact hj hi
      simp [retain,hi,hj,distance,hn,dist_nonneg]
    · have hn : i ≠ j := by rintro rfl; exact hi hj
      simp [retain,hi,hj,distance,hn,dist_nonneg]
    · have hh : 0 ≤ distance M o (some ⟨i,x⟩) (some ⟨j,y⟩) :=
        @dist_nonneg (Point M o) _ (some ⟨i,x⟩) (some ⟨j,y⟩)
      simpa [retain,hi,hj,distance] using hh

end DiscreteFree.MetricWedge
end

end

end OAI


