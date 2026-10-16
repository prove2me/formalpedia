-- Prove2me | Definitions.Def_OAI_Analysis_LipschitzFree_Model__RealL1Renorming
-- name    : OAI_Analysis_LipschitzFree_Model__RealL1Renorming
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T11:50:16.596301+00:00
-- url     : https://prove2.me/theorems/7770f7b4-b6f7-4f31-b2db-8c6624c6e37e
-- title:
--   The pointed Lipschitz space $\mathrm{Lip}_0(M)$, point evaluations and the Lipschitz-free space $\mathcal{F}(M)$
-- statement:
--   This file constructs, for a metric space $(M,d)$ with a distinguished base point $o\in M$, the normed space of pointed Lipschitz functions on $M$ and the Lipschitz-free space of $M$ as a closed subspace of its dual.
--
--   1. **Pointed Lipschitz functions.** $\mathrm{Lip}_0(M)$ is the set of functions $f:M\to\mathbb{R}$ with $f(o)=0$ for which some constant $C\ge 0$ satisfies $|f(x)-f(y)|\le C\,d(x,y)$ for all $x,y\in M$. It is a linear subspace of the space of all real functions on $M$, with pointwise operations.
--
--   2. **Slope map and Lipschitz norm.** The slope map sends $f\in\mathrm{Lip}_0(M)$ to the bounded function of two variables
--   $$(x,y)\longmapsto\frac{f(x)-f(y)}{d(x,y)},\qquad (x,y)\in M\times M,$$
--   regarded as an element of $\ell^\infty(M\times M)$. It is linear and injective, and $\mathrm{Lip}_0(M)$ is normed by pulling back the sup norm along it, so that
--   $$\|f\|=\sup_{x\neq y}\frac{|f(x)-f(y)|}{d(x,y)}$$
--   is the best Lipschitz constant of $f$. The file records that every $f$ vanishes at $o$; that for every $C\ge 0$ one has $\|f\|\le C$ if and only if $|f(x)-f(y)|\le C\,d(x,y)$ for all $x,y\in M$; and hence $|f(x)-f(y)|\le\|f\|\,d(x,y)$. It also provides a constructor that turns any $f:M\to\mathbb{R}$ with $f(o)=0$ and an explicit Lipschitz bound $C\ge0$ into an element of $\mathrm{Lip}_0(M)$.
--
--   3. **Point evaluations.** For $x\in M$ the evaluation functional $e_x:\mathrm{Lip}_0(M)\to\mathbb{R}$, $e_x(f)=f(x)$, is a bounded linear functional with $\|e_x\|\le d(x,o)$, and $e_o=0$.
--
--   4. **Lipschitz-free space.** $\mathcal{F}(M)$ is the norm closure of the linear span of $\{e_x : x\in M\}$ inside the dual space $\mathrm{Lip}_0(M)^{*}$ of bounded linear functionals on $\mathrm{Lip}_0(M)$, equipped with the operator norm. For $x\in M$, $\delta_x\in\mathcal{F}(M)$ denotes $e_x$ regarded as an element of this subspace.
--
--   These are the basic objects of the construction: a renorming of a sequence space is obtained by identifying it with a Lipschitz-free space $\mathcal{F}(M)$ over a suitable discrete metric space $M$, and explicit functions in $\mathrm{Lip}_0(M)$ serve as test functionals for elements of $\mathcal{F}(M)$.
--
--   **Formalization Note** `lipSubmodule o` is the subspace of item 1 and `Lip0 o` its carrier type. Its norm is induced from the linear map `Lip0.slope o` into `lp (fun _ : M × M => ℝ) ∞`; on the diagonal the difference quotient is $0/0=0$ by Lean's division convention, so the norm is the supremum over pairs $x\neq y$ (and equals $0$ when $M$ consists of the base point only). `Lip0.ofBound` is the constructor, `Lip0.norm_le_iff` and `Lip0.sub_le` are the norm characterisations, `evaluation o x` is $e_x$, `freeSubmodule o` is the closed span, `FreeSpace o` its carrier type and `delta o x` is $\delta_x$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/LipschitzFree/Model.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/LipschitzFree/Model.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the RealL1Renorming mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_RealL1Renorming

namespace OAI

/-!
# Real Lipschitz-free spaces and compact-uniform approximation properties
-/

noncomputable section
open scoped BigOperators ENNReal

namespace DiscreteFree

variable {M : Type*} [MetricSpace M]

def lipSubmodule (o : M) : Submodule ℝ (M → ℝ) where
  carrier := {f | f o = 0 ∧ ∃ C : ℝ, 0 ≤ C ∧
    ∀ x y, |f x - f y| ≤ C * dist x y}
  zero_mem' := by
    refine ⟨rfl, 0, le_rfl, ?_⟩
    intro x y
    simp
  add_mem' := by
    rintro f g ⟨hfo, C, hC, hf⟩ ⟨hgo, D, hD, hg⟩
    refine ⟨by simpa using congrArg₂ (· + ·) hfo hgo,
      C + D, add_nonneg hC hD, ?_⟩
    intro x y
    change |f x + g x - (f y + g y)| ≤ (C + D) * dist x y
    calc
      _ = |(f x - f y) + (g x - g y)| := by ring_nf
      _ ≤ |f x - f y| + |g x - g y| := abs_add_le _ _
      _ ≤ C * dist x y + D * dist x y := add_le_add (hf x y) (hg x y)
      _ = _ := by ring
  smul_mem' := by
    rintro c f ⟨hfo, C, hC, hf⟩
    refine ⟨by simp [hfo], |c| * C, mul_nonneg (abs_nonneg c) hC, ?_⟩
    intro x y
    change |c * f x - c * f y| ≤ (|c| * C) * dist x y
    calc
      _ = |c| * |f x - f y| := by rw [← mul_sub, abs_mul]
      _ ≤ |c| * (C * dist x y) := mul_le_mul_of_nonneg_left (hf x y) (abs_nonneg c)
      _ = _ := by ring

def Lip0 (o : M) := ↥(lipSubmodule o)

namespace Lip0

variable {o : M}

instance : AddCommGroup (Lip0 o) := inferInstanceAs (AddCommGroup ↥(lipSubmodule o))
instance : Module ℝ (Lip0 o) := inferInstanceAs (Module ℝ ↥(lipSubmodule o))

instance : CoeFun (Lip0 o) (fun _ => M → ℝ) := ⟨fun f => f.val⟩

@[simp] theorem at_base (f : Lip0 o) : f o = 0 := f.property.1

def slope (o : M) : Lip0 o →ₗ[ℝ] lp (fun _ : M × M => ℝ) ∞ where
  toFun f := ⟨fun z : M × M => (f z.1 - f z.2) / dist z.1 z.2, by
    obtain ⟨C, hC, hf⟩ := f.property.2
    apply memℓp_infty
    refine ⟨C, ?_⟩
    rintro r ⟨⟨x, y⟩, rfl⟩
    change ‖(f x - f y) / dist x y‖ ≤ C
    rw [Real.norm_eq_abs, abs_div, abs_of_nonneg dist_nonneg]
    by_cases hxy : x = y
    · simp [hxy, hC]
    · exact (div_le_iff₀ (dist_pos.mpr hxy)).2 (hf x y)⟩
  map_add' f g := by
    apply lp.ext
    funext z
    change ((f z.1 + g z.1) - (f z.2 + g z.2)) / dist z.1 z.2 =
      (f z.1 - f z.2) / dist z.1 z.2 + (g z.1 - g z.2) / dist z.1 z.2
    ring
  map_smul' c f := by
    apply lp.ext
    funext z
    change (c * f z.1 - c * f z.2) / dist z.1 z.2 =
      c * ((f z.1 - f z.2) / dist z.1 z.2)
    ring

instance (o : M) : NormedAddCommGroup (Lip0 o) :=
  NormedAddCommGroup.induced _ _ (slope o).toAddMonoidHom (by
    intro f g h
    apply Subtype.ext
    funext x
    have hx := congrArg (fun q : lp (fun _ : M × M => ℝ) ∞ => q (x, o)) h
    change (f x - f o) / dist x o = (g x - g o) / dist x o at hx
    rw [f.property.1, g.property.1, sub_zero, sub_zero] at hx
    by_cases hxo : x = o
    · rw [hxo, f.property.1, g.property.1]
    · exact (div_left_inj' (ne_of_gt (dist_pos.mpr hxo))).mp hx)

instance (o : M) : NormedSpace ℝ (Lip0 o) :=
  NormedSpace.induced ℝ _ _ (slope o)

@[simp] theorem norm_slope (f : Lip0 o) : ‖slope o f‖ = ‖f‖ := rfl

theorem norm_le_iff (f : Lip0 o) {C : ℝ} (hC : 0 ≤ C) :
    ‖f‖ ≤ C ↔ ∀ x y, |f x - f y| ≤ C * dist x y := by
  constructor
  · intro h x y
    by_cases hxy : x = y
    · simp [hxy]
    · have hx := (lp.norm_apply_le_norm (by simp : (∞ : ℝ≥0∞) ≠ 0) (slope o f) (x, y)).trans h
      change ‖(f x - f y) / dist x y‖ ≤ C at hx
      rw [Real.norm_eq_abs, abs_div, abs_of_nonneg dist_nonneg] at hx
      exact (div_le_iff₀ (dist_pos.mpr hxy)).mp hx
  · intro h
    apply lp.norm_le_of_forall_le hC
    rintro ⟨x, y⟩
    change ‖(f x - f y) / dist x y‖ ≤ C
    rw [Real.norm_eq_abs, abs_div, abs_of_nonneg dist_nonneg]
    by_cases hxy : x = y
    · simp [hxy, hC]
    · exact (div_le_iff₀ (dist_pos.mpr hxy)).mpr (h x y)

theorem sub_le (f : Lip0 o) (x y : M) :
    |f x - f y| ≤ ‖f‖ * dist x y :=
  (norm_le_iff f (norm_nonneg f)).mp le_rfl x y

def ofBound (o : M) (f : M → ℝ) (hfo : f o = 0) (C : ℝ) (hC : 0 ≤ C)
    (hf : ∀ x y, |f x - f y| ≤ C * dist x y) : Lip0 o :=
  ⟨f, hfo, C, hC, hf⟩

end Lip0

def evaluation (o x : M) : (Lip0 o →L[ℝ] ℝ) :=
  LinearMap.mkContinuous
    ({ toFun := fun f : Lip0 o => f x
       map_add' := fun _ _ => rfl
       map_smul' := fun _ _ => rfl } : Lip0 o →ₗ[ℝ] ℝ)
    (dist x o) (fun f => by
      change ‖f x‖ ≤ dist x o * ‖f‖
      rw [mul_comm]
      have hx := lp.norm_apply_le_norm (by simp : (∞ : ℝ≥0∞) ≠ 0)
        (Lip0.slope o f) (x, o)
      change ‖(f x - f o) / dist x o‖ ≤ ‖f‖ at hx
      rw [f.property.1, sub_zero, norm_div, Real.norm_of_nonneg dist_nonneg] at hx
      by_cases hxo : x = o
      · rw [hxo, f.property.1, norm_zero, dist_self, mul_zero]
      · exact (div_le_iff₀ (dist_pos.mpr hxo)).mp hx)

@[simp] theorem evaluation_apply (o x : M) (f : Lip0 o) : evaluation o x f = f x := rfl

@[simp] theorem evaluation_base (o : M) : evaluation o o = 0 := by
  ext f
  exact Lip0.at_base f

def freeSubmodule (o : M) : Submodule ℝ ((Lip0 o →L[ℝ] ℝ)) :=
  (Submodule.span ℝ (Set.range (evaluation o))).topologicalClosure

def FreeSpace (o : M) := ↥(freeSubmodule o)

instance (o : M) : NormedAddCommGroup (FreeSpace o) :=
  inferInstanceAs (NormedAddCommGroup ↥(freeSubmodule o))

instance (o : M) : NormedSpace ℝ (FreeSpace o) :=
  inferInstanceAs (NormedSpace ℝ ↥(freeSubmodule o))

def delta (o x : M) : FreeSpace o :=
  ⟨evaluation o x, Submodule.le_topologicalClosure _
    (Submodule.subset_span ⟨x, rfl⟩)⟩

end DiscreteFree

end

end OAI


