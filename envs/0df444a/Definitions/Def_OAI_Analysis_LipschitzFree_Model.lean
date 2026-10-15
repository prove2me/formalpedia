-- Prove2me | Definitions.Def_OAI_Analysis_LipschitzFree_Model
-- name    : OAI_Analysis_LipschitzFree_Model
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T08:56:50.276508+00:00
-- url     : https://prove2.me/theorems/c97af9d1-6ff6-43cf-904a-d4cf1a2c3e30
-- title:
--   Lipschitz norm, constructors and point evaluations for the pointed Lipschitz space $\mathrm{Lip}_0(M)$
-- statement:
--   This file collects the basic calculus of the space of pointed Lipschitz functions that underlies the Lipschitz-free space.
--
--   Let $(M,d)$ be a metric space with a base point $o\in M$. $\mathrm{Lip}_0(M)$ is the real vector space of Lipschitz functions $f:M\to\mathbb{R}$ with $f(o)=0$, normed by the sup norm of the slope function $(x,y)\mapsto (f(x)-f(y))/d(x,y)$ on $M\times M$, i.e. by the best Lipschitz constant
--   $$\|f\|=\sup_{x\neq y}\frac{|f(x)-f(y)|}{d(x,y)} .$$
--   For $x\in M$, the evaluation functional $e_x:\mathrm{Lip}_0(M)\to\mathbb{R}$ is $e_x(f)=f(x)$; it is bounded, and the Lipschitz-free space $\mathcal{F}(M)$ is the closed linear span of the $e_x$ in the dual space $\mathrm{Lip}_0(M)^{*}$.
--
--   1. Every $f\in\mathrm{Lip}_0(M)$ vanishes at the base point: $f(o)=0$.
--   2. The norm of $f$ is the $\ell^\infty(M\times M)$-norm of its slope function.
--   3. For every constant $C\ge0$,
--   $$\|f\|\le C\iff |f(x)-f(y)|\le C\,d(x,y)\ \text{ for all } x,y\in M ;$$
--   in particular $|f(x)-f(y)|\le\|f\|\,d(x,y)$ for all $x,y\in M$.
--   4. Any function $f:M\to\mathbb{R}$ with $f(o)=0$ for which some constant $C\ge0$ satisfies $|f(x)-f(y)|\le C\,d(x,y)$ for all $x,y$ defines an element of $\mathrm{Lip}_0(M)$ (whose norm is then at most $C$ by item 3).
--   5. The evaluation functionals satisfy $e_x(f)=f(x)$, and the evaluation at the base point is the zero functional, $e_o=0$.
--
--   These elementary facts are used whenever an explicit Lipschitz test function is built and paired with elements of $\mathcal{F}(M)$: item 3 identifies the norm with the Lipschitz constant, and item 4 is the standard way to produce elements of $\mathrm{Lip}_0(M)$ from explicit formulas.
--
--   **Formalization Note** The objects `Lip0 o`, `Lip0.slope`, `evaluation` and `FreeSpace o` are defined in the mission's base definitions; in the slope function the diagonal terms are $0/0=0$ by Lean's division convention, so the supremum is effectively over $x\neq y$. This file proves `at_base`, `norm_slope`, `norm_le_iff`, `sub_le`, `evaluation_apply`, `evaluation_base`, and defines the constructor `ofBound` of item 4.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/LipschitzFree/Model.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/LipschitzFree/Model.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the DiscreteLipschitzFree mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_DiscreteLipschitzFree
import Definitions.Def_OAI_Analysis_LipschitzFree_PortGraphs
import Definitions.Def_OAI_Analysis_LipschitzFree_RenormingModel

namespace OAI

/-!
# Real Lipschitz-free spaces and compact-uniform approximation properties
-/

noncomputable section
open scoped BigOperators ENNReal

namespace DiscreteFree

variable {M : Type*} [MetricSpace M]

namespace Lip0

variable {o : M}

@[simp] theorem at_base (f : Lip0 o) : f o = 0 := f.property.1

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

@[simp] theorem evaluation_apply (o x : M) (f : Lip0 o) : evaluation o x f = f x := rfl

@[simp] theorem evaluation_base (o : M) : evaluation o o = 0 := by
  ext f
  exact Lip0.at_base f

end DiscreteFree

end

end OAI


