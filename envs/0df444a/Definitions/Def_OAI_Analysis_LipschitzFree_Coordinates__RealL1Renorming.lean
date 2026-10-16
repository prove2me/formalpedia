-- Prove2me | Definitions.Def_OAI_Analysis_LipschitzFree_Coordinates__RealL1Renorming
-- name    : OAI_Analysis_LipschitzFree_Coordinates__RealL1Renorming
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T11:52:14.371254+00:00
-- url     : https://prove2.me/theorems/18b8c8a4-5abf-4240-9100-ba2cf40bc9fd
-- title:
--   Dual pairing, point-indicator coordinates and finite-support projections on Lipschitz-free spaces of 1-separated spaces
-- statement:
--   Let $(M,d)$ be a metric space with base point $o$, let $\mathrm{Lip}_0(M)$ be the space of real Lipschitz functions on $M$ vanishing at $o$ (normed by the best Lipschitz constant), and let $\mathcal{F}(M)\subseteq\mathrm{Lip}_0(M)^{*}$ be the Lipschitz-free space, the closed span of the evaluation functionals $\delta_x(f)=f(x)$, $x\in M$. This file introduces the pairing between the two spaces and, for uniformly discrete $M$, coordinate functionals and finite-rank projections on $\mathcal{F}(M)$.
--
--   1. **Dual pairing.** For $f\in\mathrm{Lip}_0(M)$, the map $u\mapsto\langle f,u\rangle:=u(f)$ is a bounded linear functional on $\mathcal{F}(M)$ with $\langle f,\delta_x\rangle=f(x)$ and $|\langle f,u\rangle|\le\|u\|\,\|f\|$.
--
--   2. **Centering.** If $g:M\to\mathbb{R}$ and $L\ge 0$ satisfy $|g(x)-g(y)|\le L\,d(x,y)$ for all $x,y$, then $x\mapsto g(x)-g(o)$ is an element of $\mathrm{Lip}_0(M)$.
--
--   From now on $M$ is assumed to be **1-separated**: $d(x,y)\ge 1$ whenever $x\neq y$.
--
--   3. **Bounded functions are Lipschitz.** If $a\le g(x)\le b$ for all $x\in M$, then $|g(x)-g(y)|\le (b-a)\,d(x,y)$ for all $x,y\in M$.
--
--   4. **Point indicators and coordinates.** For $j\in M$ let $\mathbf{1}_j\in\mathrm{Lip}_0(M)$ be the function equal to $1$ at $x=j$ when $j\neq o$, and $0$ everywhere else (so $\mathbf{1}_o=0$); it has Lipschitz constant at most $1$. The $j$-th coordinate functional is $c_j(u)=\langle\mathbf{1}_j,u\rangle$, so that $c_j(\delta_x)=1$ if $x=j\neq o$, $c_j(\delta_x)=0$ otherwise, and $c_o=0$.
--
--   5. **Coefficient bound.** For every finite set $F\subseteq M$ and every $u\in\mathcal{F}(M)$,
--   $$\sum_{j\in F}|c_j(u)|\le 2\,\|u\|.$$
--
--   6. **Finite-support projections.** For a finite set $F\subseteq M$, the bounded linear operator $P_F:\mathcal{F}(M)\to\mathcal{F}(M)$ is
--   $$P_F(u)=\sum_{j\in F}c_j(u)\,\delta_j .$$
--
--   For a 1-separated space the coordinates $c_j$ read off the coefficient of $\delta_j$, and item 5 shows that the coefficient family of any element of $\mathcal{F}(M)$ is absolutely summable with total mass at most $2\|u\|$; this is one half of the identification of $\mathcal{F}(M)$ with an $\ell^1$ space. The operators $P_F$ are the natural finite-rank operators built from these coordinates.
--
--   **Formalization Note** The 1-separation hypothesis is the explicit argument `sep`. Items 1-6 are `dualPairing` (with `dualPairing_bound`), `Lip0.center`, `bounded_test_lipschitz`, `indicator` and `coordinate`, `sum_abs_coordinate_le`, and `supportProjection`. The file also contains pointwise simp lemmas for $\mathrm{Lip}_0(M)$ (`Lip0.zero_apply`, `Lip0.add_apply`, `Lip0.smul_apply`) and the finite-sum identity `sum_point_test` for sums of point indicators.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/LipschitzFree/Coordinates.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/LipschitzFree/Coordinates.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the RealL1Renorming mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_Model__RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_Evaluation__RealL1Renorming

namespace OAI

/-!
# Signed evaluation coefficients and finite-support projections
-/

noncomputable section
open scoped BigOperators ENNReal

noncomputable section
namespace DiscreteFree
open scoped BigOperators Classical
variable {M : Type*} [MetricSpace M] (o : M)

def dualPairing (f : Lip0 o) : FreeSpace o →L[ℝ] ℝ :=
  (ContinuousLinearMap.apply ℝ ℝ f).comp (freeSubmodule o).subtypeL

@[simp] theorem dualPairing_apply (f : Lip0 o) (u : FreeSpace o) : dualPairing o f u = u.val f := rfl
@[simp] theorem dualPairing_delta (f : Lip0 o) (x : M) : dualPairing o f (delta o x) = f x := rfl

theorem dualPairing_bound (f : Lip0 o) (u : FreeSpace o) : |dualPairing o f u| ≤ ‖u‖ * ‖f‖ :=
  u.val.le_opNorm f

namespace Lip0
@[simp] theorem zero_apply (x : M) : (0 : Lip0 o) x = 0 := rfl
@[simp] theorem add_apply (f g : Lip0 o) (x : M) : (f+g) x = f x + g x := rfl
@[simp] theorem smul_apply (c : ℝ) (f : Lip0 o) (x : M) : (c • f) x = c * f x := rfl

def center (g : M → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hg : ∀ x y, |g x - g y| ≤ L * dist x y) : Lip0 o :=
  ofBound o (fun x => g x - g o) (by simp) L hL (by intro x y; simpa using hg x y)

@[simp] theorem center_apply (g : M → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hg : ∀ x y, |g x - g y| ≤ L * dist x y) (x : M) :
    center o g L hL hg x = g x - g o := rfl

end Lip0

variable (sep : ∀ x y : M, x ≠ y → 1 ≤ dist x y)

include sep in

theorem bounded_test_lipschitz {g : M → ℝ} {a b : ℝ}
    (hg : ∀ x, a ≤ g x ∧ g x ≤ b) (x y : M) :
    |g x - g y| ≤ (b-a) * dist x y := by
  have hab : a ≤ b := (hg x).1.trans (hg x).2
  by_cases h : x = y
  · simp [h]
  · have hd := sep x y h
    have hs : |g x - g y| ≤ b-a := by rw [abs_le]; constructor <;> linarith [(hg x).1, (hg x).2, (hg y).1, (hg y).2]
    exact hs.trans (le_mul_of_one_le_right (sub_nonneg.mpr hab) hd)

omit [MetricSpace M] in
theorem sum_point_test {V : Type*} [AddCommMonoid V] (F : Finset M) (x : M) (v : M → V) :
    (∑ j ∈ F, if x = j ∧ j ≠ o then v j else 0) = if x ∈ F ∧ x ≠ o then v x else 0 := by
  have ht (j : M) : (if x = j ∧ j ≠ o then v j else 0) =
      if j = x then (if x ≠ o then v x else 0) else 0 := by
    by_cases h : j = x
    · subst j; simp
    · simp [h, Ne.symm h]
  simp_rw [ht]
  rw [Finset.sum_ite_eq']
  split_ifs <;> simp_all

def indicator (j : M) : Lip0 o :=
  Lip0.ofBound o (fun x => if x = j ∧ j ≠ o then 1 else 0) (by simp [eq_comm]) 1 (by norm_num)
    (by
      intro x y
      have h := bounded_test_lipschitz sep
        (g := fun x => if x = j ∧ j ≠ o then (1 : ℝ) else 0)
        (a := 0) (b := 1) (by intro z; split_ifs <;> norm_num) x y
      simpa using h)

@[simp] theorem indicator_apply (j x : M) : indicator o sep j x = if x = j ∧ j ≠ o then 1 else 0 := rfl

def coordinate (j : M) : FreeSpace o →L[ℝ] ℝ := dualPairing o (indicator o sep j)

@[simp] theorem coordinate_delta (j x : M) : coordinate o sep j (delta o x) = if x = j ∧ j ≠ o then 1 else 0 := rfl

@[simp] theorem coordinate_base : coordinate o sep o = 0 := by
  ext u
  have hi : indicator o sep o = 0 := by apply Subtype.ext; funext x; simp
  simp [coordinate, hi]

theorem sum_abs_coordinate_le (F : Finset M) (u : FreeSpace o) :
    ∑ j ∈ F, |coordinate o sep j u| ≤ 2 * ‖u‖ := by
  let c : M → ℝ := fun j => if 0 ≤ coordinate o sep j u then 1 else -1
  let f : Lip0 o := ∑ j ∈ F, c j • indicator o sep j
  have hfc (x : M) : f x = if x ∈ F ∧ x ≠ o then c x else 0 := by
    change evaluation o x (∑ j ∈ F, c j • indicator o sep j) = _
    simp only [map_sum, map_smul, evaluation_apply, indicator_apply, smul_eq_mul]
    simp only [mul_ite, mul_one, mul_zero]
    exact sum_point_test o F x c
  have hcb (x : M) : -1 ≤ f x ∧ f x ≤ 1 := by
    rw [hfc]
    dsimp [c]
    split_ifs <;> norm_num
  have hf : ‖f‖ ≤ 2 := (Lip0.norm_le_iff f (by norm_num)).mpr (by
    intro x y
    convert bounded_test_lipschitz sep hcb x y using 1; norm_num)
  have hpair : dualPairing o f u = ∑ j ∈ F, |coordinate o sep j u| := by
    change u.val (∑ j ∈ F, c j • indicator o sep j) = _
    simp only [map_sum, map_smul, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro j hj
    change c j * coordinate o sep j u = _
    dsimp [c]
    split_ifs with h
    · rw [one_mul, abs_of_nonneg h]
    · rw [neg_one_mul, abs_of_neg (lt_of_not_ge h)]
  have hh := (dualPairing_bound o f u).trans (mul_le_mul_of_nonneg_left hf (norm_nonneg u))
  rw [hpair, abs_of_nonneg (Finset.sum_nonneg (fun j _ => abs_nonneg _)), mul_comm] at hh
  exact hh

def supportProjection (F : Finset M) : FreeSpace o →L[ℝ] FreeSpace o :=
  ∑ j ∈ F, (coordinate o sep j).smulRight (delta o j)

@[simp] theorem supportProjection_apply (F : Finset M) (u : FreeSpace o) :
    supportProjection o sep F u = ∑ j ∈ F, coordinate o sep j u • delta o j := by
  simp [supportProjection]

end DiscreteFree
end

end

end OAI


