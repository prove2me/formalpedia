-- Prove2me | Definitions.Def_OAI_Analysis_LipschitzFree_Coordinates
-- name    : OAI_Analysis_LipschitzFree_Coordinates
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T09:17:10.387984+00:00
-- url     : https://prove2.me/theorems/d4768d88-d263-492b-84a4-8973b1942d41
-- title:
--   Coordinate functionals and finite-support projections on the free space of a $1$-separated space
-- statement:
--   Let $(M,d)$ be a metric space with base point $o$, let $\mathrm{Lip}_0(M)$ be the space of real Lipschitz functions vanishing at $o$, normed by their Lipschitz constant, and let $\mathcal{F}(M)\subseteq\mathrm{Lip}_0(M)^{*}$ be the Lipschitz-free space, the closed linear span of the point evaluations $\delta_x(f)=f(x)$.
--
--   1. **Duality pairing.** Each $f\in\mathrm{Lip}_0(M)$ defines the bounded linear functional $u\mapsto\langle u,f\rangle=u(f)$ on $\mathcal{F}(M)$; in particular $\langle\delta_x,f\rangle=f(x)$.
--   2. **Centering.** If $L\ge0$ and $g:M\to\mathbb{R}$ satisfies $|g(x)-g(y)|\le L\,d(x,y)$ for all $x,y$, then $x\mapsto g(x)-g(o)$ is an element of $\mathrm{Lip}_0(M)$.
--
--   The remaining items assume that $M$ is $1$-separated: $d(x,y)\ge1$ whenever $x\neq y$.
--
--   3. **Bounded functions are Lipschitz.** If $a\le g(x)\le b$ for all $x\in M$, then $|g(x)-g(y)|\le(b-a)\,d(x,y)$ for all $x,y\in M$.
--   4. **Coordinates.** For $j\in M$ let $\mathbf{1}_j\in\mathrm{Lip}_0(M)$ be the indicator function of $\{j\}$ if $j\neq o$, and the zero function if $j=o$ (it is $1$-Lipschitz by item 3). The coordinate functional $c_j(u)=\langle u,\mathbf{1}_j\rangle$ is a bounded linear functional on $\mathcal{F}(M)$ with
--   $$c_j(\delta_x)=\begin{cases}1, & x=j\neq o,\\ 0, & \text{otherwise,}\end{cases}\qquad\text{and}\qquad c_o=0 .$$
--   5. **Support projections.** For a finite set $F\subseteq M$, the bounded linear operator $P_F:\mathcal{F}(M)\to\mathcal{F}(M)$ is
--   $$P_F(u)=\sum_{j\in F}c_j(u)\,\delta_j .$$
--
--   In a $1$-separated space indicator functions of points are Lipschitz, so every element of $\mathcal{F}(M)$ has coordinates $c_j$ with respect to the point masses. The operator $P_F$ has finite rank, fixes $\delta_j$ for $j\in F$ and sends $\delta_x$ to $0$ for $x\notin F$; it is used to replace a finite-rank operator by one whose range lies in the span of finitely many point masses.
--
--   **Formalization Note** `dualPairing`, `Lip0.center`, `bounded_test_lipschitz`, `indicator`, `coordinate` and `supportProjection` are the objects above; the last four take the separation hypothesis `sep : ∀ x y, x ≠ y → 1 ≤ dist x y` as an explicit argument, and the finite set is a `Finset M`. `Lip0.zero_apply`, `add_apply`, `smul_apply` are pointwise simp lemmas.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/LipschitzFree/Coordinates.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/LipschitzFree/Coordinates.lean by skeleton subtraction
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

def supportProjection (F : Finset M) : FreeSpace o →L[ℝ] FreeSpace o :=
  ∑ j ∈ F, (coordinate o sep j).smulRight (delta o j)

@[simp] theorem supportProjection_apply (F : Finset M) (u : FreeSpace o) :
    supportProjection o sep F u = ∑ j ∈ F, coordinate o sep j u • delta o j := by
  simp [supportProjection]

end DiscreteFree
end

end

end OAI


