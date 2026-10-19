-- Prove2me | Definitions.Def_OAI_Analysis_C0Absorption_Lists
-- name    : OAI_Analysis_C0Absorption_Lists
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T20:56:44.20306+00:00
-- url     : https://prove2.me/theorems/6156bb70-9c47-4428-b729-d3d62f8bd2b5
-- title:
--   List seminorms on the completed test space
-- statement:
--   These notions belong to the construction of a separable Banach space $Z$ that contains no linear copy of $c_0$, yet $Z\times c_0$ is bi-Lipschitz equivalent to $Z$ and $Z$ is Lipschitz-universal for separable metric spaces. $Z$ is a completion of the space of molecules on the unit ball of $c_0$ (finitely supported functions with total sum zero), normed by test functions from carefully chosen Lipschitz classes. The $n$-th selected coordinate is $w_n\sigma_n$, where $\sigma_n$ is the list seminorm of the class $L_j$ with constant $C_n$ and exponent $p_n$.
--
--   1. **Completed list seminorms.** $\widehat\sigma_n=w_n^{-1}\widehat q_n$ is the extension of $\sigma_n$ to the completion $Z$. On molecules, $\sigma_n(m)\le w_n^{-1}\|m\|$.
--   2. **Completed lists.** For an admissible list $(f_1,\dots,f_k)$, the evaluation $m\mapsto(\langle f_i,m\rangle)_i\in\ell^{p_n}_k$ is bounded with norm at most $w_n^{-1}$. It extends to a continuous linear map on $Z$.
--   3. **Supremum.**
--   $$
--   \sigma^{\mathrm{lists}}_n(z)=\sup_{\text{lists}}\bigl\|(\widehat{\langle f_i,\cdot\rangle}(z))_i\bigr\|_{\ell^{p_n}},
--   $$
--   the list seminorm computed directly on $Z$ through the extended evaluations.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/C0Absorption/Lists.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/C0Absorption/Lists.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the C0Absorption mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_C0Absorption
import Definitions.Def_OAI_Analysis_C0Absorption_Molecules
import Definitions.Def_OAI_Analysis_C0Absorption_Norm
import Definitions.Def_OAI_Analysis_C0Absorption_Completion
import Definitions.Def_OAI_Analysis_C0Absorption_Signs

namespace OAI

namespace C0Absorption

open scoped BigOperators NNReal ENNReal
noncomputable section
open Finset

section CompletedLists

open UniformSpace Completion
variable {S : Type*} [MetricSpace S] (L : ℕ → Set (S → ℝ)) (o : S)

def completedSigma (n : ℕ) : Seminorm ℝ (TestSpace L o) :=
  (squareWeight n)⁻¹ • completedCoordinate L o n

@[simp] theorem completedSigma_coe (n : ℕ) (m : PreSpace L o) :
    completedSigma L o n (toTestSpace L o m) =
      sigma (L (triple n).1) (listConstant n) (listExponent n) m := by
  simp only [completedSigma, smul_apply, NNReal.smul_def, NNReal.coe_inv,
    completedCoordinate_coe, smul_eq_mul]
  change (squareWeight n : ℝ)⁻¹ * ((squareWeight n : ℝ) *
    sigma (L (triple n).1) (listConstant n) (listExponent n) m) = _
  rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt (squareWeight_pos n)), one_mul]

theorem sigma_le_preNorm (n : ℕ) (m : PreSpace L o) :
    sigma (L (triple n).1) (listConstant n) (listExponent n) m ≤
      (squareWeight n : ℝ)⁻¹ * ‖m‖ := by
  have h := selectedCoordinate_le_norm L o n m
  change (squareWeight n : ℝ) *
    sigma (L (triple n).1) (listConstant n) (listExponent n) m ≤ 1 * ‖m‖ at h
  rw [one_mul] at h
  have hm := mul_le_mul_of_nonneg_left h (inv_nonneg.mpr (squareWeight n).coe_nonneg)
  simpa only [← mul_assoc, inv_mul_cancel₀ (ne_of_gt (squareWeight_pos n)), one_mul] using hm

def initialList (n : ℕ) (l : AdmissibleList (L (triple n).1) (listConstant n)) :
    PreSpace L o →L[ℝ] PiLp (listExponent n) (fun _ : Fin l.length => ℝ) :=
  (show PreSpace L o →ₗ[ℝ] PiLp (listExponent n) (fun _ : Fin l.length => ℝ) from
    l.eval (listExponent n)).mkContinuous (squareWeight n : ℝ)⁻¹ (fun m => by
      exact (list_le_sigma _ _ _ o l m).trans (sigma_le_preNorm L o n m))

def completedList (n : ℕ) (l : AdmissibleList (L (triple n).1) (listConstant n)) :
    TestSpace L o →L[ℝ] PiLp (listExponent n) (fun _ : Fin l.length => ℝ) :=
  (initialList L o n l).extend (toTestSpace L o)

@[simp] theorem completedList_coe (n : ℕ)
    (l : AdmissibleList (L (triple n).1) (listConstant n)) (m : PreSpace L o) :
    completedList L o n l (toTestSpace L o m) = l.eval (listExponent n) m :=
  ContinuousLinearMap.extend_eq _ Completion.denseRange_coe
    (Completion.isUniformInducing_coe (PreSpace L o)) m

def completedListNorm (n : ℕ)
    (l : AdmissibleList (L (triple n).1) (listConstant n)) : Seminorm ℝ (TestSpace L o) :=
  (normSeminorm ℝ _).comp (completedList L o n l).toLinearMap

def sigmaFromLists (n : ℕ) : Seminorm ℝ (TestSpace L o) :=
  ⨆ l, completedListNorm L o n l

end CompletedLists

section InterpolationAndDenseLimits

end InterpolationAndDenseLimits

end
end C0Absorption

end OAI


