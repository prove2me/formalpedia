-- Prove2me | Definitions.Def_CK_GeneralCK_PsiEndpointPlaneLaw
-- name    : CK_GeneralCK_PsiEndpointPlaneLaw
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T12:46:40.692472+00:00
-- url     : https://prove2.me/theorems/77e7d44a-e722-4ed7-a657-50bf9c6fc089
-- title:
--   Courtade–Kumar proof module `GeneralCK.PsiEndpointPlaneLaw` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PsiEndpointPlaneLaw` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PsiEndpointPlaneLaw` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PsiEndpointPlaneLaw (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PsiEndpointPlaneLaw.lean)

import Definitions.Def_CK_GeneralCK_PsiEndpointPlaneQuotientDefs
import Definitions.Def_CK_GeneralCK_PsiEndpointContactGain

-- ===== source module GeneralCK.PsiEndpointPlaneLaw =====
section

/-!
# Integrating the endpoint supporting plane

The supporting plane is averaged against an arbitrary finite interior law.
The contact mass and entropy equations cancel its affine terms exactly.
-/

namespace GeneralCK.PsiEndpointPlane

theorem naturalCost_nonneg {x y : ℝ} (hx : 0 < x) (hx1 : x < 1)
    (hy : 0 < y) (hy1 : y < 1) : 0 ≤ naturalCost x y := by
  have hordered : ∀ {u v : ℝ}, 0 < u → u < 1 → 0 < v → v < 1 →
      u ≤ v → 0 ≤ interiorCost u v := by
    intro u v hu hu1 hv hv1 huv
    have hratio : (1 - v) / v ≤ (1 - u) / u := by
      apply (div_le_div_iff₀ hv hu).2
      nlinarith
    have hlog := Real.log_le_log (div_pos (sub_pos.mpr hv1) hv) hratio
    have hJ : J v ≤ J u := div_le_div_of_nonneg_right hlog log_two_pos.le
    exact div_nonneg (mul_nonneg (sub_nonneg.mpr huv) (sub_nonneg.mpr hJ)) (by norm_num)
  have hcost : 0 ≤ interiorCost x y := by
    rcases le_total x y with hxy | hyx
    · exact hordered hx hx1 hy hy1 hxy
    · rw [interiorCost_comm]
      exact hordered hy hy1 hx hx1 hyx
  exact mul_nonneg log_two_pos.le hcost

theorem binEntropy_eq_log_two_mul_H (x : ℝ) :
    Real.binEntropy x = Real.log 2 * H x := by
  unfold H
  field_simp [log_two_pos.ne']

theorem avg_naturalCost {ι : Type*} [Fintype ι] (μ : InteriorLaw ι) :
    μ.avg (fun i => naturalCost (μ.left i) (μ.right i)) = Real.log 2 * μ.cost := by
  exact LogSum.avg_const_mul μ (Real.log 2) _

theorem avg_binEntropy_left {ι : Type*} [Fintype ι] (μ : InteriorLaw ι) :
    μ.avg (fun i => Real.binEntropy (μ.left i)) = Real.log 2 * μ.e := by
  simp_rw [binEntropy_eq_log_two_mul_H]
  exact LogSum.avg_const_mul μ (Real.log 2) _

theorem avg_binEntropy_right {ι : Type*} [Fintype ι] (μ : InteriorLaw ι) :
    μ.avg (fun i => Real.binEntropy (μ.right i)) = Real.log 2 * μ.f := by
  simp_rw [binEntropy_eq_log_two_mul_H]
  exact LogSum.avg_const_mul μ (Real.log 2) _

theorem averaged_supporting_plane {ι : Type*} [Fintype ι] (μ : InteriorLaw ι)
    {A B C : ℝ}
    (hplane : ∀ u v : ℝ, 0 < u → u < 1 → 0 < v → v < 1 →
      C * (v - u) ≤ naturalCost u v + A * Real.binEntropy u + B * Real.binEntropy v) :
    C * (μ.b - μ.a) ≤ Real.log 2 * μ.cost +
      A * (Real.log 2 * μ.e) + B * (Real.log 2 * μ.f) := by
  have h := μ.avg_mono (fun i => hplane (μ.left i) (μ.right i)
    (μ.left_interior i).1 (μ.left_interior i).2
    (μ.right_interior i).1 (μ.right_interior i).2)
  rw [LogSum.avg_const_mul, μ.avg_sub, μ.avg_add, μ.avg_add,
    LogSum.avg_const_mul, LogSum.avg_const_mul,
    avg_naturalCost, avg_binEntropy_left, avg_binEntropy_right] at h
  exact h

end GeneralCK.PsiEndpointPlane

namespace GeneralCK.PsiEndpointContact.Contact
open PsiEndpointPlane

/-- Any genuine pointwise supporting plane with equality at the contact
proves the contact lower bound for every law having its three moments. -/
theorem value_le_cost_of_supporting_plane {ι : Type*} [Fintype ι]
    (μ : InteriorLaw ι) (c : Contact (μ.b - μ.a) μ.e μ.f) {A B C : ℝ}
    (hplane : ∀ u v : ℝ, 0 < u → u < 1 → 0 < v → v < 1 →
      C * (v - u) ≤ naturalCost u v + A * Real.binEntropy u + B * Real.binEntropy v)
    (hcontact : C * ((1 - c.right) - c.left) =
      naturalCost c.left (1 - c.right) +
        A * Real.binEntropy c.left + B * Real.binEntropy c.right) :
    c.value ≤ μ.cost := by
  have h := averaged_supporting_plane μ hplane
  have hc := congrArg (fun z : ℝ => c.mass * z) hcontact
  have heq : C * (μ.b - μ.a) = Real.log 2 * c.value +
      A * (Real.log 2 * μ.e) + B * (Real.log 2 * μ.f) := by
    simp only [naturalCost, binEntropy_eq_log_two_mul_H] at hc
    dsimp only [value]
    have hd := congrArg (fun z : ℝ => C * z) c.difference_eq
    have he := congrArg (fun z : ℝ => A * (Real.log 2 * z)) c.entropy_left_eq
    have hf := congrArg (fun z : ℝ => B * (Real.log 2 * z)) c.entropy_right_eq
    nlinarith only [hc, hd, he, hf]
  rw [heq] at h
  nlinarith [log_two_pos]

end GeneralCK.PsiEndpointContact.Contact

end


