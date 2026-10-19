-- Prove2me | Definitions.Def_OAI_Analysis_TriangularHilbert_ErrorEnvelope
-- name    : OAI_Analysis_TriangularHilbert_ErrorEnvelope
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T00:48:42.417907+00:00
-- url     : https://prove2.me/theorems/9056ce8d-9c5a-4260-9a43-da1c6ddd3bf2
-- title:
--   Endpoint error of the smooth Hilbert kernel and its envelope
-- statement:
--   Let $\kappa_0=-\frac23\phi_3(0)$ and $\mathrm{kernelProfile}(v)=\kappa_0-2(\frac{v^2}9-\frac13)\phi_3(v)$, where $\phi_\sigma$ is the centred Gaussian density of variance $\sigma$.
--
--   1. **Error profile.** $\mathrm{errorProfile}(v)=\mathrm{kernelProfile}(v)-\kappa_0\mathbf 1_{|v|>1}$, the difference between the smooth profile and a sharp step.
--   2. **Endpoint error.**
--   $$
--   \mathrm{endpointError}(r,t)=\frac{\mathrm{errorProfile}(t/r)}t .
--   $$
--   3. **Envelope.** The profile vanishes at $0$, is $C^1$, and $\phi_3(v)=\sqrt2e^{-v^2/12}\phi_6(v)$. Hence there is $K>0$ with $|\mathrm{errorProfile}(v)|\le K|v|\phi_6(v)$ for all $v$. The envelope constant is a chosen such $K$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/TriangularHilbert/ErrorEnvelope.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/TriangularHilbert/ErrorEnvelope.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the TriangularHilbert mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_TriangularHilbert
import Definitions.Def_OAI_Analysis_TriangularHilbert_Gaussian
import Definitions.Def_OAI_Analysis_TriangularHilbert_MeshMass
import Definitions.Def_OAI_Analysis_TriangularHilbert_GaussianMoments
import Definitions.Def_OAI_Analysis_TriangularHilbert_SignedWindowScalar
import Definitions.Def_OAI_Analysis_TriangularHilbert_MatrixSupport
import Definitions.Def_OAI_Analysis_TriangularHilbert_Support
import Definitions.Def_OAI_Analysis_TriangularHilbert_WeightedGram
import Definitions.Def_OAI_Analysis_TriangularHilbert_WeightedStar
import Definitions.Def_OAI_Analysis_TriangularHilbert_GroupedGaussian
import Definitions.Def_OAI_Analysis_TriangularHilbert_HeatStar
import Definitions.Def_OAI_Analysis_TriangularHilbert_HeatCost
import Definitions.Def_OAI_Analysis_TriangularHilbert_NormBounds
import Definitions.Def_OAI_Analysis_TriangularHilbert_HeatInsert
import Definitions.Def_OAI_Analysis_TriangularHilbert_GaussianDom
import Definitions.Def_OAI_Analysis_TriangularHilbert_PlaneChart
import Definitions.Def_OAI_Analysis_TriangularHilbert_PlaneDom
import Definitions.Def_OAI_Analysis_TriangularHilbert_HeatBound
import Definitions.Def_OAI_Analysis_TriangularHilbert_GramDeriv
import Definitions.Def_OAI_Analysis_TriangularHilbert_PlaneIntegral
import Definitions.Def_OAI_Analysis_TriangularHilbert_PlaneDissipation
import Definitions.Def_OAI_Analysis_TriangularHilbert_SignedTraceOrder
import Definitions.Def_OAI_Analysis_TriangularHilbert_MassPlane
import Definitions.Def_OAI_Analysis_TriangularHilbert_SignedConvolution
import Definitions.Def_OAI_Analysis_TriangularHilbert_RankJump
import Definitions.Def_OAI_Analysis_TriangularHilbert_ZeroStar
import Definitions.Def_OAI_Analysis_TriangularHilbert_StarJump
import Definitions.Def_OAI_Analysis_TriangularHilbert_InitialAlgebra
import Definitions.Def_OAI_Analysis_TriangularHilbert_InitialPlane
import Definitions.Def_OAI_Analysis_TriangularHilbert_TotalJump
import Definitions.Def_OAI_Analysis_TriangularHilbert_IntWeak
import Definitions.Def_OAI_Analysis_TriangularHilbert_StrongLayer
import Definitions.Def_OAI_Analysis_TriangularHilbert_IntMax
import Definitions.Def_OAI_Analysis_TriangularHilbert_FiniteLineMax
import Definitions.Def_OAI_Analysis_TriangularHilbert_MeshJump
import Definitions.Def_OAI_Analysis_TriangularHilbert_JumpScalar
import Definitions.Def_OAI_Analysis_TriangularHilbert_Switch
import Definitions.Def_OAI_Analysis_TriangularHilbert_MaskedDissipation
import Definitions.Def_OAI_Analysis_TriangularHilbert_SortedWindows
import Definitions.Def_OAI_Analysis_TriangularHilbert_MaskedActual
import Definitions.Def_OAI_Analysis_TriangularHilbert_SignedCenter
import Definitions.Def_OAI_Analysis_TriangularHilbert_SelectedScale
import Definitions.Def_OAI_Analysis_TriangularHilbert_DiscretePairing
import Definitions.Def_OAI_Analysis_TriangularHilbert_SmoothFormula

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

section
namespace TriangularHilbert.Heat
open MeasureTheory
noncomputable section

def errorProfile (v : ℝ) : ℝ := kernelProfile v - if 1 < |v| then kernelConstant else 0

def endpointError (r t : ℝ) : ℝ := errorProfile (t/r)/t

lemma kernelProfile_zero : kernelProfile 0 = 0 := by
  unfold kernelProfile kernelConstant
  ring

lemma profile_contDiff : ContDiff ℝ 1 kernelProfile := by
  unfold kernelProfile density
  fun_prop

lemma density_three_six (v : ℝ) :
    density 3 v = Real.sqrt 2*Real.exp (-v^2/12)*density 6 v := by
  have hp : Real.sqrt (2*Real.pi*3) ≠ 0 := by positivity
  have h2 : Real.sqrt (2:ℝ) ≠ 0 := by positivity
  unfold density
  rw [show 2*Real.pi*6 = 2*(2*Real.pi*3) by ring,Real.sqrt_mul (by norm_num : (0:ℝ)≤2)]
  have he : -v^2/(2*3) = -v^2/12 + -v^2/(2*6) := by ring
  rw [he,Real.exp_add]
  field_simp

lemma polynomial_exp_le (v : ℝ) : (v^2/9+1/3)*Real.exp (-v^2/12) ≤ 5/3 := by
  have ha := Real.add_one_le_exp (v^2/12)
  have he : Real.exp (v^2/12)*Real.exp (-v^2/12) = 1 := by
    rw [← Real.exp_add,show v^2/12+-v^2/12=0 by ring,Real.exp_zero]
  have hm := mul_le_mul_of_nonneg_right ha (Real.exp_pos (-v^2/12)).le
  rw [he] at hm
  have hle : Real.exp (-v^2/12) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg v])
  nlinarith

lemma errorProfile_exists_bound : ∃ K : ℝ, 0 < K ∧ ∀ v,
    |errorProfile v| ≤ K*|v| *density 6 v := by
  obtain ⟨L,hL⟩ := profile_contDiff.contDiffOn.exists_lipschitzOnWith
    (by norm_num : (1:WithTop ℕ∞) ≠ 0) (convex_Icc (-1:ℝ) 1) (isCompact_Icc (a := (-1:ℝ)) (b := 1))
  let K : ℝ := (L:ℝ)/density 6 1 + 10*Real.sqrt 2
  have hd : 0 < density 6 1 := density_pos (by norm_num) 1
  have hK : 0 < K := add_pos_of_nonneg_of_pos (div_nonneg L.coe_nonneg hd.le) (by positivity)
  refine ⟨K,hK,fun v => ?_⟩
  by_cases hv : 1 < |v|
  · have he : errorProfile v = -2*(v^2/9-1/3)*density 3 v := by
      unfold errorProfile kernelProfile
      rw [ite_eq_left hv]
      ring
    have hab : |v^2/9-1/3| ≤ v^2/9+1/3 := by
      exact abs_le.mpr ⟨by nlinarith [sq_nonneg v],by linarith⟩
    have hb : |errorProfile v| ≤ (10/3)*Real.sqrt 2*density 6 v := by
      rw [he,abs_mul,abs_mul,abs_of_nonneg (density_nonneg (by norm_num) v)]
      norm_num only [abs_neg]
      calc
        _ ≤ 2*(v^2/9+1/3)*density 3 v := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hab (by norm_num)) (density_nonneg (by norm_num) v)
        _ = 2*Real.sqrt 2*((v^2/9+1/3)*Real.exp (-v^2/12))*density 6 v := by rw [density_three_six]; ring
        _ ≤ 2*Real.sqrt 2*(5/3)*density 6 v := by
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (polynomial_exp_le v) (by positivity)) (density_nonneg (by norm_num) v)
        _ = _ := by ring
    apply hb.trans
    have hk : 10*Real.sqrt 2 ≤ K := le_add_of_nonneg_left (div_nonneg L.coe_nonneg hd.le)
    apply mul_le_mul_of_nonneg_right _ (density_nonneg (by norm_num) v)
    calc
      (10/3)*Real.sqrt 2 ≤ 10*Real.sqrt 2 := by gcongr; norm_num
      _ ≤ K := hk
      _ ≤ K*|v| := le_mul_of_one_le_right hK.le hv.le
  · have hv' : |v| ≤ 1 := le_of_not_gt hv
    have hmem : v ∈ Set.Icc (-1:ℝ) 1 := abs_le.mp hv'
    have hb : |kernelProfile v| ≤ (L:ℝ)*|v| := by
      have hh := hL.dist_le_mul v hmem 0 (by constructor <;> norm_num)
      simpa only [Real.dist_eq,kernelProfile_zero,sub_zero] using hh
    have hden : density 6 1 ≤ density 6 v := by
      unfold density
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Real.exp_le_exp.mpr
      have hs : v^2 ≤ 1 := by nlinarith [sq_abs v,abs_nonneg v]
      nlinarith
    unfold errorProfile
    rw [ite_eq_right hv,sub_zero]
    apply hb.trans
    have hk : (L:ℝ) ≤ K*density 6 v := by
      calc
        (L:ℝ) = ((L:ℝ)/density 6 1)*density 6 1 := (div_mul_cancel₀ _ hd.ne').symm
        _ ≤ ((L:ℝ)/density 6 1)*density 6 v := mul_le_mul_of_nonneg_left hden (div_nonneg L.coe_nonneg hd.le)
        _ ≤ K*density 6 v := mul_le_mul_of_nonneg_right
          (le_add_of_nonneg_right (by positivity)) (density_nonneg (by norm_num) v)
    nlinarith [mul_le_mul_of_nonneg_right hk (abs_nonneg v)]

def envelopeConstant : ℝ := errorProfile_exists_bound.choose
lemma envelopeConstant_pos : 0 < envelopeConstant := errorProfile_exists_bound.choose_spec.1
end
end TriangularHilbert.Heat
end

end OAI


