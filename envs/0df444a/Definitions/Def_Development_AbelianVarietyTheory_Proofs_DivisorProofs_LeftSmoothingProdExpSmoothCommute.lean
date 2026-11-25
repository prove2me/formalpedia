-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LeftSmoothingProdExpSmoothCommute
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_LeftSmoothingProdExpSmoothCommute
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T01:07:27.906491+00:00
-- url     : https://prove2.me/theorems/d8d4421c-b248-46b0-8de0-262dabcda331
-- title:
--   Left Smoothing Prod Exp Smooth Commute
-- statement:
--   Definitions and structural lemmas for Left Smoothing Prod Exp Smooth Commute, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LeftSmoothingProdExpSmoothCommute.lean

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_Casimir
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraRegularity_ExpHaar
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraInvariance_Compact
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavin
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_ParametricIntegral
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_AdL_apply
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_Ad_one
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_Ad
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_bracket
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_rightDerivEnd
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_rightTranslateEnd
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_continuous_prodExp
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_derivLie_apply
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_val_prodExp
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_coe_restrict_apply
import Theorems.Thm_GroundTheory_Automorphic_conjCME_apply
import Theorems.Thm_GroundTheory_Automorphic_contDiff_integral_of_iteratedFDeriv
import Theorems.Thm_GroundTheory_Automorphic_contDiff_prodExpVal
import Theorems.Thm_P2M_GroundTheory_Automorphic_IsExpLieAlgebra_rightUAction___d9062316eb7b
import Theorems.Thm_P2M_GroundTheory_Automorphic_IsExpLieAlgebra_uAction___195cbae0e32a
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.AdL_apply
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.Ad_one
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.coe_Ad
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.coe_bracket
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.coe_rightDerivEnd
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.coe_rightTranslateEnd
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.derivLie_apply
attribute [local simp] GroundTheory.Automorphic.UnitaryRep.coe_restrict_apply
attribute [local simp] GroundTheory.Automorphic.conjCME_apply
attribute [local simp] P2M_GroundTheory_Automorphic_IsExpLieAlgebra_rightUAction___d9062316eb7b
attribute [local simp] P2M_GroundTheory_Automorphic_IsExpLieAlgebra_uAction___195cbae0e32a


set_option autoImplicit false
open MeasureTheory GroundTheory.Automorphic
open scoped ContDiff
namespace GlobalTheory.LeftSmoothing
open scoped Manifold Topology
open Set Filter
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
  {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸}
theorem contMDiff_prodExp (h : IsExpLieAlgebra G 𝔤) {n : ℕ} (X : Fin n → 𝔤) :
    letI := h.chartedSpace; ContMDiff 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, 𝔤) ∞ (h.prodExp X) := by
  letI := h.chartedSpace
  intro t
  refine h.contMDiffAt_of_val ?_
  have e : (fun s => (((h.prodExp X s : G) : 𝔸ˣ) : 𝔸)) = prodExpVal (fun i => (X i : 𝔸)) :=
    funext fun s => h.val_prodExp X s
  rw [e]
  exact (contDiff_prodExpVal _).contMDiff.contMDiffAt
theorem contDiff_param (h : IsExpLieAlgebra G 𝔤) {n : ℕ} (X : Fin n → 𝔤) {f : G → ℂ}
    (hf : h.IsSmoothFun f) (g : G) :
    ContDiff ℝ ∞ (fun p : 𝔤 × (Fin n → ℝ) => f (h.prodExp X p.2 * g * h.expG p.1)) := by
  letI := h.chartedSpace
  haveI := h.lieGroup ∞
  have hm : ContMDiff 𝓘(ℝ, 𝔤 × (Fin n → ℝ)) 𝓘(ℝ, 𝔤) ∞
      (fun p : 𝔤 × (Fin n → ℝ) => h.prodExp X p.2 * g * h.expG p.1) :=
    (((contMDiff_prodExp h X).comp contDiff_snd.contMDiff).mul contMDiff_const).mul
      (h.contMDiff_expG_comp contDiff_fst)
  exact (ContMDiff.comp (I' := 𝓘(ℝ, 𝔤)) hf hm).contDiff
theorem continuous_iteratedFDeriv_partial {P T E' : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup T] [NormedSpace ℝ T] [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {Φ : P × T → E'} (hΦ : ContDiff ℝ ∞ Φ) (k : ℕ) :
    Continuous (fun p : P × T => iteratedFDeriv ℝ k (fun Y => Φ (Y, p.2)) p.1) := by
  set L := ContinuousLinearMap.inl ℝ P T
  set H : P × T → ContinuousMultilinearMap ℝ (fun _ : Fin k => P) E' :=
    fun q => ContinuousMultilinearMap.compContinuousLinearMapL (fun _ => L) (iteratedFDeriv ℝ k Φ q)
  have hH : Continuous H :=
    (ContinuousLinearMap.continuous _).comp (hΦ.continuous_iteratedFDeriv (by exact_mod_cast le_top))
  have hpart : ∀ (Z : T) (Y : P), iteratedFDeriv ℝ k (fun Y => Φ (Y, Z)) Y = H (Y, Z) := by
    intro Z Y
    have e : (fun Y => Φ (Y, Z)) = (fun w => Φ (w + (0, Z))) ∘ L := by
      funext Y; simp [L]
    have hΦZ : ContDiff ℝ ∞ (fun w : P × T => Φ (w + (0, Z))) :=
      hΦ.comp (contDiff_id.add contDiff_const)
    rw [e, L.iteratedFDeriv_comp_right hΦZ Y (by exact_mod_cast le_top),
      iteratedFDeriv_comp_add_right]
    simp [H, L]
  have e : (fun p : P × T => iteratedFDeriv ℝ k (fun Y => Φ (Y, p.2)) p.1) = H := by
    funext p; exact hpart p.2 p.1
  rw [e]; exact hH
variable (h : IsExpLieAlgebra G 𝔤) {n : ℕ} (X : Fin n → 𝔤) (κ : (Fin n → ℝ) → ℂ)
noncomputable def integrand (f : G → ℂ) (g : G) (Y : 𝔤) (t : Fin n → ℝ) : ℂ :=
  κ t * f (h.prodExp X t * g * h.expG Y)
noncomputable def conv (f : G → ℂ) (y : G) : ℂ :=
  ∫ t, κ t * f (h.prodExp X t * y)
theorem conv_mul_expG (f : G → ℂ) (g : G) (Y : 𝔤) :
    conv h X κ f (g * h.expG Y) = ∫ t, integrand h X κ f g Y t := by
  simp only [conv, integrand, mul_assoc]
variable {h X κ}
theorem contDiff_slice {f : G → ℂ} (hf : h.IsSmoothFun f) (g : G) (t : Fin n → ℝ) :
    ContDiff ℝ ∞ (fun Y : 𝔤 => f (h.prodExp X t * g * h.expG Y)) :=
  (contDiff_param h X hf g).comp (contDiff_id.prodMk contDiff_const)
theorem iter_integrand_eq {f : G → ℂ} (hf : h.IsSmoothFun f) (g : G) (k : ℕ) (Y : 𝔤)
    (t : Fin n → ℝ) :
    ParamIntegral.iter (integrand h X κ f g) k Y t =
      (ContinuousLinearMap.mul ℝ ℂ (κ t)).compContinuousMultilinearMap
        (iteratedFDeriv ℝ k (fun Y : 𝔤 => f (h.prodExp X t * g * h.expG Y)) Y) := by
  rw [ParamIntegral.iter]
  have e : (fun Y => integrand h X κ f g Y t) =
      (ContinuousLinearMap.mul ℝ ℂ (κ t)) ∘ (fun Y : 𝔤 => f (h.prodExp X t * g * h.expG Y)) := by
    funext Y; simp [integrand]
  rw [e]
  exact (ContinuousLinearMap.mul ℝ ℂ (κ t)).iteratedFDeriv_comp_left
    (contDiff_slice hf g t).contDiffAt (by exact_mod_cast le_top)
theorem integrand_contDiff {f : G → ℂ} (hf : h.IsSmoothFun f) (g : G) (t : Fin n → ℝ) :
    ContDiff ℝ ∞ (fun Y => integrand h X κ f g Y t) := by
  have e : (fun Y => integrand h X κ f g Y t) =
      (ContinuousLinearMap.mul ℝ ℂ (κ t)) ∘ (fun Y : 𝔤 => f (h.prodExp X t * g * h.expG Y)) := by
    funext Y; simp [integrand]
  rw [e]
  exact (ContinuousLinearMap.mul ℝ ℂ (κ t)).contDiff.comp (contDiff_slice hf g t)
theorem integrand_cont (hκ : Continuous κ) {f : G → ℂ} (hf : h.IsSmoothFun f) (g : G) (k : ℕ) :
    Continuous (fun p : 𝔤 × (Fin n → ℝ) => ParamIntegral.iter (integrand h X κ f g) k p.1 p.2) := by
  simp_rw [iter_integrand_eq hf]
  have hc := continuous_iteratedFDeriv_partial (contDiff_param h X hf g) k
  have hL : Continuous (fun t => ContinuousLinearMap.mul ℝ ℂ (κ t)) :=
    (ContinuousLinearMap.mul ℝ ℂ).continuous.comp hκ
  have hB := ContinuousLinearMap.continuous₂ (𝕜 := ℝ) (E := ℂ →L[ℝ] ℂ)
    (F := ContinuousMultilinearMap ℝ (fun _ : Fin k => 𝔤) ℂ)
    (G := ContinuousMultilinearMap ℝ (fun _ : Fin k => 𝔤) ℂ)
    (ContinuousLinearMap.compContinuousMultilinearMapL ℝ (fun _ : Fin k => 𝔤) ℂ ℂ)
  exact hB.comp ((hL.comp continuous_snd).prodMk hc)
theorem integrand_supp (hκs : HasCompactSupport κ) (f : G → ℂ) (g : G) (Y₀ : 𝔤) :
    ∃ U ∈ 𝓝 Y₀, ∃ C : Set (Fin n → ℝ), IsCompact C ∧
      ∀ Y ∈ U, ∀ t ∉ C, integrand h X κ f g Y t = 0 :=
  ⟨univ, univ_mem, tsupport κ, hκs, fun Y _ t ht => by
    simp [integrand, image_eq_zero_of_notMem_tsupport ht]⟩
theorem isSmoothFun_conv (hκ : Continuous κ) (hκs : HasCompactSupport κ) {f : G → ℂ}
    (hf : h.IsSmoothFun f) : h.IsSmoothFun (conv h X κ f) := by
  rw [IsExpLieAlgebra.isSmoothFun_iff]
  intro g
  simp_rw [conv_mul_expG]
  exact contDiff_integral_of_iteratedFDeriv _ (integrand_contDiff hf g)
    (integrand_cont hκ hf g) (integrand_supp hκs f g)
variable (h X) in

noncomputable def convEnd (hκ : Continuous κ) (hκs : HasCompactSupport κ) :
    Module.End ℂ (h.smoothFuns (F := ℂ)) where
  toFun f := ⟨conv h X κ f, isSmoothFun_conv hκ hκs f.2⟩
  map_add' f₁ f₂ := by
    apply Subtype.ext
    funext y
    have hc : ∀ f : h.smoothFuns (F := ℂ), Integrable (fun t => κ t * (f : G → ℂ) (h.prodExp X t * y)) := by
      intro f
      have hfc : Continuous (f : G → ℂ) := by
        letI := h.chartedSpace
        exact (show h.IsSmoothFun (f : G → ℂ) from f.2).continuous
      exact (hκ.mul (hfc.comp ((h.continuous_prodExp X).mul continuous_const))).integrable_of_hasCompactSupport
        (hκs.mul_right)
    show ∫ t, κ t * ((f₁ : G → ℂ) + f₂) (h.prodExp X t * y) = (∫ t, κ t * (f₁ : G → ℂ) (h.prodExp X t * y)) + ∫ t, κ t * (f₂ : G → ℂ) (h.prodExp X t * y)
    rw [← integral_add (hc f₁) (hc f₂)]
    congr 1; funext t; simp [mul_add]
  map_smul' c f := by
    apply Subtype.ext
    funext y
    show ∫ t, κ t * (c • (f : G → ℂ)) (h.prodExp X t * y) = c * ∫ t, κ t * (f : G → ℂ) (h.prodExp X t * y)
    rw [← integral_const_mul]
    congr 1; funext t; simp only [Pi.smul_apply, smul_eq_mul]; ring
end GlobalTheory.LeftSmoothing


