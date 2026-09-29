-- Prove2me | solution 1 for AutomorphicForm.isKfSmooth_rightConv
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/1a25808b-3583-57f1-8a79-e08dcb75d92b

import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_NumberField_AdelicBox
import Theorems.Thm_IsLocallyConstant_exists_nhds_one_forall_apply_mul_mul_eq_of_hasCompactSupport
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_isKfSmooth_rightConv

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.AdelicBox NumberField.AdelicLevel NumberField.AdelicHaar MeasureTheory
open AutomorphicForm
open scoped Topology

theorem solution
    (F : Type) [Field F] [NumberField F]
    (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (f : AdelicGL2 (𝓞 F) F → ℂ) (hf : IsFactorizableTestFn F f) :
    IsKfSmooth F (rightConv F φ f) := by
  classical
  obtain ⟨fa, ff, hfa, hff, hfac⟩ := hf

  obtain ⟨V, hV1, hV⟩ :=
    IsLocallyConstant.exists_nhds_one_forall_apply_mul_mul_eq_of_hasCompactSupport hff.1 hff.2
  have h1V : (1 : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) ∈ V := mem_of_mem_nhds hV1

  set V' : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) := V ∩ (fun u => u⁻¹) ⁻¹' V with hV'
  have hV'1 : V' ∈ 𝓝 (1 : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) := by
    refine Filter.inter_mem hV1 ?_
    exact continuous_inv.continuousAt.preimage_mem_nhds (by simpa using hV1)

  have hleftf : ∀ k : AdelicGL2 (𝓞 F) F, glArch (𝓞 F) F k = 1 → glFin (𝓞 F) F k ∈ V' →
      ∀ y : AdelicGL2 (𝓞 F) F, f (k⁻¹ * y) = f y := by
    intro k hk hkV y
    rw [hfac, hfac y, map_mul, map_mul, map_inv, map_inv, hk, inv_one, one_mul]
    congr 1
    have := hV (glFin (𝓞 F) F k)⁻¹ hkV.2 1 h1V (glFin (𝓞 F) F y)
    simpa using this

  letI := AdelicHaar.glBorel (Fin 2) (𝓞 F) F
  haveI := AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 F) F
  haveI := AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F

  have hinv : ∀ k : AdelicGL2 (𝓞 F) F, glArch (𝓞 F) F k = 1 → glFin (𝓞 F) F k ∈ V' →
      ∀ g : AdelicGL2 (𝓞 F) F, rightConv F φ f (g * k) = rightConv F φ f g := by
    intro k hk hkV g
    show (∫ x, φ (g * k * x) * f x ∂(AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F)) =
      ∫ x, φ (g * x) * f x ∂(AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F)
    have h := integral_mul_left_eq_self (μ := AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F)
      (fun x => φ (g * k * x) * f x) k⁻¹
    rw [← h]
    congr 1
    funext x
    rw [hleftf k hk hkV x]
    simp only [mul_assoc, mul_inv_cancel_left]

  rw [isKfSmooth_iff, FLT.SmoothVectors.isSmoothVector_iff_isOpen_stabilizer]
  apply Subgroup.isOpen_of_mem_nhds (g := 1)
  have hcont : Continuous fun k : ↥(finiteAdelicGL2Subgroup F) => glFin (𝓞 F) F (k : AdelicGL2 (𝓞 F) F) :=
    (continuous_glFin (𝓞 F) F).comp continuous_subtype_val
  have hW : (fun k : ↥(finiteAdelicGL2Subgroup F) => glFin (𝓞 F) F (k : AdelicGL2 (𝓞 F) F)) ⁻¹' V' ∈
      𝓝 (1 : ↥(finiteAdelicGL2Subgroup F)) :=
    hcont.continuousAt.preimage_mem_nhds (by simpa using hV'1)
  refine Filter.mem_of_superset hW ?_
  intro k hk
  simp only [SetLike.mem_coe, MulAction.mem_stabilizer_iff]
  refine FLT.SmoothVectors.RightTranslationFn.ext fun g => ?_
  rw [Subgroup.smul_def, FLT.SmoothVectors.RightTranslationFn.toFun_smul,
    FLT.SmoothVectors.RightTranslationFn.toFun_mk]
  exact hinv k ((mem_finiteAdelicGL2Subgroup_iff F k).mp k.2) hk g

end S_AutomorphicForm_isKfSmooth_rightConv
end P2MW
export P2MW.S_AutomorphicForm_isKfSmooth_rightConv (solution)
