-- Prove2me | solution 1 for AutomorphicForm.CuspidalConstituent.IsCuspConstituent.finiteDimensional_of_forall_rightTranslate_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/aef25fb2-0731-5f24-8e59-61116e35e992

import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_DirichletCharacter_DirichletIdeleChar
import Definitions.Def_AutomorphicForm_FnTwist
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Theorems.Thm_AutomorphicForm_finiteDimensional_inf_levelInvariantSubmodule_inf_archCutSubmodule_of_isCuspConstituent
import Theorems.Thm_AutomorphicForm_SiegelCovering_coversModCentre_productionPinsGeneral_D_rat
import Theorems.Thm_AutomorphicForm_mul_dirichletIdeleChar_det_rightTranslate_invariant_levelOne_sq
import Theorems.Thm_AutomorphicForm_CuspidalConstituent_isCuspConstituent_twistedCentralChar_span_image_fnTwist
import Theorems.Thm_DirichletCharacter_isFiniteOrderHeckeChar_dirichletIdeleChar
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_CuspidalConstituent_IsCuspConstituent_finiteDimensional_of_forall_rightTranslate_eq
p2m_attr_erase "instance" "RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instCountableOfNumberField_definitions AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply AutomorphicForm.whittakerCoefficient_zero NumberField.StandardAddChar.ratArchLine_apply"
p2m_attr_erase "simp" "NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply AutomorphicForm.CuspidalSpectrum.fdPins_μ AutomorphicForm.CuspidalSpectrum.fdPins_nS AutomorphicForm.CuspidalSpectrum.fdPins_ν AutomorphicForm.CuspidalSpectrum.fdPins_gen AutomorphicForm.CuspidalSpectrum.fdPins_U AutomorphicForm.CuspidalSpectrum.fdPins_D AutomorphicForm.CuspidalSpectrum.fdPins_Z AutomorphicForm.CuspidalSpectrum.mem_detNormSlab AutomorphicForm.CuspidalSpectrum.fdPins_eq AutomorphicForm.CuspidalSpectrum.fdPins_mS LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero"

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain in

private abbrev AfQ := FiniteAdeleRing (𝓞 ℚ) ℚ

namespace AutomorphicForm
p2m_export "AutomorphicForm" "CuspidalConstituent.rightTranslate CuspidalConstituent.IsCuspConstituent typeSubmodule mem_typeSubmodule_of_isRightEquivariant comp_mul_mem_typeSubmodule_of_commute rowIsometryInclAt₀ rowIsometryInclAt₀_apply archTypeSubmoduleAt ArchTypeFamily archCutSubmodule mem_archCutSubmodule_iff classRepTranslates productionPinsGeneral CarrierPins AdelicGL2 finiteAdelicGL2Subgroup mem_finiteAdelicGL2Subgroup_iff rowIsometrySubgroup₀ mem_rowIsometrySubgroup₀_iff archGLIncl archComponent_archGLIncl_self archComponent_archGLIncl_of_ne adelicArchGLIncl adelicArchGLInclAt glArch_adelicArchGLIncl glFin_adelicArchGLIncl fnTwist fnTwist_apply finiteDimensional_inf_levelInvariantSubmodule_inf_archCutSubmodule_of_isCuspConstituent SiegelCovering.coversModCentre_productionPinsGeneral_D_rat mul_dirichletIdeleChar_det_rightTranslate_invariant_levelOne_sq CuspidalConstituent.isCuspConstituent_twistedCentralChar_span_image_fnTwist"
namespace TorusEigenDecomposition
p2m_open "AutomorphicForm"

section Projections

variable {M : ℕ} [NeZero M] {E : Type*} [AddCommGroup E] [Module ℂ E]

private noncomputable def charProj (T : (ZMod M)ˣ → E →ₗ[ℂ] E) (χ : DirichletCharacter ℂ M) : E →ₗ[ℂ] E :=
  ((M.totient : ℂ)⁻¹) • ∑ a : (ZMod M)ˣ, χ ((a⁻¹ : (ZMod M)ˣ) : ZMod M) • T a

private theorem charProj_apply (T : (ZMod M)ˣ → E →ₗ[ℂ] E) (χ : DirichletCharacter ℂ M) (v : E) :
    charProj T χ v =
      ((M.totient : ℂ)⁻¹) • ∑ a : (ZMod M)ˣ, χ ((a⁻¹ : (ZMod M)ˣ) : ZMod M) • T a v := by
  simp [charProj, LinearMap.sum_apply]

private theorem sum_char_inv_mul (a b : (ZMod M)ˣ) :
    ∑ χ : DirichletCharacter ℂ M, χ ((a⁻¹ : (ZMod M)ˣ) : ZMod M) * χ (b : ZMod M) =
      if a = b then (M.totient : ℂ) else 0 := by
  have h := DirichletCharacter.sum_char_inv_mul_char_eq ℂ (Units.isUnit a) (b : ZMod M)
  simp only [ZMod.inv_coe_unit, Units.val_injective.eq_iff] at h
  exact h

private theorem sum_charProj_apply (T : (ZMod M)ˣ → E →ₗ[ℂ] E) (v : E) (hT1 : T 1 v = v) :
    ∑ χ : DirichletCharacter ℂ M, charProj T χ v = v := by
  have htot : (M.totient : ℂ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos M)).ne'
  calc ∑ χ : DirichletCharacter ℂ M, charProj T χ v
      = ((M.totient : ℂ)⁻¹) • ∑ a : (ZMod M)ˣ,
          (∑ χ : DirichletCharacter ℂ M,
            χ ((a⁻¹ : (ZMod M)ˣ) : ZMod M) * χ ((1 : (ZMod M)ˣ) : ZMod M)) • T a v := by
        simp only [charProj_apply, ← Finset.smul_sum]
        rw [Finset.sum_comm]
        congr 1
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.sum_smul]
        refine Finset.sum_congr rfl fun χ _ => ?_
        rw [Units.val_one, map_one, mul_one]
    _ = ((M.totient : ℂ)⁻¹) • ((M.totient : ℂ) • T 1 v) := by
        congr 1
        rw [Finset.sum_eq_single (1 : (ZMod M)ˣ)]
        · rw [sum_char_inv_mul, if_pos rfl]
        · intro a _ ha
          rw [sum_char_inv_mul, if_neg ha, zero_smul]
        · intro h
          exact absurd (Finset.mem_univ _) h
    _ = v := by rw [smul_smul, inv_mul_cancel₀ htot, one_smul, hT1]

private theorem apply_charProj (T : (ZMod M)ˣ → E →ₗ[ℂ] E) (χ : DirichletCharacter ℂ M) (b : (ZMod M)ˣ)
    (L : E →ₗ[ℂ] E) (v : E) (hstep : ∀ a : (ZMod M)ˣ, L (T a v) = T (b * a) v) :
    L (charProj T χ v) = χ (b : ZMod M) • charProj T χ v := by
  have hbb : χ (b : ZMod M) * χ ((b⁻¹ : (ZMod M)ˣ) : ZMod M) = 1 := by
    rw [← map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, map_one]
  have hre : ∑ a : (ZMod M)ˣ, χ ((a⁻¹ : (ZMod M)ˣ) : ZMod M) • T (b * a) v =
      ∑ a : (ZMod M)ˣ, (χ (b : ZMod M) * χ ((a⁻¹ : (ZMod M)ˣ) : ZMod M)) • T a v := by
    rw [← Equiv.sum_comp (Equiv.mulLeft b)
      (fun a => (χ (b : ZMod M) * χ ((a⁻¹ : (ZMod M)ˣ) : ZMod M)) • T a v)]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [Equiv.coe_mulLeft]
    congr 1
    rw [mul_inv_rev, Units.val_mul, map_mul, mul_left_comm, hbb, mul_one]
  calc L (charProj T χ v)
      = ((M.totient : ℂ)⁻¹) • ∑ a : (ZMod M)ˣ, χ ((a⁻¹ : (ZMod M)ˣ) : ZMod M) • L (T a v) := by
        simp only [charProj_apply, map_smul, map_sum]
    _ = ((M.totient : ℂ)⁻¹) • ∑ a : (ZMod M)ˣ, χ ((a⁻¹ : (ZMod M)ˣ) : ZMod M) • T (b * a) v := by
        simp only [hstep]
    _ = ((M.totient : ℂ)⁻¹) •
          ∑ a : (ZMod M)ˣ, (χ (b : ZMod M) * χ ((a⁻¹ : (ZMod M)ˣ) : ZMod M)) • T a v := by rw [hre]
    _ = χ (b : ZMod M) • charProj T χ v := by
        rw [charProj_apply, smul_comm (χ (b : ZMod M))]
        congr 1
        rw [Finset.smul_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [smul_smul]

end Projections

section Descent

variable {M : ℕ} {E : Type*} [AddCommGroup E] [Module ℂ E] {G : Type*} [Group G]

open Classical in

private noncomputable def residueLift (r : G →* (ZMod M)ˣ) (a : (ZMod M)ˣ) : G :=
  if h : ∃ g, r g = a then h.choose else 1

private theorem apply_residueLift (r : G →* (ZMod M)ˣ) {a : (ZMod M)ˣ} (h : ∃ g, r g = a) :
    r (residueLift r a) = a := by
  unfold residueLift
  rw [dif_pos h]
  exact h.choose_spec

open Classical in

private noncomputable def descendedOp (T : G →* Module.End ℂ E) (r : G →* (ZMod M)ˣ) (a : (ZMod M)ˣ) :
    E →ₗ[ℂ] E :=
  if ∃ g, r g = a then T (residueLift r a) else 0

variable (T : G →* Module.End ℂ E) (r : G →* (ZMod M)ˣ) (S : Submodule ℂ E)

private theorem descendedOp_apply_mem (hS : ∀ g, ∀ w ∈ S, T g w ∈ S) (a : (ZMod M)ˣ) {w : E} (hw : w ∈ S) :
    descendedOp T r a w ∈ S := by
  unfold descendedOp
  split_ifs with h
  · exact hS _ w hw
  · rw [LinearMap.zero_apply]
    exact S.zero_mem

private theorem descendedOp_one_apply (hker : ∀ g, r g = 1 → ∀ w ∈ S, T g w = w) {w : E} (hw : w ∈ S) :
    descendedOp T r 1 w = w := by
  have h : ∃ g, r g = 1 := ⟨1, map_one r⟩
  unfold descendedOp
  rw [if_pos h]
  exact hker _ (apply_residueLift r h) w hw

private theorem apply_descendedOp (hker : ∀ g, r g = 1 → ∀ w ∈ S, T g w = w)
    (g : G) (a : (ZMod M)ˣ) {w : E} (hw : w ∈ S) :
    T g (descendedOp T r a w) = descendedOp T r (r g * a) w := by
  unfold descendedOp
  by_cases h : ∃ g', r g' = a
  · have h' : ∃ g', r g' = r g * a := by
      obtain ⟨g', hg'⟩ := h
      exact ⟨g * g', by rw [map_mul, hg']⟩
    have hk : r ((residueLift r (r g * a))⁻¹ * (g * residueLift r a)) = 1 := by
      rw [map_mul, map_mul, map_inv, apply_residueLift r h, apply_residueLift r h', inv_mul_cancel]
    rw [if_pos h, if_pos h']
    calc T g (T (residueLift r a) w)
        = T (g * residueLift r a) w := by
          rw [map_mul]
          rfl
      _ = T (residueLift r (r g * a) * ((residueLift r (r g * a))⁻¹ * (g * residueLift r a))) w := by
          rw [mul_inv_cancel_left]
      _ = T (residueLift r (r g * a))
            (T ((residueLift r (r g * a))⁻¹ * (g * residueLift r a)) w) := by
          rw [map_mul]
          rfl
      _ = T (residueLift r (r g * a)) w := by rw [hker _ hk w hw]
  · have h' : ¬ ∃ g', r g' = r g * a := by
      rintro ⟨g', hg'⟩
      exact h ⟨g⁻¹ * g', by rw [map_mul, map_inv, hg', inv_mul_cancel_left]⟩
    rw [if_neg h, if_neg h']
    simp only [LinearMap.zero_apply, map_zero]

private def eigenSubmoduleOf (χ : DirichletCharacter ℂ M) : Submodule ℂ E where
  carrier := {w | w ∈ S ∧ ∀ g : G, T g w = χ ((r g : (ZMod M)ˣ) : ZMod M) • w}
  add_mem' := fun {x y} hx hy => ⟨S.add_mem hx.1 hy.1, fun g => by rw [map_add, hx.2 g, hy.2 g, smul_add]⟩
  zero_mem' := ⟨S.zero_mem, fun g => by rw [map_zero, smul_zero]⟩
  smul_mem' := fun c {x} hx => ⟨S.smul_mem c hx.1, fun g => by rw [map_smul, hx.2 g, smul_comm]⟩

private theorem mem_eigenSubmoduleOf_iff (χ : DirichletCharacter ℂ M) (w : E) :
    w ∈ eigenSubmoduleOf T r S χ ↔ w ∈ S ∧ ∀ g : G, T g w = χ ((r g : (ZMod M)ˣ) : ZMod M) • w :=
  Iff.rfl

private theorem eigenSubmoduleOf_le (χ : DirichletCharacter ℂ M) : eigenSubmoduleOf T r S χ ≤ S :=
  fun _ hw => hw.1

variable [NeZero M]

private theorem charProj_descendedOp_mem (hS : ∀ g, ∀ w ∈ S, T g w ∈ S)
    (hker : ∀ g, r g = 1 → ∀ w ∈ S, T g w = w) (χ : DirichletCharacter ℂ M) {v : E} (hv : v ∈ S) :
    charProj (descendedOp T r) χ v ∈ eigenSubmoduleOf T r S χ := by
  refine ⟨?_, fun g => apply_charProj (descendedOp T r) χ (r g) (T g) v
    fun a => apply_descendedOp T r S hker g a hv⟩
  rw [charProj_apply]
  exact S.smul_mem _ (S.sum_mem fun a _ => S.smul_mem _ (descendedOp_apply_mem T r S hS a hv))

private theorem mem_iSup_eigenSubmoduleOf (hS : ∀ g, ∀ w ∈ S, T g w ∈ S)
    (hker : ∀ g, r g = 1 → ∀ w ∈ S, T g w = w) {v : E} (hv : v ∈ S) :
    v ∈ ⨆ χ : DirichletCharacter ℂ M, eigenSubmoduleOf T r S χ := by
  rw [← sum_charProj_apply (descendedOp T r) v (descendedOp_one_apply T r S hker hv)]
  exact Submodule.sum_mem _ fun χ _ =>
    Submodule.mem_iSup_of_mem χ (charProj_descendedOp_mem T r S hS hker χ hv)

private theorem iSup_eigenSubmoduleOf_eq (hS : ∀ g, ∀ w ∈ S, T g w ∈ S)
    (hker : ∀ g, r g = 1 → ∀ w ∈ S, T g w = w) :
    ⨆ χ : DirichletCharacter ℂ M, eigenSubmoduleOf T r S χ = S :=
  le_antisymm (iSup_le fun χ => eigenSubmoduleOf_le T r S χ)
    fun _ hv => mem_iSup_eigenSubmoduleOf T r S hS hker hv

private theorem finiteDimensional_of_eigenSubmoduleOf (hS : ∀ g, ∀ w ∈ S, T g w ∈ S)
    (hker : ∀ g, r g = 1 → ∀ w ∈ S, T g w = w)
    (hfin : ∀ χ : DirichletCharacter ℂ M, FiniteDimensional ℂ (eigenSubmoduleOf T r S χ)) :
    FiniteDimensional ℂ S := by
  rw [← iSup_eigenSubmoduleOf_eq T r S hS hker]
  exact Submodule.finiteDimensional_iSup _

end Descent

end AutomorphicForm.TorusEigenDecomposition

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField.AdelicLevel RatIdele
open Rat.HeightOneSpectrum

namespace AutomorphicForm
p2m_export "AutomorphicForm" "CuspidalConstituent.rightTranslate CuspidalConstituent.IsCuspConstituent typeSubmodule mem_typeSubmodule_of_isRightEquivariant comp_mul_mem_typeSubmodule_of_commute rowIsometryInclAt₀ rowIsometryInclAt₀_apply archTypeSubmoduleAt ArchTypeFamily archCutSubmodule mem_archCutSubmodule_iff classRepTranslates productionPinsGeneral CarrierPins AdelicGL2 finiteAdelicGL2Subgroup mem_finiteAdelicGL2Subgroup_iff rowIsometrySubgroup₀ mem_rowIsometrySubgroup₀_iff archGLIncl archComponent_archGLIncl_self archComponent_archGLIncl_of_ne adelicArchGLIncl adelicArchGLInclAt glArch_adelicArchGLIncl glFin_adelicArchGLIncl fnTwist fnTwist_apply finiteDimensional_inf_levelInvariantSubmodule_inf_archCutSubmodule_of_isCuspConstituent SiegelCovering.coversModCentre_productionPinsGeneral_D_rat mul_dirichletIdeleChar_det_rightTranslate_invariant_levelOne_sq CuspidalConstituent.isCuspConstituent_twistedCentralChar_span_image_fnTwist"
namespace ResidueCongruence
p2m_open "AutomorphicForm"

private theorem ρ_finIncl_of_forall_valued_eq_one (u : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hu : ∀ v : HeightOneSpectrum (𝓞 ℚ), Valued.v ((u : FiniteAdeleRing (𝓞 ℚ) ℚ) v) = 1) :
    ρ (Units.map (finIncl (𝓞 ℚ) ℚ) u) = 1 := by
  refine ρ_eq_of_isNormalizer ⟨fun w => ?_, ?_⟩
  · rw [Units.coe_map, finIncl_apply_snd, map_one]
    exact hu w
  · rw [archCoord_finIncl, one_mul, Rat.cast_one]
    exact one_pos

private theorem unitAt_finIncl_of_forall_valued_eq_one (u : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hu : ∀ v : HeightOneSpectrum (𝓞 ℚ), Valued.v ((u : FiniteAdeleRing (𝓞 ℚ) ℚ) v) = 1)
    (v : HeightOneSpectrum (𝓞 ℚ)) :
    unitAt v (Units.map (finIncl (𝓞 ℚ) ℚ) u) = (u : FiniteAdeleRing (𝓞 ℚ) ℚ) v := by
  unfold unitAt
  rw [ρ_finIncl_of_forall_valued_eq_one u hu, map_one, inv_one, mul_one, Units.coe_map,
    finIncl_apply_snd]

private theorem valued_natCast_eq_valued_pow (M : ℕ) [NeZero M] (p : ℕ) [hp : Fact p.Prime]
    (W : HeightOneSpectrum (𝓞 ℚ)) (hWp : natGenerator W = p) :
    Valued.v ((M : ℕ) : W.adicCompletion ℚ) =
      Valued.v (((p : ℕ) : W.adicCompletion ℚ) ^ M.factorization p) := by
  have hcompl : Valued.v ((M / p ^ M.factorization p : ℕ) : W.adicCompletion ℚ) = 1 := by
    rw [← map_natCast (algebraMap ℚ (W.adicCompletion ℚ)), valued_algebraMap_rat,
      valuation_natCast_of_not_dvd W ?_]
    rw [hWp]
    exact Nat.not_dvd_ordCompl hp.out (NeZero.ne M)
  conv_lhs => rw [← Nat.ordProj_mul_ordCompl_eq_self M p]
  rw [Nat.cast_mul, map_mul, hcompl, mul_one, Nat.cast_pow]

private theorem valued_unitAt_sub_one_le (M : ℕ) [NeZero M] {x : (AdeleRing (𝓞 ℚ) ℚ)ˣ}
    (hx : unitResidue M x = 1) (p : ℕ) [hp : Fact p.Prime] (hpM : p ∣ M)
    (W : HeightOneSpectrum (𝓞 ℚ)) (hWp : natGenerator W = p)
    (e : W.adicCompletionIntegers ℚ ≃+* ℤ_[p]) (he : e (unitIntAt W x) = unitPadicAt p x) :
    Valued.v (unitAt W x - 1) ≤ Valued.v ((M : ℕ) : W.adicCompletion ℚ) := by
  have hmem : p ∈ M.primeFactors := Nat.mem_primeFactors.mpr ⟨hp.out, hpM, NeZero.ne M⟩
  have h1 : unitResidues M x ⟨p, hmem⟩ = 1 := by
    have h := congrFun (equivPi_unitResidue M x) ⟨p, hmem⟩
    rw [hx, map_one, Pi.one_apply] at h
    exact h.symm
  have h2 : PadicInt.toZModPow (M.factorization p) (unitPadicAt p x) = 1 := h1
  have h3 : unitPadicAt p x - 1 ∈ Ideal.span {(p : ℤ_[p]) ^ M.factorization p} := by
    rw [← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, map_one, h2, sub_self]
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp h3
  have h4 : unitIntAt W x = e.symm c * ((p : ℕ) : W.adicCompletionIntegers ℚ) ^ M.factorization p + 1 := by
    have h' : unitIntAt W x = e.symm (unitPadicAt p x) := by
      rw [← he, RingEquiv.symm_apply_apply]
    have h'' : unitPadicAt p x = c * (p : ℤ_[p]) ^ M.factorization p + 1 := by
      rw [hc, sub_add_cancel]
    rw [h', h'', map_add, map_mul, map_pow, map_natCast, map_one]
  have h5 : unitAt W x - 1 =
      (e.symm c : W.adicCompletion ℚ) * ((p : ℕ) : W.adicCompletion ℚ) ^ M.factorization p := by
    rw [← coe_unitIntAt, h4, AddMemClass.coe_add, MulMemClass.coe_mul, SubmonoidClass.coe_pow,
      SubringClass.coe_natCast, OneMemClass.coe_one, add_sub_cancel_right]
  have hint : Valued.v (e.symm c : W.adicCompletion ℚ) ≤ 1 :=
    (mem_adicCompletionIntegers _ _ _).mp (SetLike.coe_mem _)
  calc Valued.v (unitAt W x - 1)
      = Valued.v (e.symm c : W.adicCompletion ℚ) *
          Valued.v (((p : ℕ) : W.adicCompletion ℚ) ^ M.factorization p) := by
        rw [h5, map_mul]
    _ ≤ 1 * Valued.v (((p : ℕ) : W.adicCompletion ℚ) ^ M.factorization p) := by gcongr
    _ = Valued.v ((M : ℕ) : W.adicCompletion ℚ) := by
        rw [one_mul, valued_natCast_eq_valued_pow M p W hWp]

private theorem valued_sub_one_le (M : ℕ) [NeZero M] (u : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hu : ∀ v : HeightOneSpectrum (𝓞 ℚ), Valued.v ((u : FiniteAdeleRing (𝓞 ℚ) ℚ) v) = 1)
    (hres : unitResidue M (Units.map (finIncl (𝓞 ℚ) ℚ) u) = 1) (v : HeightOneSpectrum (𝓞 ℚ)) :
    Valued.v ((u : FiniteAdeleRing (𝓞 ℚ) ℚ) v - 1) ≤ Valued.v ((M : ℕ) : v.adicCompletion ℚ) := by
  by_cases hv : natGenerator v ∣ M
  · haveI hp : Fact (natGenerator v).Prime := ⟨prime_natGenerator v⟩
    have hvw : (primesEquiv (R := 𝓞 ℚ)).symm ⟨natGenerator v, hp.out⟩ = v :=
      eq_of_natGenerator_eq (natGenerator_primesEquiv_symm _)
    have hcong := valued_unitAt_sub_one_le M hres (natGenerator v) hv
      ((primesEquiv (R := 𝓞 ℚ)).symm ⟨natGenerator v, hp.out⟩)
      (natGenerator_primesEquiv_symm ⟨natGenerator v, hp.out⟩)
      (PadicInt.adicCompletionIntegersEquiv (𝓞 ℚ) ⟨natGenerator v, hp.out⟩).symm.toAlgEquiv.toRingEquiv
      rfl
    rw [hvw, unitAt_finIncl_of_forall_valued_eq_one u hu v] at hcong
    exact hcong
  · rw [← map_natCast (algebraMap ℚ (v.adicCompletion ℚ)), valued_algebraMap_rat,
      valuation_natCast_of_not_dvd v hv]
    calc Valued.v ((u : FiniteAdeleRing (𝓞 ℚ) ℚ) v - 1)
        ≤ max (Valued.v ((u : FiniteAdeleRing (𝓞 ℚ) ℚ) v)) (Valued.v (1 : v.adicCompletion ℚ)) :=
          Valuation.map_sub _ _ _
      _ = 1 := by rw [hu v, map_one, max_self]

end AutomorphicForm.ResidueCongruence

open NumberField NumberField.AdelicLevel IsDedekindDomain IsDedekindDomain.HeightOneSpectrum AdelicDock
open RatIdele AutomorphicForm.CuspidalConstituent

namespace AutomorphicForm
p2m_export "AutomorphicForm" "CuspidalConstituent.rightTranslate CuspidalConstituent.IsCuspConstituent typeSubmodule mem_typeSubmodule_of_isRightEquivariant comp_mul_mem_typeSubmodule_of_commute rowIsometryInclAt₀ rowIsometryInclAt₀_apply archTypeSubmoduleAt ArchTypeFamily archCutSubmodule mem_archCutSubmodule_iff classRepTranslates productionPinsGeneral CarrierPins AdelicGL2 finiteAdelicGL2Subgroup mem_finiteAdelicGL2Subgroup_iff rowIsometrySubgroup₀ mem_rowIsometrySubgroup₀_iff archGLIncl archComponent_archGLIncl_self archComponent_archGLIncl_of_ne adelicArchGLIncl adelicArchGLInclAt glArch_adelicArchGLIncl glFin_adelicArchGLIncl fnTwist fnTwist_apply finiteDimensional_inf_levelInvariantSubmodule_inf_archCutSubmodule_of_isCuspConstituent SiegelCovering.coversModCentre_productionPinsGeneral_D_rat mul_dirichletIdeleChar_det_rightTranslate_invariant_levelOne_sq CuspidalConstituent.isCuspConstituent_twistedCentralChar_span_image_fnTwist"
namespace TorusOnPrincipalFixed
p2m_open "AutomorphicForm"

private theorem commute_of_glArch_eq_one_of_glFin_eq_one {g h : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)}
    (hg : glArch (𝓞 ℚ) ℚ g = 1) (hh : glFin (𝓞 ℚ) ℚ h = 1) : Commute g h := by
  have harch : glArch (𝓞 ℚ) ℚ (g * h) = glArch (𝓞 ℚ) ℚ (h * g) := by
    rw [map_mul, map_mul, hg, one_mul, mul_one]
  have hfin : glFin (𝓞 ℚ) ℚ (g * h) = glFin (𝓞 ℚ) ℚ (h * g) := by
    rw [map_mul, map_mul, hh, one_mul, mul_one]
  refine Units.ext (Matrix.ext fun i j => Prod.ext ?_ ?_)
  · rw [← glArch_apply, ← glArch_apply, harch]
  · rw [← glFin_apply, ← glFin_apply, hfin]

private theorem units_ext_of_parts_eq {g h : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)}
    (harch : glArch (𝓞 ℚ) ℚ g = glArch (𝓞 ℚ) ℚ h) (hfin : glFin (𝓞 ℚ) ℚ g = glFin (𝓞 ℚ) ℚ h) : g = h :=
  Units.ext (Matrix.ext fun i j => Prod.ext (by rw [← glArch_apply, ← glArch_apply, harch])
    (by rw [← glFin_apply, ← glFin_apply, hfin]))

private theorem finEmbed_glFin_of_glArch_eq_one {g : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)} (hg : glArch (𝓞 ℚ) ℚ g = 1) :
    finEmbed (𝓞 ℚ) ℚ (glFin (𝓞 ℚ) ℚ g) = g :=
  units_ext_of_parts_eq (by rw [glArch_finEmbed (R := 𝓞 ℚ) (K := ℚ), hg])
    (glFin_finEmbed (R := 𝓞 ℚ) (K := ℚ) _)

private theorem rightTranslate_mem_archCutSubmodule_of_glArch_eq_one (tys : ArchTypeFamily ℚ)
    {φ : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ) → ℂ} (hφ : φ ∈ archCutSubmodule ℚ tys)
    {g : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)} (hg : glArch (𝓞 ℚ) ℚ g = 1) :
    rightTranslate ℚ g φ ∈ archCutSubmodule ℚ tys := by
  rw [mem_archCutSubmodule_iff] at hφ ⊢
  intro w
  have hle : ∀ i : Fin (tys.card w),
      (archTypeSubmoduleAt ℚ w (tys.rep w i)).map (rightRegular ℚ g) ≤
        archTypeSubmoduleAt ℚ w (tys.rep w i) := by
    intro i f hf
    obtain ⟨f₀, hf₀, rfl⟩ := Submodule.mem_map.mp hf
    refine comp_mul_mem_typeSubmodule_of_commute hf₀ _ fun k' => ?_
    rw [rowIsometryInclAt₀_apply]
    exact commute_of_glArch_eq_one_of_glFin_eq_one hg (glFin_adelicArchGLIncl (F := ℚ) _)
  have hmap : (⨆ i, archTypeSubmoduleAt ℚ w (tys.rep w i)).map (rightRegular ℚ g) ≤
      ⨆ i, archTypeSubmoduleAt ℚ w (tys.rep w i) := by
    rw [Submodule.map_iSup]
    exact iSup_mono hle
  exact hmap (Submodule.mem_map_of_mem (hφ w))

private def integralUnits : Subgroup AfQˣ where
  carrier := {u | (u : AfQ) ∈ integralFiniteAdeles (𝓞 ℚ) ℚ ∧
    ((u⁻¹ : AfQˣ) : AfQ) ∈ integralFiniteAdeles (𝓞 ℚ) ℚ}
  mul_mem' := fun {a b} ha hb =>
    ⟨fun v => by
      rw [Units.val_mul, coe_mul_apply]
      exact mul_mem (ha.1 v) (hb.1 v),
     fun v => by
      rw [mul_inv_rev, Units.val_mul, coe_mul_apply]
      exact mul_mem (hb.2 v) (ha.2 v)⟩
  one_mem' :=
    ⟨fun v => by
      rw [Units.val_one, coe_one_apply]
      exact one_mem _,
     fun v => by
      rw [inv_one, Units.val_one, coe_one_apply]
      exact one_mem _⟩
  inv_mem' := fun {a} ha => ⟨ha.2, by rw [inv_inv]; exact ha.1⟩

private theorem mem_integralUnits_iff (u : AfQˣ) :
    u ∈ integralUnits ↔ (u : AfQ) ∈ integralFiniteAdeles (𝓞 ℚ) ℚ ∧
      ((u⁻¹ : AfQˣ) : AfQ) ∈ integralFiniteAdeles (𝓞 ℚ) ℚ :=
  Iff.rfl

private theorem valued_eq_one_of_mem_integralUnits {u : AfQˣ} (hu : u ∈ integralUnits)
    (v : HeightOneSpectrum (𝓞 ℚ)) : Valued.v ((u : AfQ) v) = 1 := by
  have h1 : Valued.v ((u : AfQ) v) ≤ 1 := (mem_adicCompletionIntegers _ _ _).mp (hu.1 v)
  have h2 : Valued.v (((u⁻¹ : AfQˣ) : AfQ) v) ≤ 1 := (mem_adicCompletionIntegers _ _ _).mp (hu.2 v)
  have h12 : Valued.v ((u : AfQ) v) * Valued.v (((u⁻¹ : AfQˣ) : AfQ) v) = 1 := by
    rw [← map_mul, ← coe_mul_apply, ← Units.val_mul, mul_inv_cancel, Units.val_one, coe_one_apply,
      map_one]
  refine le_antisymm h1 ?_
  calc (1 : WithZero (Multiplicative ℤ)) = Valued.v ((u : AfQ) v) * Valued.v (((u⁻¹ : AfQˣ) : AfQ) v) :=
        h12.symm
    _ ≤ Valued.v ((u : AfQ) v) * 1 := by gcongr
    _ = Valued.v ((u : AfQ) v) := mul_one _

private def principalFixed (M : ℕ) : Submodule ℂ (GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ) → ℂ) where
  carrier := {φ | ∀ (x : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) (k : GL (Fin 2) AfQ),
    (∀ i j, ((k : Matrix (Fin 2) (Fin 2) AfQ) - 1) i j ∈
      idealBall (𝓞 ℚ) ℚ (Ideal.span {(M : 𝓞 ℚ)})) →
    (∀ i j, (((k⁻¹ : GL (Fin 2) AfQ) : Matrix (Fin 2) (Fin 2) AfQ) - 1) i j ∈
      idealBall (𝓞 ℚ) ℚ (Ideal.span {(M : 𝓞 ℚ)})) →
    φ (x * finEmbed (𝓞 ℚ) ℚ k) = φ x}
  add_mem' := fun {φ ψ} hφ hψ x k hk hk' => by
    rw [Pi.add_apply, Pi.add_apply, hφ x k hk hk', hψ x k hk hk']
  zero_mem' := fun _ _ _ _ => rfl
  smul_mem' := fun c {φ} hφ x k hk hk' => by
    rw [Pi.smul_apply, Pi.smul_apply, hφ x k hk hk']

private theorem coe_diagOne (u : AfQˣ) :
    ((diagOne u : GL (Fin 2) AfQ) : Matrix (Fin 2) (Fin 2) AfQ) = Matrix.diagonal ![(u : AfQ), 1] :=
  Matrix.ext fun i j => diagOne_coe_apply u i j

private theorem conj_apply_00 (u w : AfQˣ) (g : Matrix (Fin 2) (Fin 2) AfQ) :
    ((diagOne u : GL (Fin 2) AfQ) * g * (diagOne w : GL (Fin 2) AfQ)) 0 0 = (u : AfQ) * g 0 0 * (w : AfQ) := by
  simp [coe_diagOne, Matrix.mul_diagonal, Matrix.diagonal_mul]

private theorem conj_apply_01 (u w : AfQˣ) (g : Matrix (Fin 2) (Fin 2) AfQ) :
    ((diagOne u : GL (Fin 2) AfQ) * g * (diagOne w : GL (Fin 2) AfQ)) 0 1 = (u : AfQ) * g 0 1 := by
  simp [coe_diagOne, Matrix.mul_diagonal, Matrix.diagonal_mul]

private theorem conj_apply_10 (u w : AfQˣ) (g : Matrix (Fin 2) (Fin 2) AfQ) :
    ((diagOne u : GL (Fin 2) AfQ) * g * (diagOne w : GL (Fin 2) AfQ)) 1 0 = g 1 0 * (w : AfQ) := by
  simp [coe_diagOne, Matrix.mul_diagonal, Matrix.diagonal_mul]

private theorem conj_apply_11 (u w : AfQˣ) (g : Matrix (Fin 2) (Fin 2) AfQ) :
    ((diagOne u : GL (Fin 2) AfQ) * g * (diagOne w : GL (Fin 2) AfQ)) 1 1 = g 1 1 := by
  simp [coe_diagOne, Matrix.mul_diagonal, Matrix.diagonal_mul]

private theorem forall_fin_two {P : Fin 2 → Fin 2 → Prop} (h00 : P 0 0) (h01 : P 0 1) (h10 : P 1 0)
    (h11 : P 1 1) : ∀ i j, P i j := by
  intro i j
  fin_cases i <;> fin_cases j <;> assumption

private theorem idealBall_mul_left_of_valued_le {N : Ideal (𝓞 ℚ)} {a y : AfQ}
    (ha : ∀ v : HeightOneSpectrum (𝓞 ℚ), Valued.v (a v) ≤ 1) (hy : y ∈ idealBall (𝓞 ℚ) ℚ N) :
    a * y ∈ idealBall (𝓞 ℚ) ℚ N := fun v => by
  rw [coe_mul_apply, map_mul]
  calc Valued.v (a v) * Valued.v (y v) ≤ 1 * idealBound (𝓞 ℚ) N v := by
        have h1 := ha v
        have h2 := hy v
        gcongr
    _ = idealBound (𝓞 ℚ) N v := one_mul _

private theorem idealBall_mul_right_of_valued_le {N : Ideal (𝓞 ℚ)} {a y : AfQ}
    (ha : ∀ v : HeightOneSpectrum (𝓞 ℚ), Valued.v (a v) ≤ 1) (hy : y ∈ idealBall (𝓞 ℚ) ℚ N) :
    y * a ∈ idealBall (𝓞 ℚ) ℚ N := by
  rw [mul_comm]
  exact idealBall_mul_left_of_valued_le ha hy

private theorem conj_sub_one_apply_mem (M : ℕ) {u : AfQˣ} (hu : u ∈ integralUnits) {g : GL (Fin 2) AfQ}
    (hg : ∀ i j, ((g : Matrix (Fin 2) (Fin 2) AfQ) - 1) i j ∈ idealBall (𝓞 ℚ) ℚ (Ideal.span {(M : 𝓞 ℚ)})) :
    ∀ i j, ((((diagOne u)⁻¹ * g * diagOne u : GL (Fin 2) AfQ) : Matrix (Fin 2) (Fin 2) AfQ) - 1) i j ∈
      idealBall (𝓞 ℚ) ℚ (Ideal.span {(M : 𝓞 ℚ)}) := by
  have hval : ∀ v, Valued.v ((u : AfQ) v) ≤ 1 := fun v => (valued_eq_one_of_mem_integralUnits hu v).le
  have hvalinv : ∀ v, Valued.v (((u⁻¹ : AfQˣ) : AfQ) v) ≤ 1 := fun v =>
    (valued_eq_one_of_mem_integralUnits (inv_mem hu) v).le
  have hmat : (((diagOne u)⁻¹ * g * diagOne u : GL (Fin 2) AfQ) : Matrix (Fin 2) (Fin 2) AfQ) =
      (diagOne u⁻¹ : GL (Fin 2) AfQ) * (g : Matrix (Fin 2) (Fin 2) AfQ) * (diagOne u : GL (Fin 2) AfQ) := by
    rw [← map_inv, Units.val_mul, Units.val_mul]
  have h00 := hg 0 0
  have h01 := hg 0 1
  have h10 := hg 1 0
  have h11 := hg 1 1
  rw [Matrix.sub_apply, Matrix.one_apply_ne (by decide), sub_zero] at h01
  rw [Matrix.sub_apply, Matrix.one_apply_ne (by decide), sub_zero] at h10
  refine forall_fin_two ?_ ?_ ?_ ?_
  · rw [Matrix.sub_apply, hmat, conj_apply_00, mul_right_comm, Units.inv_mul, one_mul, ← Matrix.sub_apply]
    exact h00
  · rw [Matrix.sub_apply, hmat, conj_apply_01, Matrix.one_apply_ne (by decide), sub_zero]
    exact idealBall_mul_left_of_valued_le hvalinv h01
  · rw [Matrix.sub_apply, hmat, conj_apply_10, Matrix.one_apply_ne (by decide), sub_zero]
    exact idealBall_mul_right_of_valued_le hval h10
  · rw [Matrix.sub_apply, hmat, conj_apply_11, ← Matrix.sub_apply]
    exact h11

private theorem conj_inv_eq {G : Type*} [Group G] (d g : G) : (d⁻¹ * g * d)⁻¹ = d⁻¹ * g⁻¹ * d := by
  rw [mul_inv_rev, mul_inv_rev, inv_inv, mul_assoc]

private theorem rightTranslate_diagOne_mem_principalFixed (M : ℕ) {u : AfQˣ} (hu : u ∈ integralUnits)
    {φ : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ) → ℂ} (hφ : φ ∈ principalFixed M) :
    rightTranslate ℚ (finEmbed (𝓞 ℚ) ℚ (diagOne u)) φ ∈ principalFixed M := by
  intro x k hk hk'
  show φ (x * finEmbed (𝓞 ℚ) ℚ k * finEmbed (𝓞 ℚ) ℚ (diagOne u)) =
    φ (x * finEmbed (𝓞 ℚ) ℚ (diagOne u))
  have h := hφ (x * finEmbed (𝓞 ℚ) ℚ (diagOne u)) ((diagOne u)⁻¹ * k * diagOne u)
    (conj_sub_one_apply_mem M hu hk) (by rw [conj_inv_eq]; exact conj_sub_one_apply_mem M hu hk')
  rw [map_mul, map_mul, map_inv, ← mul_assoc, ← mul_assoc, mul_inv_cancel_right] at h
  exact h

private theorem det_finEmbed (g : GL (Fin 2) AfQ) :
    Matrix.GeneralLinearGroup.det (finEmbed (𝓞 ℚ) ℚ g) =
      Units.map (finIncl (𝓞 ℚ) ℚ) (Matrix.GeneralLinearGroup.det g) := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, Units.coe_map, Matrix.GeneralLinearGroup.val_det_apply,
    coe_finEmbed]
  refine Prod.ext ?_ ?_
  · show adeleArch (𝓞 ℚ) ℚ (Matrix.det (finMat (𝓞 ℚ) ℚ g)) =
      (finIncl (𝓞 ℚ) ℚ (Matrix.det (g : Matrix (Fin 2) (Fin 2) AfQ))).1
    rw [RingHom.map_det, mapMatrix_arch_finMat, Matrix.det_one, finIncl_apply_fst]
  · show adeleFin (𝓞 ℚ) ℚ (Matrix.det (finMat (𝓞 ℚ) ℚ g)) =
      (finIncl (𝓞 ℚ) ℚ (Matrix.det (g : Matrix (Fin 2) (Fin 2) AfQ))).2
    rw [RingHom.map_det, mapMatrix_fin_finMat, finIncl_apply_snd]

private theorem det_diagOne (u : AfQˣ) : Matrix.GeneralLinearGroup.det (diagOne u) = u := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, coe_diagOne, Matrix.det_diagonal, Fin.prod_univ_two]
  simp

private theorem valued_natCast_eq_idealBound (M : ℕ) [NeZero M] (v : HeightOneSpectrum (𝓞 ℚ)) :
    Valued.v ((M : ℕ) : v.adicCompletion ℚ) = idealBound (𝓞 ℚ) (Ideal.span {(M : 𝓞 ℚ)}) v := by
  have hM : (M : 𝓞 ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne M)
  have hN : Ideal.span {(M : 𝓞 ℚ)} ≠ (⊥ : Ideal (𝓞 ℚ)) := by rwa [Ne, Ideal.span_singleton_eq_bot]
  rw [← map_natCast (algebraMap ℚ (v.adicCompletion ℚ)), valued_algebraMap_rat,
    ← map_natCast (algebraMap (𝓞 ℚ) ℚ) M, HeightOneSpectrum.valuation_of_algebraMap,
    idealBound_of_ne_bot hN, HeightOneSpectrum.intValuation_if_neg _ hM]

private theorem diagOne_sub_one_apply_mem (M : ℕ) [NeZero M] {u : AfQˣ} (hu : u ∈ integralUnits)
    (hres : unitResidue M (Units.map (finIncl (𝓞 ℚ) ℚ) u) = 1) :
    ∀ i j, (((diagOne u : GL (Fin 2) AfQ) : Matrix (Fin 2) (Fin 2) AfQ) - 1) i j ∈
      idealBall (𝓞 ℚ) ℚ (Ideal.span {(M : 𝓞 ℚ)}) := by
  have h00 : (u : AfQ) - 1 ∈ idealBall (𝓞 ℚ) ℚ (Ideal.span {(M : 𝓞 ℚ)}) := fun v => by
    rw [coe_sub_apply, coe_one_apply, ← valued_natCast_eq_idealBound M v]
    exact ResidueCongruence.valued_sub_one_le M u (valued_eq_one_of_mem_integralUnits hu) hres v
  refine forall_fin_two ?_ ?_ ?_ ?_
  · rw [Matrix.sub_apply, coe_diagOne, Matrix.diagonal_apply_eq, Matrix.cons_val_zero, Matrix.one_apply_eq]
    exact h00
  · rw [Matrix.sub_apply, coe_diagOne, Matrix.diagonal_apply_ne _ (by decide),
      Matrix.one_apply_ne (by decide), sub_zero]
    exact zero_mem_idealBall _
  · rw [Matrix.sub_apply, coe_diagOne, Matrix.diagonal_apply_ne _ (by decide),
      Matrix.one_apply_ne (by decide), sub_zero]
    exact zero_mem_idealBall _
  · rw [Matrix.sub_apply, coe_diagOne, Matrix.diagonal_apply_eq, Matrix.cons_val_one, Matrix.cons_val_zero,
      Matrix.one_apply_eq, sub_self]
    exact zero_mem_idealBall _

private theorem rightTranslate_diagOne_eq_of_unitResidue_eq_one (M : ℕ) [NeZero M] {u : AfQˣ}
    (hu : u ∈ integralUnits) (hres : unitResidue M (Units.map (finIncl (𝓞 ℚ) ℚ) u) = 1)
    (hresinv : unitResidue M (Units.map (finIncl (𝓞 ℚ) ℚ) u⁻¹) = 1)
    {φ : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ) → ℂ} (hφ : φ ∈ principalFixed M) :
    rightTranslate ℚ (finEmbed (𝓞 ℚ) ℚ (diagOne u)) φ = φ := by
  funext x
  exact hφ x (diagOne u) (diagOne_sub_one_apply_mem M hu hres)
    (by rw [← map_inv]; exact diagOne_sub_one_apply_mem M (inv_mem hu) hresinv)

private def torusOp : integralUnits →* Module.End ℂ (GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ) → ℂ) :=
  ((rightRegular ℚ).comp ((finEmbed (𝓞 ℚ) ℚ).comp diagOne)).comp integralUnits.subtype

private theorem torusOp_apply (u : integralUnits) (φ : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ) → ℂ) :
    torusOp u φ = rightTranslate ℚ (finEmbed (𝓞 ℚ) ℚ (diagOne (u : AfQˣ))) φ :=
  rfl

private def residueHom (M : ℕ) [NeZero M] : integralUnits →* (ZMod M)ˣ :=
  (((unitResidue M).comp
    ((Matrix.GeneralLinearGroup.det : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ) →* (AdeleRing (𝓞 ℚ) ℚ)ˣ).comp
      ((finEmbed (𝓞 ℚ) ℚ).comp diagOne))).comp integralUnits.subtype).toHomUnits

private theorem coe_residueHom (M : ℕ) [NeZero M] (u : integralUnits) :
    (residueHom M u : ZMod M) =
      unitResidue M (Matrix.GeneralLinearGroup.det (finEmbed (𝓞 ℚ) ℚ (diagOne (u : AfQˣ)))) :=
  rfl

private theorem coe_residueHom_eq_unitResidue_map (M : ℕ) [NeZero M] (u : integralUnits) :
    (residueHom M u : ZMod M) = unitResidue M (Units.map (finIncl (𝓞 ℚ) ℚ) (u : AfQˣ)) := by
  rw [coe_residueHom, det_finEmbed, det_diagOne]

private theorem torusOp_apply_mem {pins : CarrierPins ℚ} {ξ : pins.Z →* ℂˣ}
    {V : Submodule ℂ (GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ) → ℂ)} (hV : IsCuspSubrep ℚ pins ξ V) (M : ℕ)
    (tys : ArchTypeFamily ℚ) (u : integralUnits) {φ : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ) → ℂ}
    (hφ : φ ∈ V ⊓ principalFixed M ⊓ archCutSubmodule ℚ tys) :
    torusOp u φ ∈ V ⊓ principalFixed M ⊓ archCutSubmodule ℚ tys := by
  rw [Submodule.mem_inf, Submodule.mem_inf] at hφ ⊢
  obtain ⟨⟨hφV, hφF⟩, hφt⟩ := hφ
  rw [torusOp_apply]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · refine hV.rightTranslate_fin_mem _ ?_ φ hφV
    rw [mem_finiteAdelicGL2Subgroup_iff]
    exact glArch_finEmbed (R := 𝓞 ℚ) (K := ℚ) _
  · exact rightTranslate_diagOne_mem_principalFixed M u.2 hφF
  · exact rightTranslate_mem_archCutSubmodule_of_glArch_eq_one tys hφt
      (glArch_finEmbed (R := 𝓞 ℚ) (K := ℚ) _)

private theorem torusOp_eq_self_of_residueHom_eq_one (M : ℕ) [NeZero M] (u : integralUnits)
    (hu : residueHom M u = 1) {φ : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ) → ℂ} (hφ : φ ∈ principalFixed M) :
    torusOp u φ = φ := by
  have hinv : residueHom M u⁻¹ = 1 := by rw [map_inv, hu, inv_one]
  have hres : unitResidue M (Units.map (finIncl (𝓞 ℚ) ℚ) (u : AfQˣ)) = 1 := by
    rw [← coe_residueHom_eq_unitResidue_map, hu, Units.val_one]
  have hresinv : unitResidue M (Units.map (finIncl (𝓞 ℚ) ℚ) (u : AfQˣ)⁻¹) = 1 := by
    rw [← Subgroup.coe_inv, ← coe_residueHom_eq_unitResidue_map, hinv, Units.val_one]
  rw [torusOp_apply]
  exact rightTranslate_diagOne_eq_of_unitResidue_eq_one M u.2 hres hresinv hφ

end AutomorphicForm.TorusOnPrincipalFixed

namespace AutomorphicForm
p2m_export "AutomorphicForm" "CuspidalConstituent.rightTranslate CuspidalConstituent.IsCuspConstituent typeSubmodule mem_typeSubmodule_of_isRightEquivariant comp_mul_mem_typeSubmodule_of_commute rowIsometryInclAt₀ rowIsometryInclAt₀_apply archTypeSubmoduleAt ArchTypeFamily archCutSubmodule mem_archCutSubmodule_iff classRepTranslates productionPinsGeneral CarrierPins AdelicGL2 finiteAdelicGL2Subgroup mem_finiteAdelicGL2Subgroup_iff rowIsometrySubgroup₀ mem_rowIsometrySubgroup₀_iff archGLIncl archComponent_archGLIncl_self archComponent_archGLIncl_of_ne adelicArchGLIncl adelicArchGLInclAt glArch_adelicArchGLIncl glFin_adelicArchGLIncl fnTwist fnTwist_apply finiteDimensional_inf_levelInvariantSubmodule_inf_archCutSubmodule_of_isCuspConstituent SiegelCovering.coversModCentre_productionPinsGeneral_D_rat mul_dirichletIdeleChar_det_rightTranslate_invariant_levelOne_sq CuspidalConstituent.isCuspConstituent_twistedCentralChar_span_image_fnTwist"
namespace PrincipalLevelNhds
p2m_open "AutomorphicForm"

open NumberField NumberField.AdelicLevel IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

variable {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K] [Algebra R K]
  [IsFractionRing R K]

private theorem exists_exp_neg_nat_lt {δ : WithZero (Multiplicative ℤ)} (hδ : δ ≠ 0) :
    ∃ n : ℕ, WithZero.exp (-(n : ℤ)) < δ := by
  refine ⟨(-(WithZero.log δ)).toNat + 1, ?_⟩
  conv_rhs => rw [← WithZero.exp_log hδ]
  rw [WithZero.exp_lt_exp]
  omega

private theorem idealBound_span_singleton {r : R} (hr : r ≠ 0) (v : HeightOneSpectrum R) :
    idealBound R (Ideal.span {r}) v = v.intValuation r := by
  have hN : Ideal.span {r} ≠ (⊥ : Ideal R) := by
    rwa [Ne, Ideal.span_singleton_eq_bot]
  rw [idealBound_of_ne_bot hN, intValuation_if_neg _ hr]

private theorem exists_forall_idealBall_subset_of_isOpen {U : Set (FiniteAdeleRing R K)}
    (hU : IsOpen U) (h0 : (0 : FiniteAdeleRing R K) ∈ U) :
    ∃ A : Ideal R, A ≠ ⊥ ∧ ∀ r ∈ A, r ≠ 0 → idealBall R K (Ideal.span {r}) ⊆ U := by
  classical

  let sM : (Π v : HeightOneSpectrum R, v.adicCompletionIntegers K) → FiniteAdeleRing R K :=
    RestrictedProduct.structureMap (fun v : HeightOneSpectrum R => v.adicCompletion K)
      (fun v : HeightOneSpectrum R => (v.adicCompletionIntegers K : Set (v.adicCompletion K)))
      Filter.cofinite
  have hcont : Continuous sM := RestrictedProduct.isEmbedding_structureMap.continuous

  let z0 : Π v : HeightOneSpectrum R, v.adicCompletionIntegers K := fun v => 0
  have hsM0 : sM z0 = 0 := by
    refine FiniteAdeleRing.ext K (fun v => ?_)
    show (RestrictedProduct.structureMap _ _ _ _) v = (0 : FiniteAdeleRing R K) v
    rw [RestrictedProduct.structureMap_apply, coe_zero_apply]
    rfl

  have hW : IsOpen (sM ⁻¹' U) := hU.preimage hcont
  have hW0 : z0 ∈ sM ⁻¹' U := by
    show sM z0 ∈ U; rwa [hsM0]
  obtain ⟨I, u, hu, hIu⟩ := isOpen_pi_iff.mp hW z0 hW0

  have hcoord : ∀ v ∈ I, ∃ n : ℕ, ∀ z : v.adicCompletionIntegers K,
      Valued.v (z : v.adicCompletion K) ≤ WithZero.exp (-(n : ℤ)) → z ∈ u v := by
    intro v hv
    obtain ⟨huo, hu0⟩ := hu v hv
    obtain ⟨s, hs, hsu⟩ := (mem_nhds_subtype _ (z0 v) _).mp (huo.mem_nhds hu0)
    have hz0 : ((z0 v : v.adicCompletionIntegers K) : v.adicCompletion K) = 0 := rfl
    rw [hz0] at hs
    obtain ⟨γ, hγ⟩ := Valued.mem_nhds_zero.mp hs
    have hγ0 : MonoidWithZeroHom.ValueGroup₀.embedding
        (γ : MonoidWithZeroHom.ValueGroup₀ (MonoidWithZeroHom.ofClass (Valued.v (R := v.adicCompletion K)))) ≠ 0 := by
      intro h
      exact γ.ne_zero (MonoidWithZeroHom.ValueGroup₀.embedding_strictMono.injective
        (h.trans (map_zero _).symm))
    obtain ⟨n, hn⟩ := exists_exp_neg_nat_lt hγ0
    refine ⟨n, fun z hz => hsu ?_⟩
    show (z : v.adicCompletion K) ∈ s
    apply hγ
    show Valued.v.restrict (z : v.adicCompletion K) <
      (γ : MonoidWithZeroHom.ValueGroup₀ (MonoidWithZeroHom.ofClass (Valued.v (R := v.adicCompletion K))))
    rw [Valuation.restrict_lt_iff_lt_embedding]
    exact lt_of_le_of_lt hz hn
  choose! e he using hcoord

  set A : Ideal R := ∏ v ∈ I, v.asIdeal ^ e v with hA
  have hA0 : A ≠ ⊥ := by
    rw [hA, ← Ideal.zero_eq_bot]
    exact Finset.prod_ne_zero_iff.mpr fun v _ => pow_ne_zero _ (by
      rw [Ideal.zero_eq_bot]; exact v.ne_bot)
  refine ⟨A, hA0, fun r hrA hr0 x hx => ?_⟩

  have hxint : x ∈ integralFiniteAdeles R K := idealBall_subset_integralFiniteAdeles _ hx
  let y : Π v : HeightOneSpectrum R, v.adicCompletionIntegers K := fun v => ⟨x v, hxint v⟩
  have hy : sM y = x := by
    refine FiniteAdeleRing.ext K (fun v => ?_)
    show (RestrictedProduct.structureMap _ _ _ _) v = x v
    rw [RestrictedProduct.structureMap_apply]

  have hyI : y ∈ (I : Set (HeightOneSpectrum R)).pi u := by
    intro v hv
    apply he v (Finset.mem_coe.mp hv)
    show Valued.v (x v) ≤ WithZero.exp (-(e v : ℤ))
    refine (hx v).trans ?_
    rw [idealBound_span_singleton hr0]
    have hdvd : v.asIdeal ^ e v ∣ Ideal.span {r} := by
      rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
      have hle : A ≤ v.asIdeal ^ e v := by
        rw [hA]
        exact Ideal.prod_le_inf.trans (Finset.inf_le (Finset.mem_coe.mp hv))
      exact hle hrA
    exact (intValuation_le_pow_iff_dvd v r (e v)).mpr hdvd
  have : sM y ∈ U := hIu hyI
  rwa [hy] at this

end AutomorphicForm.PrincipalLevelNhds

namespace AutomorphicForm
p2m_export "AutomorphicForm" "CuspidalConstituent.rightTranslate CuspidalConstituent.IsCuspConstituent typeSubmodule mem_typeSubmodule_of_isRightEquivariant comp_mul_mem_typeSubmodule_of_commute rowIsometryInclAt₀ rowIsometryInclAt₀_apply archTypeSubmoduleAt ArchTypeFamily archCutSubmodule mem_archCutSubmodule_iff classRepTranslates productionPinsGeneral CarrierPins AdelicGL2 finiteAdelicGL2Subgroup mem_finiteAdelicGL2Subgroup_iff rowIsometrySubgroup₀ mem_rowIsometrySubgroup₀_iff archGLIncl archComponent_archGLIncl_self archComponent_archGLIncl_of_ne adelicArchGLIncl adelicArchGLInclAt glArch_adelicArchGLIncl glFin_adelicArchGLIncl fnTwist fnTwist_apply finiteDimensional_inf_levelInvariantSubmodule_inf_archCutSubmodule_of_isCuspConstituent SiegelCovering.coversModCentre_productionPinsGeneral_D_rat mul_dirichletIdeleChar_det_rightTranslate_invariant_levelOne_sq CuspidalConstituent.isCuspConstituent_twistedCentralChar_span_image_fnTwist"
namespace PrincipalLevelNhds
p2m_open "AutomorphicForm"

open NumberField NumberField.AdelicLevel IsDedekindDomain

private theorem exists_forall_sub_one_mem_idealBall_imp {T : Set (Matrix (Fin 2) (Fin 2) AfQ)}
    (hT : T ∈ nhds (1 : Matrix (Fin 2) (Fin 2) AfQ)) :
    ∃ A : Ideal (𝓞 ℚ), A ≠ ⊥ ∧ ∀ r ∈ A, r ≠ 0 → ∀ m : Matrix (Fin 2) (Fin 2) AfQ,
      (∀ i j, (m - 1) i j ∈ idealBall (𝓞 ℚ) ℚ (Ideal.span {r})) → m ∈ T := by
  classical
  obtain ⟨O, hOT, hO, h1O⟩ := mem_nhds_iff.mp hT
  obtain ⟨I, t, ht, hIt⟩ := isOpen_pi_iff.mp hO (1 : Matrix (Fin 2) (Fin 2) AfQ) h1O

  have hrow : ∀ i : Fin 2, ∃ t' : Fin 2 → Set AfQ,
      (∀ j, IsOpen (t' j) ∧ (1 : Matrix (Fin 2) (Fin 2) AfQ) i j ∈ t' j) ∧
        (Set.univ : Set (Fin 2)).pi t' ⊆ (if i ∈ I then t i else Set.univ) := by
    intro i
    by_cases hi : i ∈ I
    · obtain ⟨J, t', ht', hJt'⟩ := isOpen_pi_iff.mp (ht i hi).1 _ (ht i hi).2
      refine ⟨fun j => if j ∈ J then t' j else Set.univ, fun j => ?_, ?_⟩
      · dsimp only
        by_cases hj : j ∈ J
        · rw [if_pos hj]
          exact ht' j hj
        · rw [if_neg hj]
          exact ⟨isOpen_univ, Set.mem_univ _⟩
      · rw [if_pos hi]
        intro f hf
        apply hJt'
        intro j hj
        have hfj := hf j (Set.mem_univ j)
        dsimp only at hfj
        rw [if_pos (Finset.mem_coe.mp hj)] at hfj
        exact hfj
    · exact ⟨fun _ => Set.univ, fun j => ⟨isOpen_univ, Set.mem_univ _⟩, by rw [if_neg hi]; exact Set.subset_univ _⟩
  choose t' ht' hsub using hrow

  have hentry : ∀ i j : Fin 2, ∃ A : Ideal (𝓞 ℚ), A ≠ ⊥ ∧ ∀ r ∈ A, r ≠ 0 → ∀ y : AfQ,
      y ∈ idealBall (𝓞 ℚ) ℚ (Ideal.span {r}) → (1 : Matrix (Fin 2) (Fin 2) AfQ) i j + y ∈ t' i j := by
    intro i j
    have hopen : IsOpen ((fun y => (1 : Matrix (Fin 2) (Fin 2) AfQ) i j + y) ⁻¹' t' i j) :=
      (ht' i j).1.preimage (continuous_const.add continuous_id)
    have h0 : (0 : AfQ) ∈ (fun y => (1 : Matrix (Fin 2) (Fin 2) AfQ) i j + y) ⁻¹' t' i j := by
      show (1 : Matrix (Fin 2) (Fin 2) AfQ) i j + 0 ∈ t' i j
      rw [add_zero]
      exact (ht' i j).2
    obtain ⟨A, hA, hball⟩ := exists_forall_idealBall_subset_of_isOpen hopen h0
    exact ⟨A, hA, fun r hr hr0 y hy => hball r hr hr0 hy⟩
  choose A hA hAt using hentry
  refine ⟨∏ p : Fin 2 × Fin 2, A p.1 p.2, ?_, fun r hr hr0 m hm => ?_⟩
  · rw [← Ideal.zero_eq_bot]
    exact Finset.prod_ne_zero_iff.mpr fun p _ => by rw [Ideal.zero_eq_bot]; exact hA p.1 p.2
  · have hrA : ∀ i j, r ∈ A i j := fun i j =>
      (Ideal.prod_le_inf.trans (Finset.inf_le (Finset.mem_univ (i, j)))) hr
    apply hOT
    apply hIt
    intro i hi
    have hmi : m i ∈ (if i ∈ I then t i else Set.univ) := by
      apply hsub i
      intro j _
      have h := hAt i j r (hrA i j) hr0 ((m - 1) i j) (hm i j)
      rwa [Matrix.sub_apply, add_sub_cancel] at h
    rw [if_pos (Finset.mem_coe.mp hi)] at hmi
    exact hmi

private theorem exists_forall_sub_one_mem_idealBall_imp_mem (U : Subgroup (GL (Fin 2) AfQ))
    (hU : IsOpen (U : Set (GL (Fin 2) AfQ))) :
    ∃ M : ℕ, M ≠ 0 ∧ ∀ k : GL (Fin 2) AfQ,
      (∀ i j, ((k : Matrix (Fin 2) (Fin 2) AfQ) - 1) i j ∈ idealBall (𝓞 ℚ) ℚ (Ideal.span {(M : 𝓞 ℚ)})) →
      (∀ i j, (((k⁻¹ : GL (Fin 2) AfQ) : Matrix (Fin 2) (Fin 2) AfQ) - 1) i j ∈
        idealBall (𝓞 ℚ) ℚ (Ideal.span {(M : 𝓞 ℚ)})) →
      k ∈ U := by
  have h1 : (U : Set (GL (Fin 2) AfQ)) ∈ nhds (1 : GL (Fin 2) AfQ) := hU.mem_nhds U.one_mem
  rw [Units.isInducing_embedProduct.nhds_eq_comap, Filter.mem_comap] at h1
  obtain ⟨S, hS, hSU⟩ := h1
  rw [Units.embedProduct_apply, Units.val_one, inv_one, Units.val_one, MulOpposite.op_one,
    mem_nhds_prod_iff] at hS
  obtain ⟨S₁, hS₁, S₂, hS₂, hS₁₂⟩ := hS
  have hS₂' : MulOpposite.op ⁻¹' S₂ ∈ nhds (1 : Matrix (Fin 2) (Fin 2) AfQ) :=
    MulOpposite.continuous_op.continuousAt.preimage_mem_nhds (by rwa [MulOpposite.op_one])
  obtain ⟨A₁, hA₁, h₁⟩ := exists_forall_sub_one_mem_idealBall_imp hS₁
  obtain ⟨A₂, hA₂, h₂⟩ := exists_forall_sub_one_mem_idealBall_imp hS₂'
  have hA : A₁ * A₂ ≠ ⊥ := mul_ne_zero hA₁ hA₂
  refine ⟨Ideal.absNorm (A₁ * A₂), fun h => hA (Ideal.absNorm_eq_zero_iff.mp h), fun k hk hk' => ?_⟩
  have hr : ((Ideal.absNorm (A₁ * A₂) : ℕ) : 𝓞 ℚ) ∈ A₁ * A₂ := Ideal.absNorm_mem _
  have hr0 : ((Ideal.absNorm (A₁ * A₂) : ℕ) : 𝓞 ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr fun h => hA (Ideal.absNorm_eq_zero_iff.mp h)
  apply hSU
  show Units.embedProduct _ k ∈ S
  rw [Units.embedProduct_apply]
  apply hS₁₂
  refine Set.mk_mem_prod ?_ ?_
  · exact h₁ _ (Ideal.mul_le_left hr) hr0 _ hk
  · exact h₂ _ (Ideal.mul_le_right hr) hr0 _ hk'

end AutomorphicForm.PrincipalLevelNhds

namespace AutomorphicForm
p2m_export "AutomorphicForm" "CuspidalConstituent.rightTranslate CuspidalConstituent.IsCuspConstituent typeSubmodule mem_typeSubmodule_of_isRightEquivariant comp_mul_mem_typeSubmodule_of_commute rowIsometryInclAt₀ rowIsometryInclAt₀_apply archTypeSubmoduleAt ArchTypeFamily archCutSubmodule mem_archCutSubmodule_iff classRepTranslates productionPinsGeneral CarrierPins AdelicGL2 finiteAdelicGL2Subgroup mem_finiteAdelicGL2Subgroup_iff rowIsometrySubgroup₀ mem_rowIsometrySubgroup₀_iff archGLIncl archComponent_archGLIncl_self archComponent_archGLIncl_of_ne adelicArchGLIncl adelicArchGLInclAt glArch_adelicArchGLIncl glFin_adelicArchGLIncl fnTwist fnTwist_apply finiteDimensional_inf_levelInvariantSubmodule_inf_archCutSubmodule_of_isCuspConstituent SiegelCovering.coversModCentre_productionPinsGeneral_D_rat mul_dirichletIdeleChar_det_rightTranslate_invariant_levelOne_sq CuspidalConstituent.isCuspConstituent_twistedCentralChar_span_image_fnTwist"
namespace CharacterLanding
p2m_open "AutomorphicForm"

open NumberField NumberField.AdelicLevel IsDedekindDomain AdelicDock RatIdele DirichletCharacter
open AutomorphicForm.CuspidalConstituent AutomorphicForm.TorusOnPrincipalFixed
open AutomorphicForm.TorusEigenDecomposition

private theorem det_eq_one_of_glArch_of_glFin {g : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)}
    (h1 : Matrix.GeneralLinearGroup.det (glArch (𝓞 ℚ) ℚ g) = 1)
    (h2 : Matrix.GeneralLinearGroup.det (glFin (𝓞 ℚ) ℚ g) = 1) :
    Matrix.GeneralLinearGroup.det g = 1 := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one]
  have e1 : Matrix.det (glArch (𝓞 ℚ) ℚ g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing ℚ)) = 1 := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply, h1, Units.val_one]
  have e2 : Matrix.det (glFin (𝓞 ℚ) ℚ g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) = 1 := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply, h2, Units.val_one]
  refine Prod.ext ?_ ?_
  · show adeleArch (𝓞 ℚ) ℚ (Matrix.det (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ))) = 1
    rw [RingHom.map_det]
    exact e1
  · show adeleFin (𝓞 ℚ) ℚ (Matrix.det (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ))) = 1
    rw [RingHom.map_det]
    exact e2

private theorem det_archGLIncl_eq_one (w : InfinitePlace ℚ) {k : GL (Fin 2) w.Completion}
    (hk : Matrix.GeneralLinearGroup.det k = 1) :
    Matrix.GeneralLinearGroup.det (archGLIncl ℚ w k) = 1 := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one]
  funext v
  show archEval ℚ v (Matrix.det (archGLIncl ℚ w k : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing ℚ))) = 1
  rw [RingHom.map_det]
  show Matrix.det (archComponent ℚ v (archGLIncl ℚ w k) : Matrix (Fin 2) (Fin 2) v.Completion) = 1
  by_cases hvw : v = w
  · subst hvw
    rw [archComponent_archGLIncl_self, ← Matrix.GeneralLinearGroup.val_det_apply, hk, Units.val_one]
  · rw [archComponent_archGLIncl_of_ne ℚ hvw, Units.val_one, Matrix.det_one]

private theorem det_rowIsometryInclAt₀ (w : InfinitePlace ℚ) (k : rowIsometrySubgroup₀ w.Completion) :
    Matrix.GeneralLinearGroup.det (rowIsometryInclAt₀ ℚ w k) = 1 := by
  have hk : Matrix.GeneralLinearGroup.det (k : GL (Fin 2) w.Completion) = 1 :=
    Units.ext (by
      rw [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one]
      exact ((mem_rowIsometrySubgroup₀_iff _).mp k.2).1)
  rw [rowIsometryInclAt₀_apply,
    show adelicArchGLInclAt ℚ w (k : GL (Fin 2) w.Completion) =
      adelicArchGLIncl ℚ (archGLIncl ℚ w k) from rfl]
  refine det_eq_one_of_glArch_of_glFin ?_ ?_
  · rw [glArch_adelicArchGLIncl]
    exact det_archGLIncl_eq_one w hk
  · rw [glFin_adelicArchGLIncl, map_one]

private theorem mul_mem_typeSubmodule_of_forall {G H W : Type*} [Group G] [Group H] [AddCommGroup W]
    [Module ℂ W] {ι : H →* G} {ρ : Representation ℂ H W} {f : G → ℂ} (hf : f ∈ typeSubmodule ι ρ)
    (θ : G → ℂ) (hθ : ∀ (k : H) (x : G), θ (x * ι k) = θ x) : f * θ ∈ typeSubmodule ι ρ := by
  refine Submodule.span_induction (p := fun f _ => f * θ ∈ typeSubmodule ι ρ) ?_ ?_ ?_ ?_ hf
  · rintro _ ⟨T, hT, v, rfl⟩
    refine mem_typeSubmodule_of_isRightEquivariant (T := (LinearMap.mulRight ℂ θ).comp T) ?_ v
    intro k v' x
    show T (ρ k v') x * θ x = T v' (x * ι k) * θ (x * ι k)
    rw [hT k v' x, hθ k x]
  · show (0 : G → ℂ) * θ ∈ typeSubmodule ι ρ
    rw [zero_mul]
    exact Submodule.zero_mem _
  · intro f g _ _ hf hg
    rw [add_mul]
    exact Submodule.add_mem _ hf hg
  · intro c f _ hf
    rw [smul_mul_assoc]
    exact Submodule.smul_mem _ c hf

private theorem mul_mem_archCutSubmodule (tys : ArchTypeFamily ℚ) {φ : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ) → ℂ}
    (hφ : φ ∈ archCutSubmodule ℚ tys) (θ : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ) → ℂ)
    (hθ : ∀ (w : InfinitePlace ℚ) (k : rowIsometrySubgroup₀ w.Completion)
      (x : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)), θ (x * rowIsometryInclAt₀ ℚ w k) = θ x) :
    φ * θ ∈ archCutSubmodule ℚ tys := by
  rw [mem_archCutSubmodule_iff] at hφ ⊢
  intro w
  have hle : ∀ i : Fin (tys.card w),
      (archTypeSubmoduleAt ℚ w (tys.rep w i)).map (LinearMap.mulRight ℂ θ) ≤
        archTypeSubmoduleAt ℚ w (tys.rep w i) := by
    intro i f hf
    obtain ⟨f₀, hf₀, rfl⟩ := Submodule.mem_map.mp hf
    exact mul_mem_typeSubmodule_of_forall hf₀ θ fun k x => hθ w k x
  have hmap : (⨆ i, archTypeSubmoduleAt ℚ w (tys.rep w i)).map (LinearMap.mulRight ℂ θ) ≤
      ⨆ i, archTypeSubmoduleAt ℚ w (tys.rep w i) := by
    rw [Submodule.map_iSup]
    exact iSup_mono hle
  exact hmap (Submodule.mem_map_of_mem (hφ w))

private def twistFn {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ) → ℂ :=
  fun x => ((dirichletIdeleChar χ (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ)

private theorem twistFn_apply {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (x : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) :
    twistFn χ x = ((dirichletIdeleChar χ (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ) :=
  rfl

private theorem twistFn_ne_zero {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (x : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) : twistFn χ x ≠ 0 :=
  Units.ne_zero _

private theorem twistFn_mul_rowIsometryInclAt₀ {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (w : InfinitePlace ℚ) (k : rowIsometrySubgroup₀ w.Completion) (x : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) :
    twistFn χ (x * rowIsometryInclAt₀ ℚ w k) = twistFn χ x := by
  rw [twistFn_apply, twistFn_apply, map_mul, det_rowIsometryInclAt₀, mul_one]

private def scaleUnit (M : ℕ) [NeZero M] : AfQˣ :=
  Units.map (algebraMap ℚ AfQ : ℚ →* AfQ) (Units.mk0 (M : ℚ) (Nat.cast_ne_zero.mpr (NeZero.ne M)))

private def scaleElt (M : ℕ) [NeZero M] : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ) :=
  (finEmbed (𝓞 ℚ) ℚ (diagOne (scaleUnit M)))⁻¹

private theorem glArch_scaleElt (M : ℕ) [NeZero M] : glArch (𝓞 ℚ) ℚ (scaleElt M) = 1 := by
  rw [scaleElt, map_inv, glArch_finEmbed (R := 𝓞 ℚ) (K := ℚ), inv_one]

private def eigTransfer (s : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) (θ : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ) → ℂ) :
    (GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ) → ℂ) →ₗ[ℂ] (GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ) → ℂ) :=
  (LinearMap.mulRight ℂ θ).comp (rightRegular ℚ s)

private theorem eigTransfer_apply (s : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) (θ : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ) → ℂ)
    (ψ : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ) → ℂ) (x : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) :
    eigTransfer s θ ψ x = ψ (x * s) * θ x :=
  rfl

private theorem eigTransfer_injective (s : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) {θ : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ) → ℂ}
    (hθ : ∀ x, θ x ≠ 0) : Function.Injective (eigTransfer s θ) := by
  intro ψ₁ ψ₂ h
  funext y
  have hy := congrFun h (y * s⁻¹)
  rw [eigTransfer_apply, eigTransfer_apply, inv_mul_cancel_right] at hy
  exact mul_right_cancel₀ (hθ _) hy

variable {ξ : (productionPinsGeneral ℚ).Z →* ℂˣ} {V : Submodule ℂ (GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ) → ℂ)}

private theorem eigTransfer_mem (hV : IsCuspConstituent ℚ (productionPinsGeneral ℚ) ξ V) (M : ℕ) [NeZero M]
    (tys : ArchTypeFamily ℚ) (χ : DirichletCharacter ℂ M) {ψ : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ) → ℂ}
    (hψ : ψ ∈ eigenSubmoduleOf torusOp (residueHom M) (V ⊓ principalFixed M ⊓ archCutSubmodule ℚ tys) χ) :
    eigTransfer (scaleElt M) (twistFn χ) ψ ∈
      V.map (LinearMap.mulRight ℂ (twistFn χ)) ⊓
        levelInvariantSubmodule ℚ (productionPinsGeneral ℚ) (Ideal.span {(M : 𝓞 ℚ)} ^ 2) ⊓
        archCutSubmodule ℚ tys := by
  rw [mem_eigenSubmoduleOf_iff, Submodule.mem_inf, Submodule.mem_inf] at hψ
  obtain ⟨⟨⟨hψV, hψF⟩, hψt⟩, heig⟩ := hψ
  have hs : scaleElt M ∈ finiteAdelicGL2Subgroup ℚ := by
    rw [mem_finiteAdelicGL2Subgroup_iff]
    exact glArch_scaleElt M
  have hT : ∀ (x : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) (u : AfQˣ),
      (u : AfQ) ∈ integralFiniteAdeles (𝓞 ℚ) ℚ → ((u⁻¹ : AfQˣ) : AfQ) ∈ integralFiniteAdeles (𝓞 ℚ) ℚ →
      ψ (x * finEmbed (𝓞 ℚ) ℚ (diagOne u)) =
        χ (unitResidue M (Matrix.GeneralLinearGroup.det (finEmbed (𝓞 ℚ) ℚ (diagOne u)))) * ψ x := by
    intro x u hu hu'
    have h := congrFun (heig ⟨u, hu, hu'⟩) x
    rw [torusOp_apply, Pi.smul_apply, smul_eq_mul] at h
    exact h
  refine Submodule.mem_inf.mpr ⟨Submodule.mem_inf.mpr ⟨?_, ?_⟩, ?_⟩
  · show LinearMap.mulRight ℂ (twistFn χ) (rightRegular ℚ (scaleElt M) ψ) ∈ _
    exact Submodule.mem_map_of_mem (hV.1.rightTranslate_fin_mem _ hs ψ hψV)
  · intro g u hu
    change u ∈ levelOne (𝓞 ℚ) ℚ (Ideal.span {(M : 𝓞 ℚ)} ^ 2) ⊓ finiteAdelicGL2Subgroup ℚ at hu
    obtain ⟨hu1, hu2⟩ := Subgroup.mem_inf.mp hu
    rw [mem_levelOne_iff] at hu1
    rw [mem_finiteAdelicGL2Subgroup_iff] at hu2
    rw [← finEmbed_glFin_of_glArch_eq_one hu2]
    exact AutomorphicForm.mul_dirichletIdeleChar_det_rightTranslate_invariant_levelOne_sq M χ ψ hψF hT g
      (glFin (𝓞 ℚ) ℚ u) hu1
  · exact mul_mem_archCutSubmodule tys
      (rightTranslate_mem_archCutSubmodule_of_glArch_eq_one tys hψt (glArch_scaleElt M)) (twistFn χ)
      (twistFn_mul_rowIsometryInclAt₀ χ)

private theorem isCuspConstituent_map_mulRight_twistFn
    (hV : IsCuspConstituent ℚ (productionPinsGeneral ℚ) ξ V) {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) :
    IsCuspConstituent ℚ (productionPinsGeneral ℚ)
      (ξ * ((dirichletIdeleChar χ).comp (productionPinsGeneral ℚ).Z.subtype) ^ 2)
      (V.map (LinearMap.mulRight ℂ (twistFn χ))) := by
  have hfun : (fun φ => AutomorphicForm.fnTwist ℚ (dirichletIdeleChar χ) φ) =
      ⇑(LinearMap.mulRight ℂ (twistFn χ)) := by
    funext φ
    funext g
    rw [LinearMap.mulRight_apply, Pi.mul_apply, AutomorphicForm.fnTwist_apply, twistFn_apply]
    exact mul_comm _ _
  have key : Submodule.span ℂ ((fun φ => AutomorphicForm.fnTwist ℚ (dirichletIdeleChar χ) φ) ''
      (V : Set (GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ) → ℂ))) = V.map (LinearMap.mulRight ℂ (twistFn χ)) := by
    rw [hfun, Submodule.span_image, Submodule.span_eq]
  have h := AutomorphicForm.CuspidalConstituent.isCuspConstituent_twistedCentralChar_span_image_fnTwist ℚ
    _ _ _ _ ξ (dirichletIdeleChar χ) (DirichletCharacter.isFiniteOrderHeckeChar_dirichletIdeleChar χ) V hV
  rw [key] at h
  exact h

private theorem finiteDimensional_eigenSubmoduleOf (hV : IsCuspConstituent ℚ (productionPinsGeneral ℚ) ξ V)
    (M : ℕ) [NeZero M] (tys : ArchTypeFamily ℚ) (χ : DirichletCharacter ℂ M) :
    FiniteDimensional ℂ
      (eigenSubmoduleOf torusOp (residueHom M) (V ⊓ principalFixed M ⊓ archCutSubmodule ℚ tys) χ) := by
  have hM : Ideal.span {(M : 𝓞 ℚ)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact Nat.cast_ne_zero.mpr (NeZero.ne M)
  haveI : FiniteDimensional ℂ ↥(V.map (LinearMap.mulRight ℂ (twistFn χ)) ⊓
      levelInvariantSubmodule ℚ (productionPinsGeneral ℚ) (Ideal.span {(M : 𝓞 ℚ)} ^ 2) ⊓
      archCutSubmodule ℚ tys) :=
    AutomorphicForm.finiteDimensional_inf_levelInvariantSubmodule_inf_archCutSubmodule_of_isCuspConstituent
      ℚ (1/2 : ℝ) 1 (1/2) 2 (classRepTranslates ℚ) (by norm_num)
      SiegelCovering.coversModCentre_productionPinsGeneral_D_rat
      (ξ * ((dirichletIdeleChar χ).comp (productionPinsGeneral ℚ).Z.subtype) ^ 2)
      (Ideal.span {(M : 𝓞 ℚ)} ^ 2) (pow_ne_zero 2 hM) tys _
      (isCuspConstituent_map_mulRight_twistFn hV χ)
  refine FiniteDimensional.of_injective
    (LinearMap.codRestrict _ ((eigTransfer (scaleElt M) (twistFn χ)).comp (Submodule.subtype _))
      fun ψ => eigTransfer_mem hV M tys χ ψ.2) fun a b h => ?_
  exact Subtype.ext (eigTransfer_injective (scaleElt M) (twistFn_ne_zero χ) (congrArg Subtype.val h))

end AutomorphicForm.CharacterLanding

p2m_open "NumberField IsDedekindDomain AutomorphicForm P2MW.S_AutomorphicForm_CuspidalConstituent_IsCuspConstituent_finiteDimensional_of_forall_rightTranslate_eq.AutomorphicForm AutomorphicForm.CuspidalConstituent"
open AutomorphicForm.TorusOnPrincipalFixed AutomorphicForm.TorusEigenDecomposition

theorem solution
    (ξ : (AutomorphicForm.productionPinsGeneral ℚ).Z →* ℂˣ)
    (V : Submodule ℂ (AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ))
    (hV : AutomorphicForm.CuspidalConstituent.IsCuspConstituent ℚ
      (AutomorphicForm.productionPinsGeneral ℚ) ξ V)
    (K : Subgroup (GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers ℚ) ℚ)))
    (hK : IsOpen (K : Set (GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers ℚ) ℚ))))
    (tys : AutomorphicForm.ArchTypeFamily ℚ)
    (W : Submodule ℂ (AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ))
    (hWV : W ≤ V)
    (hWK : ∀ φ ∈ W, ∀ k ∈ K,
      AutomorphicForm.CuspidalConstituent.rightTranslate ℚ
        (AdelicDock.finEmbed (NumberField.RingOfIntegers ℚ) ℚ k) φ = φ)
    (hWt : W ≤ AutomorphicForm.archCutSubmodule ℚ tys) :
    FiniteDimensional ℂ W := by
  obtain ⟨M, hM0, hMK⟩ :=
    AutomorphicForm.PrincipalLevelNhds.exists_forall_sub_one_mem_idealBall_imp_mem K hK
  haveI : NeZero M := ⟨hM0⟩
  have hWS : W ≤ V ⊓ principalFixed M ⊓ AutomorphicForm.archCutSubmodule ℚ tys := by
    intro φ hφ
    refine Submodule.mem_inf.mpr ⟨Submodule.mem_inf.mpr ⟨hWV hφ, fun x k hk hk' => ?_⟩, hWt hφ⟩
    exact congrFun (hWK φ hφ k (hMK k hk hk')) x
  haveI : FiniteDimensional ℂ ↥(V ⊓ principalFixed M ⊓ AutomorphicForm.archCutSubmodule ℚ tys) :=
    finiteDimensional_of_eigenSubmoduleOf torusOp (residueHom M) _
      (fun g φ hφ => torusOp_apply_mem hV.1 M tys g hφ)
      (fun g hg φ hφ => torusOp_eq_self_of_residueHom_eq_one M g hg
        (Submodule.mem_inf.mp (Submodule.mem_inf.mp hφ).1).2)
      (fun χ => AutomorphicForm.CharacterLanding.finiteDimensional_eigenSubmoduleOf hV M tys χ)
  exact Submodule.finiteDimensional_of_le hWS

end
end S_AutomorphicForm_CuspidalConstituent_IsCuspConstituent_finiteDimensional_of_forall_rightTranslate_eq
end P2MW
export P2MW.S_AutomorphicForm_CuspidalConstituent_IsCuspConstituent_finiteDimensional_of_forall_rightTranslate_eq (solution)
