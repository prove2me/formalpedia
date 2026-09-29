-- Prove2me | solution 1 for AutomorphicForm.CuspidalConstituent.exists_eq_sum_su2String_highestWeight_of_mem_cut_of_isComplex
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/8352c146-5861-5ccd-962b-4a75fd075c56

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_AutomorphicForm_ArchDerivCasimirComplex
import Definitions.Def_AutomorphicForm_ArchDerivCasimirComplexAPI
import Definitions.Def_AutomorphicForm_ArchWeightCharTransport
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_NumberField_AdelicTraceFin
import Definitions.Def_NumberField_TateGlobalZeta
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Theorems.Thm_AutomorphicForm_exists_su2Strings_of_finiteDimensional_of_isArchSmoothAtComplex
import Theorems.Thm_AutomorphicForm_hasArchCharacterAtZero_one_of_archDerivAtComplex_compact_eq_zero
import Theorems.Thm_AutomorphicForm_su2Derivs_stable_and_hasDerivAt_and_exists_sum_hasCircleWeightAt_of_finiteDimensional
import Theorems.Thm_AutomorphicForm_exists_coordMatrix_rightTranslate_rot_of_linearIndependent_of_span_stable
import Theorems.Thm_AutomorphicForm_CuspidalConstituent_isArchSmoothAtComplex_and_continuous_foldr_archDerivAtComplex_of_mem_cut
import Theorems.Thm_AutomorphicForm_CuspidalConstituent_exists_norm_whittakerCoefficient_le_mul_ideleNorm_det_rpow_of_isCuspConstituent
import Theorems.Thm_AutomorphicForm_CuspidalConstituent_finiteDimensional_span_rightTranslate_of_mem_iSup_archTypeSubmoduleAt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_CuspidalConstituent_exists_eq_sum_su2String_highestWeight_of_mem_cut_of_isComplex
p2m_attr_erase "instance" "RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instCountableOfNumberField_definitions AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply AdelicDock.coe_finEmbed AdelicDock.splice_apply_self"
p2m_attr_erase "simp" "AdelicDock.coe_localEmbed AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox
p2m_open "AutomorphicForm P2MW.S_AutomorphicForm_CuspidalConstituent_exists_eq_sum_su2String_highestWeight_of_mem_cut_of_isComplex.AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering IsDedekindDomain"
open AutomorphicForm.CuspidalConstituent

noncomputable section

namespace AutomorphicForm
p2m_export "AutomorphicForm" "productionPinsOf AdelicGL2 globalPoints centralScalar finiteAdelicGL2Subgroup mem_finiteAdelicGL2Subgroup_iff lsXiMemberAt_iff rowIsometryInclAt₀ archTypeSubmoduleAt ArchTypeFamily archCutSubmodule mem_archCutSubmodule_iff glFin_rowIsometryInclAt₀ rowIsometrySubgroup₀ HasArchCharacterAt₀ archComplexLiftAt IsArchSmoothAtComplex ArchDirComplex archDerivAtComplex archCasimirAtComplex archCasimirBarAtComplex HasCircleWeightAt eq_of_glArch_eq_of_glFin_eq archComplexLiftAt_of_symm_one archDerivAtComplex_add archDerivAtComplex_smul whittakerCoefficient exists_su2Strings_of_finiteDimensional_of_isArchSmoothAtComplex hasArchCharacterAtZero_one_of_archDerivAtComplex_compact_eq_zero su2Derivs_stable_and_hasDerivAt_and_exists_sum_hasCircleWeightAt_of_finiteDimensional exists_coordMatrix_rightTranslate_rot_of_linearIndependent_of_span_stable CuspidalConstituent.isArchSmoothAtComplex_and_continuous_foldr_archDerivAtComplex_of_mem_cut CuspidalConstituent.exists_norm_whittakerCoefficient_le_mul_ideleNorm_det_rpow_of_isCuspConstituent CuspidalConstituent.finiteDimensional_span_rightTranslate_of_mem_iSup_archTypeSubmoduleAt"
namespace StringData35
p2m_open "AutomorphicForm"

variable (K : Type) [Field K] [NumberField K]

theorem rightTranslate_one' (φ : AdelicGL2 (𝓞 K) K → ℂ) : rightTranslate K 1 φ = φ := by
  funext x; simp [rightTranslate]

theorem isLsXi_of_mem_cuspKFiniteSubmodule
    (D : Set (AdelicGL2 (𝓞 K) K))
    (ξ : (productionPinsOf K D (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
        (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).Z →* ℂˣ)
    {φ : AdelicGL2 (𝓞 K) K → ℂ}
    (hφ : φ ∈ cuspKFiniteSubmodule K (productionPinsOf K D (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
        (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) ξ) :
    (∀ (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K), φ (globalPoints (𝓞 K) K γ * g) = φ g) ∧
    (∀ (z : (productionPinsOf K D (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
        (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).Z) (g : AdelicGL2 (𝓞 K) K),
        φ (centralScalar (𝓞 K) K (z : (AdeleRing (𝓞 K) K)ˣ) * g) = ((ξ z : ℂˣ) : ℂ) * φ g) ∧
    Continuous φ := by
  refine Submodule.span_induction (p := fun φ _ =>
    (∀ (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K), φ (globalPoints (𝓞 K) K γ * g) = φ g) ∧
    (∀ (z : (productionPinsOf K D (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
        (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).Z) (g : AdelicGL2 (𝓞 K) K),
        φ (centralScalar (𝓞 K) K (z : (AdeleRing (𝓞 K) K)ˣ) * g) = ((ξ z : ℂˣ) : ℂ) * φ g) ∧
    Continuous φ) ?_ ?_ ?_ ?_ hφ
  · rintro φ ⟨hsat, hcont, -⟩
    have h1 := hsat 1
    rw [rightTranslate_one'] at h1
    letI : MeasurableSpace (AdelicGL2 (𝓞 K) K) := NumberField.AdelicHaar.glBorel (Fin 2) (𝓞 K) K
    have hls := ((lsXiMemberAt_iff (𝓞 K) K _ _ ξ _ φ).mp h1.1.1).1
    exact ⟨hls.left_invariant, hls.central_transform, hcont⟩
  · exact ⟨fun _ _ => rfl, fun _ _ => by simp, continuous_zero⟩
  · rintro u w - - ⟨hu1, hu2, hu3⟩ ⟨hw1, hw2, hw3⟩
    refine ⟨fun γ g => by simp only [Pi.add_apply, hu1, hw1], fun z g => ?_, hu3.add hw3⟩
    simp only [Pi.add_apply, hu2, hw2]; ring
  · rintro r u - ⟨hu1, hu2, hu3⟩
    refine ⟨fun γ g => by simp only [Pi.smul_apply, hu1], fun z g => ?_, hu3.const_smul r⟩
    simp only [Pi.smul_apply, smul_eq_mul, hu2]; ring

theorem rowIsometryInclAt₀_mul_comm_of_glArch_eq_one (w : InfinitePlace K) (k : rowIsometrySubgroup₀ w.Completion)
    {u : AdelicGL2 (𝓞 K) K} (hu : AdelicLevel.glArch (𝓞 K) K u = 1) :
    rowIsometryInclAt₀ K w k * u = u * rowIsometryInclAt₀ K w k := by
  refine eq_of_glArch_eq_of_glFin_eq ?_ ?_
  · rw [map_mul, map_mul, hu, mul_one, one_mul]
  · rw [map_mul, map_mul, glFin_rowIsometryInclAt₀, mul_one, one_mul]

theorem rightTranslate_rowIsometryInclAt₀_mem_cut
    (D : Set (AdelicGL2 (𝓞 K) K)) (gen : HeightOneSpectrum (𝓞 K) → AdelicGL2 (𝓞 K) K) (B : Set (AdeleRing (𝓞 K) K))
    {ξ : (productionPinsOf K D (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) gen B).Z →* ℂˣ}
    {V : Submodule ℂ (AdelicGL2 (𝓞 K) K → ℂ)}
    (hV : IsCuspSubrep K (productionPinsOf K D (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) gen B) ξ V)
    (N : Ideal (𝓞 K)) (tys : ArchTypeFamily K)
    {φ : AdelicGL2 (𝓞 K) K → ℂ}
    (hφ : φ ∈ V ⊓ levelInvariantSubmodule K
        (productionPinsOf K D (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) gen B) N ⊓ archCutSubmodule K tys)
    (w : InfinitePlace K) (k : rowIsometrySubgroup₀ w.Completion) :
    rightTranslate K (rowIsometryInclAt₀ K w k) φ ∈ V ⊓ levelInvariantSubmodule K
        (productionPinsOf K D (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) gen B) N ⊓ archCutSubmodule K tys := by
  obtain ⟨⟨hV', hL⟩, hC⟩ := hφ
  refine ⟨⟨hV.rightTranslate_arch_mem w k φ hV', ?_⟩, rightTranslate_rowIsometryInclAt₀_mem_archCutSubmodule K tys hC w k⟩
  intro g u hu
  have hu' : AdelicLevel.glArch (𝓞 K) K u = 1 := (mem_finiteAdelicGL2Subgroup_iff K u).mp hu.2
  show φ (g * u * rowIsometryInclAt₀ K w k) = φ (g * rowIsometryInclAt₀ K w k)
  rw [mul_assoc, ← rowIsometryInclAt₀_mul_comm_of_glArch_eq_one K w k hu', ← mul_assoc]
  exact hL _ u hu

section Ladder

variable {K}
variable {w : InfinitePlace K} (hw : w.IsComplex)

theorem sum_ladder_eq (n : ℕ) (x : ℕ → (AdelicGL2 (𝓞 K) K → ℂ)) (hxz : ∀ p, n < p → x p = 0)
    (a : ℂ) (b : ℂ → ℂ) (hb : b 0 = 0) (p : Fin (n + 1)) (g : AdelicGL2 (𝓞 K) K) :
    (∑ p' : Fin (n + 1),
        (if (p' : ℕ) = p + 1 then a else if (p : ℕ) = p' + 1 then b (p : ℂ) else 0) * x p' g) =
      a * x ((p : ℕ) + 1) g + b (p : ℂ) * x ((p : ℕ) - 1) g := by
  classical
  have hsplit : ∀ p' : Fin (n + 1),
      (if (p' : ℕ) = p + 1 then a else if (p : ℕ) = p' + 1 then b (p : ℂ) else 0) * x p' g =
        (if (p' : ℕ) = p + 1 then a * x p' g else 0) + (if (p : ℕ) = p' + 1 then b (p : ℂ) * x p' g else 0) := by
    intro p'
    by_cases h1 : (p' : ℕ) = p + 1
    · have h2 : ¬ (p : ℕ) = p' + 1 := by omega
      rw [if_pos h1, if_pos h1, if_neg h2, add_zero]
    · by_cases h2 : (p : ℕ) = p' + 1
      · rw [if_neg h1, if_pos h2, if_neg h1, if_pos h2, zero_add]
      · rw [if_neg h1, if_neg h2, if_neg h1, if_neg h2, zero_mul, add_zero]
  rw [Finset.sum_congr rfl fun p' _ => hsplit p', Finset.sum_add_distrib]
  congr 1
  ·
    by_cases hp : (p : ℕ) + 1 < n + 1
    · rw [Finset.sum_eq_single ⟨(p : ℕ) + 1, hp⟩]
      · simp
      · intro q _ hq
        have : ¬ ((q : ℕ) = p + 1) := fun h => hq (Fin.ext h)
        simp [this]
      · intro h; exact absurd (Finset.mem_univ _) h
    · have hz : x ((p : ℕ) + 1) = 0 := hxz _ (by omega)
      rw [hz, Finset.sum_eq_zero]
      · simp
      · intro q _
        have : ¬ ((q : ℕ) = p + 1) := by have := q.isLt; omega
        simp [this]
  ·
    by_cases hp : 1 ≤ (p : ℕ)
    · have hlt : (p : ℕ) - 1 < n + 1 := by have := p.isLt; omega
      rw [Finset.sum_eq_single ⟨(p : ℕ) - 1, hlt⟩]
      · have : (p : ℕ) = (p : ℕ) - 1 + 1 := by omega
        simp [← this]
      · intro q _ hq
        have : ¬ ((p : ℕ) = q + 1) := fun h => hq (Fin.ext (by simp; omega))
        simp [this]
      · intro h; exact absurd (Finset.mem_univ _) h
    · have hp0 : (p : ℕ) = 0 := by omega
      have hb0 : b (p : ℂ) = 0 := by
        have : ((p : ℕ) : ℂ) = 0 := by rw [hp0]; simp
        rw [show (p : ℂ) = ((p : ℕ) : ℂ) from rfl, this, hb]
      rw [hb0, zero_mul, Finset.sum_eq_zero]
      intro q _
      have : ¬ ((p : ℕ) = q + 1) := by omega
      simp [this]

end Ladder

end AutomorphicForm.StringData35

namespace AutomorphicForm
p2m_export "AutomorphicForm" "productionPinsOf AdelicGL2 globalPoints centralScalar finiteAdelicGL2Subgroup mem_finiteAdelicGL2Subgroup_iff lsXiMemberAt_iff rowIsometryInclAt₀ archTypeSubmoduleAt ArchTypeFamily archCutSubmodule mem_archCutSubmodule_iff glFin_rowIsometryInclAt₀ rowIsometrySubgroup₀ HasArchCharacterAt₀ archComplexLiftAt IsArchSmoothAtComplex ArchDirComplex archDerivAtComplex archCasimirAtComplex archCasimirBarAtComplex HasCircleWeightAt eq_of_glArch_eq_of_glFin_eq archComplexLiftAt_of_symm_one archDerivAtComplex_add archDerivAtComplex_smul whittakerCoefficient exists_su2Strings_of_finiteDimensional_of_isArchSmoothAtComplex hasArchCharacterAtZero_one_of_archDerivAtComplex_compact_eq_zero su2Derivs_stable_and_hasDerivAt_and_exists_sum_hasCircleWeightAt_of_finiteDimensional exists_coordMatrix_rightTranslate_rot_of_linearIndependent_of_span_stable CuspidalConstituent.isArchSmoothAtComplex_and_continuous_foldr_archDerivAtComplex_of_mem_cut CuspidalConstituent.exists_norm_whittakerCoefficient_le_mul_ideleNorm_det_rpow_of_isCuspConstituent CuspidalConstituent.finiteDimensional_span_rightTranslate_of_mem_iSup_archTypeSubmoduleAt"
namespace StringData35
p2m_open "AutomorphicForm"

section OneString

variable {K : Type} [Field K] [NumberField K]
variable {w : InfinitePlace K} (hw : w.IsComplex)

theorem archComplexLiftAt_rot_zero :
    archComplexLiftAt hw !![(Real.cos 0 : ℂ), -(Real.sin 0 : ℂ); (Real.sin 0 : ℂ), (Real.cos 0 : ℂ)] = 1 := by
  have h : (!![(Real.cos 0 : ℂ), -(Real.sin 0 : ℂ); (Real.sin 0 : ℂ), (Real.cos 0 : ℂ)] : Fin 2 → Fin 2 → ℂ) =
      Matrix.of.symm (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    ext i j; fin_cases i <;> fin_cases j <;> simp
  rw [h]; exact archComplexLiftAt_of_symm_one hw

theorem archComplexLiftAt_rotI_zero :
    archComplexLiftAt hw !![(Real.cos 0 : ℂ), (Real.sin 0 : ℂ) * Complex.I; (Real.sin 0 : ℂ) * Complex.I, (Real.cos 0 : ℂ)] = 1 := by
  have h : (!![(Real.cos 0 : ℂ), (Real.sin 0 : ℂ) * Complex.I; (Real.sin 0 : ℂ) * Complex.I, (Real.cos 0 : ℂ)] : Fin 2 → Fin 2 → ℂ) =
      Matrix.of.symm (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    ext i j; fin_cases i <;> fin_cases j <;> simp
  rw [h]; exact archComplexLiftAt_of_symm_one hw

theorem archDerivAtComplex_zero' (d : ArchDirComplex) :
    archDerivAtComplex hw d (0 : AdelicGL2 (𝓞 K) K → ℂ) = 0 := by
  have h := archDerivAtComplex_smul hw d (0 : ℂ) (0 : AdelicGL2 (𝓞 K) K → ℂ)
  simpa using h

theorem string_span_stable_and_hasDerivAt
    (Y : Submodule ℂ (AdelicGL2 (𝓞 K) K → ℂ)) [FiniteDimensional ℂ Y]
    (hYs : ∀ y ∈ Y, IsArchSmoothAtComplex hw y)
    (hYK : ∀ (k : rowIsometrySubgroup₀ w.Completion), ∀ y ∈ Y, (fun g => y (g * rowIsometryInclAt₀ K w k)) ∈ Y)
    (n : ℕ) (x : ℕ → (AdelicGL2 (𝓞 K) K → ℂ)) (hxY : ∀ p, x p ∈ Y) (hxz : ∀ p, n < p → x p = 0)
    (hD0 : ∀ p : ℕ, archDerivAtComplex hw .iH (x p) = (Complex.I * ((n : ℂ) - 2 * (p : ℂ))) • x p)
    (hD1 : ∀ p : ℕ, archDerivAtComplex hw .Fm (x p) - archDerivAtComplex hw .E (x p) =
      x (p + 1) - ((p : ℂ) * ((n : ℂ) + 1 - (p : ℂ))) • x (p - 1))
    (hD2 : ∀ p : ℕ, archDerivAtComplex hw .iE (x p) + archDerivAtComplex hw .iFm (x p) =
      Complex.I • (x (p + 1) + ((p : ℂ) * ((n : ℂ) + 1 - (p : ℂ))) • x (p - 1))) :
    (∀ (p : Fin (n + 1)) (s : ℝ),
      (fun g => x p (g * archComplexLiftAt hw
        !![(Real.cos s : ℂ), -(Real.sin s : ℂ); (Real.sin s : ℂ), (Real.cos s : ℂ)])) ∈
          Submodule.span ℂ (Set.range fun p : Fin (n + 1) => x p)) ∧
    (∀ (p : Fin (n + 1)) (s : ℝ),
      (fun g => x p (g * archComplexLiftAt hw
        !![(Real.cos s : ℂ), (Real.sin s : ℂ) * Complex.I; (Real.sin s : ℂ) * Complex.I, (Real.cos s : ℂ)])) ∈
          Submodule.span ℂ (Set.range fun p : Fin (n + 1) => x p)) ∧
    (∀ (p : Fin (n + 1)) (g : AdelicGL2 (𝓞 K) K),
      HasDerivAt (fun s : ℝ => x p (g * archComplexLiftAt hw
        !![(Real.cos s : ℂ), -(Real.sin s : ℂ); (Real.sin s : ℂ), (Real.cos s : ℂ)]))
        (∑ p' : Fin (n + 1),
          (if (p' : ℕ) = p + 1 then 1 else if (p : ℕ) = p' + 1 then -((p : ℂ) * ((n : ℂ) + 1 - p)) else 0) * x p' g) 0) ∧
    (∀ (p : Fin (n + 1)) (g : AdelicGL2 (𝓞 K) K),
      HasDerivAt (fun s : ℝ => x p (g * archComplexLiftAt hw
        !![(Real.cos s : ℂ), (Real.sin s : ℂ) * Complex.I; (Real.sin s : ℂ) * Complex.I, (Real.cos s : ℂ)]))
        (∑ p' : Fin (n + 1),
          (if (p' : ℕ) = p + 1 then Complex.I else if (p : ℕ) = p' + 1 then Complex.I * ((p : ℂ) * ((n : ℂ) + 1 - p)) else 0) *
            x p' g) 0) := by
  classical
  set S : Submodule ℂ (AdelicGL2 (𝓞 K) K → ℂ) := Submodule.span ℂ (Set.range fun p : Fin (n + 1) => x p) with hS
  have hSY : S ≤ Y := Submodule.span_le.mpr (by rintro _ ⟨p, rfl⟩; exact hxY p)

  have hmem : ∀ p : Fin (n + 1), x p ∈ S := fun p => Submodule.subset_span ⟨p, rfl⟩
  have hup : ∀ p : Fin (n + 1), x ((p : ℕ) + 1) ∈ S := by
    intro p
    by_cases h : (p : ℕ) + 1 < n + 1
    · exact Submodule.subset_span ⟨⟨(p : ℕ) + 1, h⟩, rfl⟩
    · rw [hxz _ (by omega)]; exact S.zero_mem
  have hdown : ∀ p : Fin (n + 1), x ((p : ℕ) - 1) ∈ S := fun p =>
    Submodule.subset_span ⟨⟨(p : ℕ) - 1, by have := p.isLt; omega⟩, rfl⟩

  have hLie : ∀ z ∈ S,
      archDerivAtComplex hw .iH z ∈ S ∧
      (archDerivAtComplex hw .Fm z - archDerivAtComplex hw .E z) ∈ S ∧
      (archDerivAtComplex hw .iE z + archDerivAtComplex hw .iFm z) ∈ S := by
    intro z hz
    refine Submodule.span_induction (p := fun z _ =>
      archDerivAtComplex hw .iH z ∈ S ∧
      (archDerivAtComplex hw .Fm z - archDerivAtComplex hw .E z) ∈ S ∧
      (archDerivAtComplex hw .iE z + archDerivAtComplex hw .iFm z) ∈ S) ?_ ?_ ?_ ?_ hz
    · rintro _ ⟨p, rfl⟩
      refine ⟨?_, ?_, ?_⟩
      · rw [hD0]; exact S.smul_mem _ (hmem p)
      · rw [hD1]; exact S.sub_mem (hup p) (S.smul_mem _ (hdown p))
      · rw [hD2]; exact S.smul_mem _ (S.add_mem (hup p) (S.smul_mem _ (hdown p)))
    · simp only [archDerivAtComplex_zero', sub_zero, add_zero]
      exact ⟨S.zero_mem, S.zero_mem, S.zero_mem⟩
    · intro u v hu hv ⟨hu0, hu1, hu2⟩ ⟨hv0, hv1, hv2⟩
      have hus : IsArchSmoothAtComplex hw u := hYs u (hSY hu)
      have hvs : IsArchSmoothAtComplex hw v := hYs v (hSY hv)
      simp only [archDerivAtComplex_add hus hvs]
      refine ⟨S.add_mem hu0 hv0, ?_, ?_⟩
      · have : archDerivAtComplex hw .Fm u + archDerivAtComplex hw .Fm v -
            (archDerivAtComplex hw .E u + archDerivAtComplex hw .E v) =
            (archDerivAtComplex hw .Fm u - archDerivAtComplex hw .E u) +
            (archDerivAtComplex hw .Fm v - archDerivAtComplex hw .E v) := by abel
        rw [this]; exact S.add_mem hu1 hv1
      · have : archDerivAtComplex hw .iE u + archDerivAtComplex hw .iE v +
            (archDerivAtComplex hw .iFm u + archDerivAtComplex hw .iFm v) =
            (archDerivAtComplex hw .iE u + archDerivAtComplex hw .iFm u) +
            (archDerivAtComplex hw .iE v + archDerivAtComplex hw .iFm v) := by abel
        rw [this]; exact S.add_mem hu2 hv2
    · intro c u hu ⟨hu0, hu1, hu2⟩
      simp only [archDerivAtComplex_smul]
      refine ⟨S.smul_mem c hu0, ?_, ?_⟩
      · rw [← smul_sub]; exact S.smul_mem c hu1
      · rw [← smul_add]; exact S.smul_mem c hu2

  have hK := AutomorphicForm.su2Derivs_stable_and_hasDerivAt_and_exists_sum_hasCircleWeightAt_of_finiteDimensional
    K hw Y hYs hYK
  obtain ⟨-, hK2, hK3, -⟩ := hK
  have hK3S := hK3 S hSY hLie
  refine ⟨fun p s => (hK3S (x p) (hmem p) s).2.1, fun p s => (hK3S (x p) (hmem p) s).2.2, fun p g => ?_, fun p g => ?_⟩
  · have h := (hK2 (x p) (hxY p) g 0).2.1
    refine h.congr_deriv ?_
    dsimp only
    rw [archComplexLiftAt_rot_zero hw, mul_one, Pi.sub_apply]
    have e1 := congrFun (hD1 p) g
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e1
    rw [e1]
    have := sum_ladder_eq n x hxz 1 (fun q => -(q * ((n : ℂ) + 1 - q))) (by simp) p g
    rw [this]; ring
  · have h := (hK2 (x p) (hxY p) g 0).2.2
    refine h.congr_deriv ?_
    dsimp only
    rw [archComplexLiftAt_rotI_zero hw, mul_one, Pi.add_apply]
    have e2 := congrFun (hD2 p) g
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at e2
    rw [e2]
    have := sum_ladder_eq n x hxz Complex.I (fun q => Complex.I * (q * ((n : ℂ) + 1 - q))) (by simp) p g
    rw [this]; ring

end OneString

end AutomorphicForm.StringData35

open AutomorphicForm.StringData35

set_option maxHeartbeats 800000 in
theorem solution

    (K : Type) [Field K] [NumberField K]
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K))
    (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂))
    (ξ : (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)).Z →* ℂˣ)
    (V : Submodule ℂ (AdelicGL2 (𝓞 K) K → ℂ))
    (hV : IsCuspConstituent K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) ξ V)
    (N : Ideal (𝓞 K)) (hN : N ≠ ⊥) (tys : AutomorphicForm.ArchTypeFamily K)
    (hX : V ⊓ levelInvariantSubmodule K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) N ⊓ archCutSubmodule K tys ≠ ⊥)
    (w : InfinitePlace K) (hw : w.IsComplex)
    (y : AdelicGL2 (𝓞 K) K → ℂ) (hy : y ∈ V ⊓ levelInvariantSubmodule K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) N ⊓ archCutSubmodule K tys)
    (w₀ : ℝ)
    (hξ : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      ‖((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = NumberField.TateGlobal.ideleNorm K z ^ w₀)
    (lam lam' : ℂ)
    (hlam : ∀ x ∈ V, IsArchSmoothAtComplex hw x ∧ (∀ d : ArchDirComplex, Continuous (archDerivAtComplex hw d x)) ∧
      (∀ d d' : ArchDirComplex, Continuous (archDerivAtComplex hw d (archDerivAtComplex hw d' x))) ∧
      archCasimirAtComplex hw x = lam • x ∧ archCasimirBarAtComplex hw x = lam' • x) :
    ∃ (m : ℕ) (n : Fin m → ℕ) (x : (s : Fin m) → Fin (n s + 1) → (AdelicGL2 (𝓞 K) K → ℂ))
      (coef : (s : Fin m) → Fin (n s + 1) → ℂ)
      (E₁ E₂ : (s : Fin m) → ℝ → Matrix (Fin (n s + 1)) (Fin (n s + 1)) ℂ),
      y = ∑ s : Fin m, ∑ p : Fin (n s + 1), coef s p • x s p ∧
      ∀ s : Fin m,
        (∀ p, x s p ∈ V ⊓ levelInvariantSubmodule K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) N ⊓ archCutSubmodule K tys) ∧
        (x s 0 ≠ 0) ∧
        (n s = 0 → HasArchCharacterAt₀ K w 1 (x s 0)) ∧
        (archDerivAtComplex hw .iH (x s 0) = (Complex.I * (n s : ℂ)) • x s 0) ∧
        (archDerivAtComplex hw .Fm (x s 0) - archDerivAtComplex hw .E (x s 0)
          + Complex.I • (archDerivAtComplex hw .iE (x s 0) + archDerivAtComplex hw .iFm (x s 0)) = 0) ∧
        (∀ p, Continuous (x s p)) ∧
        (∀ p (γ : GL (Fin 2) K) (g' : AdelicGL2 (𝓞 K) K), x s p (globalPoints (𝓞 K) K γ * g') = x s p g') ∧
        (∀ p (z : (AdeleRing (𝓞 K) K)ˣ) (g' : AdelicGL2 (𝓞 K) K),
          x s p (centralScalar (𝓞 K) K z * g') = ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * x s p g') ∧
        (∀ p (l : List ArchDirComplex),
      IsArchSmoothAtComplex hw (l.foldr (archDerivAtComplex hw) (x s p)) ∧ Continuous (l.foldr (archDerivAtComplex hw) (x s p))) ∧
        (∀ p : Fin (n s + 1), HasCircleWeightAt hw ((n s : ℤ) - 2 * (p : ℕ)) (x s p)) ∧
        (E₁ s 0 = 1) ∧
        (E₂ s 0 = 1) ∧
        (∀ i j : Fin (n s + 1), HasDerivAt (fun r : ℝ => E₁ s r i j)
          (if (i : ℕ) = j + 1 then 1 else if (j : ℕ) = i + 1 then -((j : ℂ) * ((n s : ℂ) + 1 - j)) else 0) 0) ∧
        (∀ i j : Fin (n s + 1), HasDerivAt (fun r : ℝ => E₂ s r i j)
          (if (i : ℕ) = j + 1 then Complex.I else if (j : ℕ) = i + 1 then Complex.I * ((j : ℂ) * ((n s : ℂ) + 1 - j)) else 0) 0) ∧
        (∀ (p : Fin (n s + 1)) (r : ℝ) (g' : AdelicGL2 (𝓞 K) K),
          x s p (g' * archComplexLiftAt hw !![(Real.cos r : ℂ), -(Real.sin r : ℂ); (Real.sin r : ℂ), (Real.cos r : ℂ)]) = ∑ p' : Fin (n s + 1), E₁ s r p' p * x s p' g') ∧
        (∀ (p : Fin (n s + 1)) (r : ℝ) (g' : AdelicGL2 (𝓞 K) K),
          x s p (g' * archComplexLiftAt hw !![(Real.cos r : ℂ), (Real.sin r : ℂ) * Complex.I; (Real.sin r : ℂ) * Complex.I, (Real.cos r : ℂ)]) = ∑ p' : Fin (n s + 1), E₂ s r p' p * x s p' g') ∧
        (∀ p, archCasimirAtComplex hw (x s p) = lam • x s p ∧ archCasimirBarAtComplex hw (x s p) = lam' • x s p) ∧
        (∀ p, ∃ C₀ : ℝ, ∀ g' : AdelicGL2 (𝓞 K) K,
      ‖whittakerCoefficient K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) (x s p) 1 g'‖ ≤ C₀ * NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g') ^ (w₀ / 2)) := by
  classical
  have hyV : y ∈ V := hy.1.1
  have hyC : y ∈ archCutSubmodule K tys := hy.2

  have hφw : y ∈ ⨆ i : Fin (tys.card w), archTypeSubmoduleAt K w (tys.rep w i) :=
    (mem_archCutSubmodule_iff K tys y).mp hyC w
  have hKF := AutomorphicForm.CuspidalConstituent.finiteDimensional_span_rightTranslate_of_mem_iSup_archTypeSubmoduleAt
    K w (tys.card w) (tys.rep w) y hφw
  obtain ⟨hYfin, hYK', -⟩ := hKF
  set Y : Submodule ℂ (AdelicGL2 (𝓞 K) K → ℂ) := Submodule.span ℂ (Set.range fun k : rowIsometrySubgroup₀ w.Completion =>
    rightTranslate K (rowIsometryInclAt₀ K w k) y) with hYdef
  haveI : FiniteDimensional ℂ Y := hYfin
  have hYcut : Y ≤ V ⊓ levelInvariantSubmodule K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) N ⊓ archCutSubmodule K tys :=
    Submodule.span_le.mpr (by
      rintro _ ⟨k, rfl⟩
      exact rightTranslate_rowIsometryInclAt₀_mem_cut K _ _ _ hV.1 N tys hy w k)
  have hYs : ∀ z ∈ Y, IsArchSmoothAtComplex hw z := fun z hz => (hlam z (hYcut hz).1.1).1
  have hYK : ∀ (k : rowIsometrySubgroup₀ w.Completion), ∀ z ∈ Y, (fun g => z (g * rowIsometryInclAt₀ K w k)) ∈ Y :=
    fun k z hz => hYK' k z hz
  have hyY : y ∈ Y := by
    have h1 : rightTranslate K (rowIsometryInclAt₀ K w 1) y ∈ Y := Submodule.subset_span ⟨1, rfl⟩
    rwa [map_one, rightTranslate_one'] at h1

  obtain ⟨m, n, x, hxY, hxz, hli, hspan, hD0, hD1, hD2, hwt⟩ :=
    AutomorphicForm.exists_su2Strings_of_finiteDimensional_of_isArchSmoothAtComplex K hw Y hYs hYK
  obtain ⟨coef, hycoef⟩ := hspan y hyY

  have hKT : ∀ s : Fin m, ∃ E₁ E₂ : ℝ → Matrix (Fin (n s + 1)) (Fin (n s + 1)) ℂ,
      E₁ 0 = 1 ∧ E₂ 0 = 1 ∧
      (∀ i j : Fin (n s + 1), HasDerivAt (fun r : ℝ => E₁ r i j)
        (if (i : ℕ) = j + 1 then 1 else if (j : ℕ) = i + 1 then -((j : ℂ) * ((n s : ℂ) + 1 - j)) else 0) 0) ∧
      (∀ i j : Fin (n s + 1), HasDerivAt (fun r : ℝ => E₂ r i j)
        (if (i : ℕ) = j + 1 then Complex.I else if (j : ℕ) = i + 1 then Complex.I * ((j : ℂ) * ((n s : ℂ) + 1 - j)) else 0) 0) ∧
      (∀ (p : Fin (n s + 1)) (r : ℝ) (g' : AdelicGL2 (𝓞 K) K),
        x s p (g' * archComplexLiftAt hw !![(Real.cos r : ℂ), -(Real.sin r : ℂ); (Real.sin r : ℂ), (Real.cos r : ℂ)]) =
          ∑ p' : Fin (n s + 1), E₁ r p' p * x s p' g') ∧
      (∀ (p : Fin (n s + 1)) (r : ℝ) (g' : AdelicGL2 (𝓞 K) K),
        x s p (g' * archComplexLiftAt hw
          !![(Real.cos r : ℂ), (Real.sin r : ℂ) * Complex.I; (Real.sin r : ℂ) * Complex.I, (Real.cos r : ℂ)]) =
          ∑ p' : Fin (n s + 1), E₂ r p' p * x s p' g') := by
    intro s
    obtain ⟨hR, hS, hR', hS'⟩ :=
      string_span_stable_and_hasDerivAt hw Y hYs hYK (n s) (x s) (hxY s) (hxz s) (hD0 s) (hD1 s) (hD2 s)
    have hli_s : LinearIndependent ℂ (fun p : Fin (n s + 1) => x s p) :=
      hli.comp (Sigma.mk s) sigma_mk_injective
    exact AutomorphicForm.exists_coordMatrix_rightTranslate_rot_of_linearIndependent_of_span_stable K hw (n s)
      (fun p => x s p) hli_s hR hS hR' hS'
  choose E₁ E₂ hE using hKT
  refine ⟨m, n, fun s p => x s p, coef, E₁, E₂, hycoef, fun s => ?_⟩
  obtain ⟨hE1, hE2, hE1', hE2', hRf, hSf⟩ := hE s
  have hcut : ∀ p : ℕ, x s p ∈ V ⊓ levelInvariantSubmodule K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) N ⊓ archCutSubmodule K tys := fun p => hYcut (hxY s p)
  have hlaws : ∀ p : ℕ,
      (∀ (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K), x s p (globalPoints (𝓞 K) K γ * g) = x s p g) ∧
      (∀ (z : (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
          (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).Z)
          (g : AdelicGL2 (𝓞 K) K),
          x s p (centralScalar (𝓞 K) K (z : (AdeleRing (𝓞 K) K)ˣ) * g) = ((ξ z : ℂˣ) : ℂ) * x s p g) ∧
      Continuous (x s p) := fun p =>
    isLsXi_of_mem_cuspKFiniteSubmodule K _ ξ (hV.1.le (hcut p).1.1)

  set p0 : Fin (n s + 1) := 0 with hp0def
  have hp0 : ((p0 : ℕ)) = 0 := by simp [hp0def]
  have hc0 : ((p0 : ℕ) : ℂ) * ((n s : ℂ) + 1 - ((p0 : ℕ) : ℂ)) = 0 := by rw [hp0]; simp
  refine ⟨fun p => hcut p, ?_, ?_, ?_, ?_, fun p => (hlaws p).2.2, fun p γ g' => (hlaws p).1 γ g',
    fun p z g' => (hlaws p).2.1 ⟨z, Subgroup.mem_top z⟩ g',
    fun p l => AutomorphicForm.CuspidalConstituent.isArchSmoothAtComplex_and_continuous_foldr_archDerivAtComplex_of_mem_cut
      K c u d₁ d₂ T hc hd₁ hd hcov ξ V hV N hN tys (x s p) (hcut p) w hw l,
    fun p => hwt s p (Nat.lt_succ_iff.mp p.isLt), hE1, hE2, hE1', hE2', hRf, hSf,
    fun p => (hlam _ (hcut p).1.1).2.2.2,
    fun p => AutomorphicForm.CuspidalConstituent.exists_norm_whittakerCoefficient_le_mul_ideleNorm_det_rpow_of_isCuspConstituent
      K c u d₁ d₂ T hc hd₁ hd hcov ξ N hN tys V hV (x s p) (hcut p) w₀ hξ⟩
  ·
    exact hli.ne_zero ⟨s, p0⟩
  ·
    intro hn
    have hx1 : x s ((p0 : ℕ) + 1) = 0 := hxz s _ (by omega)
    have h0 : archDerivAtComplex hw .iH (x s p0) = 0 := by
      rw [hD0 s p0]
      have : Complex.I * ((n s : ℂ) - 2 * ((p0 : ℕ) : ℂ)) = 0 := by rw [hp0, hn]; simp
      rw [this, zero_smul]
    have h1 : archDerivAtComplex hw .Fm (x s p0) - archDerivAtComplex hw .E (x s p0) = 0 := by
      rw [hD1 s p0, hx1, hc0, zero_smul, sub_zero]
    have h2 : archDerivAtComplex hw .iE (x s p0) + archDerivAtComplex hw .iFm (x s p0) = 0 := by
      rw [hD2 s p0, hx1, hc0, zero_smul, add_zero, smul_zero]
    exact AutomorphicForm.hasArchCharacterAtZero_one_of_archDerivAtComplex_compact_eq_zero K hw Y hYs hYK (x s p0)
      (hxY s p0) h0 h1 h2
  ·
    rw [hD0 s p0]
    congr 1
    rw [hp0]; simp
  ·
    rw [hD1 s p0, hD2 s p0, hc0]
    simp [smul_smul, Complex.I_mul_I]

end
end S_AutomorphicForm_CuspidalConstituent_exists_eq_sum_su2String_highestWeight_of_mem_cut_of_isComplex
end P2MW
export P2MW.S_AutomorphicForm_CuspidalConstituent_exists_eq_sum_su2String_highestWeight_of_mem_cut_of_isComplex (solution)
