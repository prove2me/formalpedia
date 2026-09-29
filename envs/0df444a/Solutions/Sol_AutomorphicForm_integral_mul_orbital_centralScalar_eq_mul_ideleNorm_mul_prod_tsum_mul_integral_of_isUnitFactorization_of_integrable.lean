-- Prove2me | solution 1 for AutomorphicForm.integral_mul_orbital_centralScalar_eq_mul_ideleNorm_mul_prod_tsum_mul_integral_of_isUnitFactorization_of_integrable
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/339dbffd-3daf-5a9c-8633-7d1070238461

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Theorems.Thm_AutomorphicForm_exists_isOrbitalIntegralOn_adeleRing_eq_mul_prod_of_isUnitFactorization
import Theorems.Thm_AutomorphicForm_eq_inv_mul_of_isOrbitalIntegralOn_of_isOrbitalIntegralOn_smul_infiniteAdeleRing
import Theorems.Thm_AutomorphicForm_eq_of_isOrbitalIntegral_of_isOrbitalIntegral_of_isRegularSemisimple
import Theorems.Thm_AutomorphicForm_eq_of_isOrbitalIntegral_of_isOrbitalIntegral_smul_diagonal_of_forall_centralUnit_mul
import Theorems.Thm_AutomorphicForm_eq_ite_inv_norm_sub_one_of_isOrbitalIntegral_indicator_localIntegralSet_diagonal
import Theorems.Thm_NumberField_TateGlobal_ideleNorm_partAt_mul_prod_norm_mul_finprod_norm_eq_one
import Theorems.Thm_NumberField_Idele_integral_mul_indicator_unitIdelesOutside_mul_prod_translate_eq_mul_integral_mul_prod_tsum
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "NumberField.InfinitePlace.Completion.ext"
p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
namespace P2MW.S_AutomorphicForm_integral_mul_orbital_centralScalar_eq_mul_ideleNorm_mul_prod_tsum_mul_integral_of_isUnitFactorization_of_integrable
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicHaar IsDedekindDomain

attribute [local instance] NumberField.AdelicHaar.glBorel AutomorphicForm.centralizerBorel

open LanglandsTunnell.CubicInduction (diagUnits2)

namespace AutomorphicForm
p2m_export "AutomorphicForm" "glBorelOf centralizerBorel IsOrbitalIntegralOn IsUnitFactorization IsLocalTestFn localIntegralSet mem_localIntegralSet localGLBorel localHaar localCentralizer localCentralizerBorel IsOrbitalIntegral IsRegularSemisimple globalPoints centralScalar exists_isOrbitalIntegralOn_adeleRing_eq_mul_prod_of_isUnitFactorization eq_inv_mul_of_isOrbitalIntegralOn_of_isOrbitalIntegralOn_smul_infiniteAdeleRing eq_of_isOrbitalIntegral_of_isOrbitalIntegral_of_isRegularSemisimple eq_of_isOrbitalIntegral_of_isOrbitalIntegral_smul_diagonal_of_forall_centralUnit_mul eq_ite_inv_norm_sub_one_of_isOrbitalIntegral_indicator_localIntegralSet_diagonal"
namespace FactorCentreK
p2m_open "AutomorphicForm"

variable (K : Type) [Field K] [NumberField K]

theorem norm_eq_one_iff_valued (v : HeightOneSpectrum (𝓞 K)) (x : v.adicCompletion K) :
    ‖x‖ = 1 ↔ Valued.v x = 1 := by
  constructor
  · intro h
    apply le_antisymm
    · exact Valued.toNormedField.norm_le_one_iff.mp h.le
    · exact Valued.toNormedField.one_le_norm_iff.mp h.ge
  · intro h
    apply le_antisymm
    · exact Valued.toNormedField.norm_le_one_iff.mpr h.le
    · exact Valued.toNormedField.one_le_norm_iff.mpr h.ge

theorem valued_irreducible (v : HeightOneSpectrum (𝓞 K)) (ϖ : v.adicCompletionIntegers K)
    (hϖ : Irreducible ϖ) : Valued.v (ϖ : v.adicCompletion K) = WithZero.exp (-1 : ℤ) := by

  set π : v.adicCompletionIntegers K := ⟨(uniformizerUnit K v : v.adicCompletion K), by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, valued_uniformizerUnit]
    exact le_of_lt (WithZero.exp_lt_exp.mpr (by norm_num))⟩ with hπ
  have hπv : Valued.v (π : v.adicCompletion K) = WithZero.exp (-1 : ℤ) := valued_uniformizerUnit K v

  have hmax : IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) = Ideal.span {ϖ} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ
  have hunit : ∀ x : v.adicCompletionIntegers K, IsUnit x ↔ Valued.v (x : v.adicCompletion K) = 1 :=
    fun x => Valuation.Integers.isUnit_iff_valuation_eq_one (HeightOneSpectrum.adicCompletionIntegers.integers K v)
  have hπmem : π ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, hunit, hπv]
    exact ne_of_lt (WithZero.exp_lt_exp.mpr (by norm_num))
  rw [hmax, Ideal.mem_span_singleton] at hπmem
  obtain ⟨c, hc⟩ := hπmem
  have hcv : Valued.v (c : v.adicCompletion K) ≤ 1 := c.2
  have hϖv1 : Valued.v (ϖ : v.adicCompletion K) ≤ 1 := ϖ.2
  have hϖnu : ¬ IsUnit ϖ := hϖ.not_isUnit
  rw [hunit] at hϖnu
  have hprod : Valued.v (ϖ : v.adicCompletion K) * Valued.v (c : v.adicCompletion K) = WithZero.exp (-1 : ℤ) := by
    rw [← map_mul, ← hπv]
    congr 1
    exact_mod_cast hc.symm
  have hϖ0 : Valued.v (ϖ : v.adicCompletion K) ≠ 0 := by
    intro h; rw [h, zero_mul] at hprod; exact WithZero.exp_ne_zero hprod.symm

  obtain ⟨n, hn⟩ : ∃ n : ℤ, Valued.v (ϖ : v.adicCompletion K) = WithZero.exp n :=
    ⟨WithZero.log (Valued.v (ϖ : v.adicCompletion K)), (WithZero.exp_log hϖ0).symm⟩
  rw [hn] at hprod hϖv1 hϖnu ⊢
  have hle : WithZero.exp (-1 : ℤ) ≤ WithZero.exp n := by
    rw [← hprod]
    exact mul_le_of_le_one_right' hcv
  have hlt : WithZero.exp n < WithZero.exp (0 : ℤ) := by
    rw [WithZero.exp_zero]; exact lt_of_le_of_ne hϖv1 hϖnu
  rw [WithZero.exp_le_exp] at hle
  rw [WithZero.exp_lt_exp] at hlt
  congr 1
  omega

theorem exists_unit_mul_zpow_ord (v : HeightOneSpectrum (𝓞 K)) (ϖ : v.adicCompletionIntegers K)
    (hϖ : Irreducible ϖ) (w : (AdeleRing (𝓞 K) K)ˣ) :
    ∃ ε : v.adicCompletion K, Valued.v ε = 1 ∧
      ((w : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v =
        ε * (ϖ : v.adicCompletion K) ^ NumberField.Idele.ord K v w := by
  have hϖv := valued_irreducible K v ϖ hϖ
  have hϖ0 : (ϖ : v.adicCompletion K) ≠ 0 := by
    intro h; rw [h, map_zero] at hϖv; exact WithZero.exp_ne_zero hϖv.symm
  refine ⟨((w : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v *
    ((ϖ : v.adicCompletion K) ^ NumberField.Idele.ord K v w)⁻¹, ?_, ?_⟩
  · rw [map_mul, map_inv₀, map_zpow₀, hϖv, NumberField.Idele.valued_snd_eq_exp_neg_ord,
      ← WithZero.exp_zsmul, ← WithZero.exp_neg, ← WithZero.exp_add, ← WithZero.exp_zero]
    congr 1
    simp
  · rw [inv_mul_cancel_right₀ (zpow_ne_zero _ hϖ0)]

theorem ord_eq_zero_iff_norm (v : HeightOneSpectrum (𝓞 K)) (w : (AdeleRing (𝓞 K) K)ˣ) :
    NumberField.Idele.ord K v w = 0 ↔ ‖((w : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v‖ = 1 := by
  rw [norm_eq_one_iff_valued, NumberField.Idele.valued_snd_eq_exp_neg_ord, ← WithZero.exp_zero,
    WithZero.exp_inj]
  omega

theorem mem_unitIdelesOutside_iff_norm (S : Set (HeightOneSpectrum (𝓞 K))) (w : (AdeleRing (𝓞 K) K)ˣ) :
    w ∈ NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K S ↔
      ∀ v ∉ S, ‖((w : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v‖ = 1 := by
  rw [NumberField.AdeleRing.mem_unitIdelesOutside_iff, IsDedekindDomain.FiniteAdeleRing.mem_unitIdelesOutside_iff]
  refine forall₂_congr fun v _ => ?_
  rw [IsDedekindDomain.FiniteAdeleRing.integer_and_inv_integer_iff_valuation_eq_one, norm_eq_one_iff_valued]
  rfl

variable (u : Kˣ)

noncomputable def gammaPrime (w : (AdeleRing (𝓞 K) K)ˣ) : GL (Fin 2) (AdeleRing (𝓞 K) K) :=
  AutomorphicForm.centralScalar (𝓞 K) K w *
    diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1

theorem gammaPrime_def (w : (AdeleRing (𝓞 K) K)ˣ) : gammaPrime K u w =
    AutomorphicForm.centralScalar (𝓞 K) K w *
      diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1 := rfl

theorem coe_gammaPrime (w : (AdeleRing (𝓞 K) K)ˣ) :
    ((gammaPrime K u w : GL (Fin 2) (AdeleRing (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) =
      !![(w : AdeleRing (𝓞 K) K) * algebraMap K (AdeleRing (𝓞 K) K) (u : K), 0; 0, (w : AdeleRing (𝓞 K) K)] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gammaPrime, AutomorphicForm.centralScalar, diagUnits2, Matrix.GeneralLinearGroup.scalar,
      Matrix.mul_apply, Fin.sum_univ_two]

theorem coe_finComponent_gammaPrime (w : (AdeleRing (𝓞 K) K)ˣ) (v : HeightOneSpectrum (𝓞 K)) :
    ((finComponent (𝓞 K) K v (glFin (𝓞 K) K (gammaPrime K u w)) : GL (Fin 2) (v.adicCompletion K)) :
        Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
      Matrix.diagonal ![((w : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v *
          algebraMap K (v.adicCompletion K) (u : K),
        ((w : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v] := by
  ext i j
  have h : ((finComponent (𝓞 K) K v (glFin (𝓞 K) K (gammaPrime K u w)) : GL (Fin 2) (v.adicCompletion K)) :
        Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j
      = ((((gammaPrime K u w : GL (Fin 2) (AdeleRing (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j).2 :
          FiniteAdeleRing (𝓞 K) K) v := rfl
  rw [h, coe_gammaPrime]
  fin_cases i <;> fin_cases j
  · simp [Matrix.diagonal]
    rfl
  · simp [Matrix.diagonal]
    rfl
  · simp [Matrix.diagonal]
    rfl
  · simp [Matrix.diagonal]

theorem coe_centralScalar (w : (AdeleRing (𝓞 K) K)ˣ) :
    ((AutomorphicForm.centralScalar (𝓞 K) K w : GL (Fin 2) (AdeleRing (𝓞 K) K)) :
        Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) = (w : AdeleRing (𝓞 K) K) • 1 := by
  show Matrix.scalar (Fin 2) (w : AdeleRing (𝓞 K) K) = _
  rw [Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]

theorem centralScalar_comm (w : (AdeleRing (𝓞 K) K)ˣ) (g : GL (Fin 2) (AdeleRing (𝓞 K) K)) :
    AutomorphicForm.centralScalar (𝓞 K) K w * g = g * AutomorphicForm.centralScalar (𝓞 K) K w := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_centralScalar, smul_mul_assoc, one_mul, mul_smul_comm, mul_one]

theorem centralScalar_mul_gammaPrime (w₁ w₂ : (AdeleRing (𝓞 K) K)ˣ) :
    AutomorphicForm.centralScalar (𝓞 K) K w₁ * gammaPrime K u w₂ = gammaPrime K u (w₁ * w₂) := by
  rw [gammaPrime_def, gammaPrime_def, map_mul, mul_assoc]

variable {K} in
theorem isRegularSemisimple_map {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (g : GL (Fin 2) R) (hg : AutomorphicForm.IsRegularSemisimple g) :
    AutomorphicForm.IsRegularSemisimple (Matrix.GeneralLinearGroup.map φ g) := by
  unfold AutomorphicForm.IsRegularSemisimple at hg ⊢
  have hc : ((Matrix.GeneralLinearGroup.map φ g : GL (Fin 2) S) : Matrix (Fin 2) (Fin 2) S) =
      φ.mapMatrix (g : Matrix (Fin 2) (Fin 2) R) := rfl
  rw [hc, ← RingHom.map_det]
  have htr : (φ.mapMatrix (g : Matrix (Fin 2) (Fin 2) R)).trace = φ (g : Matrix (Fin 2) (Fin 2) R).trace := by
    rw [Matrix.trace_fin_two, Matrix.trace_fin_two, map_add]; rfl
  rw [htr, ← map_pow, ← map_ofNat φ 4, ← map_mul, ← map_sub]
  exact hg.map φ

theorem isRegularSemisimple_gammaPrime (hu1 : (u : K) ≠ 1) (w : (AdeleRing (𝓞 K) K)ˣ) :
    AutomorphicForm.IsRegularSemisimple (gammaPrime K u w) := by
  unfold AutomorphicForm.IsRegularSemisimple
  rw [Matrix.trace_fin_two, Matrix.det_fin_two, coe_gammaPrime]
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, Matrix.empty_val']
  have hunit : IsUnit ((w : AdeleRing (𝓞 K) K) * (algebraMap K (AdeleRing (𝓞 K) K) (u : K) - 1)) := by
    refine (Units.isUnit w).mul ?_
    rw [← map_one (algebraMap K (AdeleRing (𝓞 K) K)), ← map_sub]
    exact (IsUnit.mk0 _ (sub_ne_zero.mpr hu1)).map _
  have heq : ((w : AdeleRing (𝓞 K) K) * algebraMap K (AdeleRing (𝓞 K) K) (u : K) + (w : AdeleRing (𝓞 K) K)) ^ 2 -
      4 * ((w : AdeleRing (𝓞 K) K) * algebraMap K (AdeleRing (𝓞 K) K) (u : K) * (w : AdeleRing (𝓞 K) K) - 0 * 0) =
      ((w : AdeleRing (𝓞 K) K) * (algebraMap K (AdeleRing (𝓞 K) K) (u : K) - 1)) ^ 2 := by ring
  rw [heq]
  exact hunit.pow 2

theorem isRegularSemisimple_glArch_gammaPrime (hu1 : (u : K) ≠ 1) (w : (AdeleRing (𝓞 K) K)ˣ) :
    AutomorphicForm.IsRegularSemisimple (glArch (𝓞 K) K (gammaPrime K u w)) :=
  isRegularSemisimple_map _ _ (isRegularSemisimple_gammaPrime K u hu1 w)

theorem isRegularSemisimple_finComponent_gammaPrime (hu1 : (u : K) ≠ 1) (w : (AdeleRing (𝓞 K) K)ˣ)
    (v : HeightOneSpectrum (𝓞 K)) :
    AutomorphicForm.IsRegularSemisimple (finComponent (𝓞 K) K v (glFin (𝓞 K) K (gammaPrime K u w))) :=
  isRegularSemisimple_map _ _ (isRegularSemisimple_map _ _ (isRegularSemisimple_gammaPrime K u hu1 w))

theorem glArch_gammaPrime_partAt (S : Finset (HeightOneSpectrum (𝓞 K))) (w : (AdeleRing (𝓞 K) K)ˣ) :
    glArch (𝓞 K) K (gammaPrime K u (NumberField.Idele.partAt K S w)) = glArch (𝓞 K) K (gammaPrime K u w) := by
  apply Units.ext
  ext i j
  show (((gammaPrime K u (NumberField.Idele.partAt K S w) : GL (Fin 2) (AdeleRing (𝓞 K) K)) :
      Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j).1 =
    (((gammaPrime K u w : GL (Fin 2) (AdeleRing (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j).1
  rw [coe_gammaPrime, coe_gammaPrime]
  fin_cases i <;> fin_cases j <;> simp <;> rfl

theorem exists_measure_transport (v : HeightOneSpectrum (𝓞 K)) (g₀ t : GL (Fin 2) (v.adicCompletion K))
    (hZ : AutomorphicForm.localCentralizer K v g₀ = AutomorphicForm.localCentralizer K v t)
    (τ : @Measure (AutomorphicForm.localCentralizer K v g₀) (AutomorphicForm.localCentralizerBorel K v g₀))
    (hτ : @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.localCentralizerBorel K v g₀) τ)
    (hτ1 : τ (Subtype.val ⁻¹' AutomorphicForm.localIntegralSet K v) = 1) :
    ∃ τ' : @Measure (AutomorphicForm.localCentralizer K v t) (AutomorphicForm.localCentralizerBorel K v t),
      @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.localCentralizerBorel K v t) τ' ∧
      τ' (Subtype.val ⁻¹' AutomorphicForm.localIntegralSet K v) = 1 ∧
      ∀ (w : GL (Fin 2) (v.adicCompletion K) → ℝ) (x : GL (Fin 2) (v.adicCompletion K)),
        ∫ s, w ((s : GL (Fin 2) (v.adicCompletion K)) * x) ∂τ' =
          ∫ s, w ((s : GL (Fin 2) (v.adicCompletion K)) * x) ∂τ := by
  letI := AutomorphicForm.localCentralizerBorel K v g₀
  letI := AutomorphicForm.localCentralizerBorel K v t
  haveI : BorelSpace (AutomorphicForm.localCentralizer K v g₀) := ⟨rfl⟩
  haveI : BorelSpace (AutomorphicForm.localCentralizer K v t) := ⟨rfl⟩

  let e : AutomorphicForm.localCentralizer K v g₀ ≃ₜ* AutomorphicForm.localCentralizer K v t :=
    { MulEquiv.subgroupCongr hZ with
      continuous_toFun := continuous_subtype_val.subtype_mk _
      continuous_invFun := continuous_subtype_val.subtype_mk _ }
  set me : AutomorphicForm.localCentralizer K v g₀ ≃ᵐ AutomorphicForm.localCentralizer K v t :=
    e.toHomeomorph.toMeasurableEquiv with hme
  have hmap : Measure.map e τ = Measure.map me τ := rfl
  refine ⟨Measure.map me τ, hmap ▸ e.isHaarMeasure_map τ, ?_, ?_⟩
  · rw [me.map_apply]
    exact hτ1
  · intro w x
    exact integral_map_equiv me (fun s => w ((s : GL (Fin 2) (v.adicCompletion K)) * x))

theorem isOrbitalIntegralOn_transport
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ]
    (γ₁ γ₂ : GL (Fin 2) (AdeleRing (𝓞 K) K))
    (τ₁ : Measure (Subgroup.centralizer ({γ₁} : Set (GL (Fin 2) (AdeleRing (𝓞 K) K)))))
    (τ₂ : Measure (Subgroup.centralizer ({γ₂} : Set (GL (Fin 2) (AdeleRing (𝓞 K) K)))))
    (C : ℝ) (ρ : Measure ((AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ))
    (h₁ : ∀ g : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ,
      ∫ t : Subgroup.centralizer ({γ₁} : Set (GL (Fin 2) (AdeleRing (𝓞 K) K))),
          g (t : GL (Fin 2) (AdeleRing (𝓞 K) K)) ∂τ₁ =
        C * ∫ p : (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ, g (diagUnits2 p.1 p.2) ∂ρ)
    (h₂ : ∀ g : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ,
      ∫ t : Subgroup.centralizer ({γ₂} : Set (GL (Fin 2) (AdeleRing (𝓞 K) K))),
          g (t : GL (Fin 2) (AdeleRing (𝓞 K) K)) ∂τ₂ =
        C * ∫ p : (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ, g (diagUnits2 p.1 p.2) ∂ρ)
    (f₁ f₂ : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ)
    (hf : ∀ x : GL (Fin 2) (AdeleRing (𝓞 K) K), f₁ (x⁻¹ * γ₁ * x) = f₂ (x⁻¹ * γ₂ * x))
    (I : ℂ) (hI : AutomorphicForm.IsOrbitalIntegralOn (AdeleRing (𝓞 K) K) (adelicGLHaar (Fin 2) (𝓞 K) K) γ₁ τ₁ f₁ I) :
    AutomorphicForm.IsOrbitalIntegralOn (AdeleRing (𝓞 K) K) (adelicGLHaar (Fin 2) (𝓞 K) K) γ₂ τ₂ f₂ I := by
  obtain ⟨w, ⟨hw0, hwm, hwc, hw1⟩, hIeq⟩ := hI
  refine ⟨w, ⟨hw0, hwm, hwc, fun x hx => ?_⟩, ?_⟩
  · have h := hw1 x (by rwa [hf])
    have key : ((∫ t : Subgroup.centralizer ({γ₂} : Set (GL (Fin 2) (AdeleRing (𝓞 K) K))),
        w ((t : GL (Fin 2) (AdeleRing (𝓞 K) K)) * x) ∂τ₂ : ℝ) : ℂ) =
        ((∫ t : Subgroup.centralizer ({γ₁} : Set (GL (Fin 2) (AdeleRing (𝓞 K) K))),
          w ((t : GL (Fin 2) (AdeleRing (𝓞 K) K)) * x) ∂τ₁ : ℝ) : ℂ) := by
      rw [← integral_complex_ofReal, ← integral_complex_ofReal, h₁ (fun y => (w (y * x) : ℂ)),
        h₂ (fun y => (w (y * x) : ℂ))]
    rw [h] at key
    exact_mod_cast key
  · rw [hIeq]
    simp_rw [hf]

theorem coe_finComponent_glFin_centralScalar (m : (AdeleRing (𝓞 K) K)ˣ) (v : HeightOneSpectrum (𝓞 K)) :
    ((finComponent (𝓞 K) K v (glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K m)) :
        GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
      ((m : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v • (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) := by
  ext i j
  show ((((AutomorphicForm.centralScalar (𝓞 K) K m : GL (Fin 2) (AdeleRing (𝓞 K) K)) :
      Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j).2 : FiniteAdeleRing (𝓞 K) K) v = _
  rw [coe_centralScalar]
  fin_cases i <;> fin_cases j <;> simp <;> rfl

theorem glArch_centralScalar_eq_one (m : (AdeleRing (𝓞 K) K)ˣ) (hm1 : (m : AdeleRing (𝓞 K) K).1 = 1) :
    glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K m) = 1 := by
  apply Units.ext
  ext i j
  show (((AutomorphicForm.centralScalar (𝓞 K) K m : GL (Fin 2) (AdeleRing (𝓞 K) K)) :
      Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j).1 = (1 : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) i j
  rw [coe_centralScalar]
  fin_cases i <;> fin_cases j <;> simp [hm1] <;> rfl

theorem localCentralizer_eq_of_coe_eq_smul (v : HeightOneSpectrum (𝓞 K)) (g g' : GL (Fin 2) (v.adicCompletion K))
    (a : v.adicCompletion K) (ha : a ≠ 0)
    (h : (g' : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) = a • (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))) :
    AutomorphicForm.localCentralizer K v g = AutomorphicForm.localCentralizer K v g' := by
  ext x
  simp only [AutomorphicForm.localCentralizer, Subgroup.mem_centralizer_iff, Set.mem_singleton_iff, forall_eq]
  constructor
  · intro hx
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, h, Matrix.mul_smul, Matrix.smul_mul, ← Units.val_mul, hx, Units.val_mul]
  · intro hx
    apply Units.ext
    have hx' := congrArg Units.val hx
    rw [Units.val_mul, Units.val_mul, h, Matrix.mul_smul, Matrix.smul_mul] at hx'
    exact smul_right_injective _ ha hx'

theorem mul_mem_localIntegralSet_iff_of_coe_eq_smul (v : HeightOneSpectrum (𝓞 K))
    (c : GL (Fin 2) (v.adicCompletion K)) (a : v.adicCompletion K) (ha : ‖a‖ = 1)
    (hc : (c : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) = a • 1) (y : GL (Fin 2) (v.adicCompletion K)) :
    c * y ∈ AutomorphicForm.localIntegralSet K v ↔ y ∈ AutomorphicForm.localIntegralSet K v := by
  have ha0 : a ≠ 0 := by intro h; rw [h, norm_zero] at ha; exact zero_ne_one ha
  have hcinv : ((c⁻¹ : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) = a⁻¹ • 1 := by
    rw [Matrix.coe_units_inv, hc]
    exact Matrix.inv_eq_left_inv (by rw [smul_mul_assoc, one_mul, smul_smul, inv_mul_cancel₀ ha0, one_smul])
  have hint : ∀ b : v.adicCompletion K, ‖b‖ = 1 → ∀ x : v.adicCompletion K,
      (x ∈ v.adicCompletionIntegers K ↔ b * x ∈ v.adicCompletionIntegers K) := by
    intro b hb x
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, HeightOneSpectrum.mem_adicCompletionIntegers,
      ← Valued.toNormedField.norm_le_one_iff, ← Valued.toNormedField.norm_le_one_iff, norm_mul, hb, one_mul]
  have hainv : ‖a⁻¹‖ = 1 := by rw [norm_inv, ha, inv_one]
  rw [AutomorphicForm.mem_localIntegralSet, AutomorphicForm.mem_localIntegralSet]
  have e1 : ∀ i j, ((c * y : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j =
      a * (y : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j := by
    intro i j; rw [Units.val_mul, hc, smul_mul_assoc, one_mul, Matrix.smul_apply, smul_eq_mul]
  have e2 : ∀ i j, (((c * y)⁻¹ : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j =
      a⁻¹ * ((y⁻¹ : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j := by
    intro i j; rw [mul_inv_rev, Units.val_mul, hcinv, mul_smul_comm, mul_one, Matrix.smul_apply, smul_eq_mul]
  simp_rw [e1, e2]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun i j => (hint a ha _).mpr (h1 i j), fun i j => (hint a⁻¹ hainv _).mpr (h2 i j)⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun i j => (hint a ha _).mp (h1 i j), fun i j => (hint a⁻¹ hainv _).mp (h2 i j)⟩

theorem diagonal_mem_localIntegralSet (v : HeightOneSpectrum (𝓞 K)) (g : GL (Fin 2) (v.adicCompletion K))
    (a b : v.adicCompletion K) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hg : (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) = Matrix.diagonal ![a, b]) :
    g ∈ AutomorphicForm.localIntegralSet K v := by
  have ha0 : a ≠ 0 := by intro h; rw [h, norm_zero] at ha; exact zero_ne_one ha
  have hb0 : b ≠ 0 := by intro h; rw [h, norm_zero] at hb; exact zero_ne_one hb
  have hint : ∀ x : v.adicCompletion K, ‖x‖ ≤ 1 → x ∈ v.adicCompletionIntegers K := fun x hx => by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers]; exact Valued.toNormedField.norm_le_one_iff.mp hx
  have hginv : ((g⁻¹ : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
      Matrix.diagonal ![a⁻¹, b⁻¹] := by
    rw [Matrix.coe_units_inv, hg]
    refine Matrix.inv_eq_left_inv ?_
    rw [Matrix.diagonal_mul_diagonal]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal, ha0, hb0]
  rw [AutomorphicForm.mem_localIntegralSet, hginv]
  simp_rw [hg]
  constructor
  · intro i j
    fin_cases i <;> fin_cases j
    · simpa [Matrix.diagonal] using hint a ha.le
    · simp [Matrix.diagonal]
    · simp [Matrix.diagonal]
    · simpa [Matrix.diagonal] using hint b hb.le
  · intro i j
    fin_cases i <;> fin_cases j
    · simpa [Matrix.diagonal] using hint a⁻¹ (by rw [norm_inv, ha, inv_one])
    · simp [Matrix.diagonal]
    · simp [Matrix.diagonal]
    · simpa [Matrix.diagonal] using hint b⁻¹ (by rw [norm_inv, hb, inv_one])

theorem isUnitFactorization_translate (S' : Finset (HeightOneSpectrum (𝓞 K)))
    (f : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ) (fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ)
    (ff : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) → ℂ)
    (fS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K) → ℂ)
    (hf : AutomorphicForm.IsUnitFactorization K S' f fa ff fS)
    (m : (AdeleRing (𝓞 K) K)ˣ) (hm1 : (m : AdeleRing (𝓞 K) K).1 = 1)
    (hmU : ∀ v ∉ S', ‖((m : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v‖ = 1) :
    AutomorphicForm.IsUnitFactorization K S' (fun g => f (AutomorphicForm.centralScalar (𝓞 K) K m * g)) fa
      (fun h => ff (glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K m) * h))
      (fun v y => fS v (finComponent (𝓞 K) K v (glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K m)) * y)) := by
  obtain ⟨hfa, ⟨hffl, hffc⟩, hfS, hprod, hzero, hfac⟩ := hf
  set cm := glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K m) with hcm
  have hcv : ∀ v, ((finComponent (𝓞 K) K v cm : GL (Fin 2) (v.adicCompletion K)) :
      Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
      ((m : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v • (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) :=
    fun v => coe_finComponent_glFin_centralScalar K m v
  have hmem : ∀ v ∉ S', ∀ y : GL (Fin 2) (v.adicCompletion K),
      finComponent (𝓞 K) K v cm * y ∈ AutomorphicForm.localIntegralSet K v ↔
        y ∈ AutomorphicForm.localIntegralSet K v :=
    fun v hv y => mul_mem_localIntegralSet_iff_of_coe_eq_smul K v _ _ (hmU v hv) (hcv v) y
  refine ⟨hfa, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · exact hffl.comp_continuous (continuous_const_mul _)
  · exact hffc.comp_homeomorph (Homeomorph.mulLeft cm)
  · intro v hv
    obtain ⟨hl, hc⟩ := hfS v hv
    exact ⟨hl.comp_continuous (continuous_const_mul _), hc.comp_homeomorph (Homeomorph.mulLeft _)⟩
  · intro h hh
    have hh' : ∀ v ∉ S', finComponent (𝓞 K) K v (cm * h) ∈ AutomorphicForm.localIntegralSet K v := by
      intro v hv; rw [map_mul]; exact (hmem v hv _).mpr (hh v hv)
    show ff (cm * h) = ∏ v ∈ S', fS v (finComponent (𝓞 K) K v cm * finComponent (𝓞 K) K v h)
    rw [hprod (cm * h) hh']
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [map_mul]
  · intro h ⟨v, hv, hhv⟩
    apply hzero (cm * h)
    exact ⟨v, hv, fun hc => hhv (by rw [map_mul] at hc; exact (hmem v hv _).mp hc)⟩
  · intro g
    show f (AutomorphicForm.centralScalar (𝓞 K) K m * g) = fa (glArch (𝓞 K) K g) * ff (cm * glFin (𝓞 K) K g)
    rw [hfac, map_mul, map_mul, glArch_centralScalar_eq_one K m hm1, one_mul]

theorem isRegularSemisimple_of_coe_eq_smul (v : HeightOneSpectrum (𝓞 K)) (g g' : GL (Fin 2) (v.adicCompletion K))
    (hg : AutomorphicForm.IsRegularSemisimple g) (a : v.adicCompletion K) (ha : a ≠ 0)
    (h : (g' : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) = a • (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))) :
    AutomorphicForm.IsRegularSemisimple g' := by
  unfold AutomorphicForm.IsRegularSemisimple at hg ⊢
  have h' : Matrix.trace (g' : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) ^ 2 -
      4 * Matrix.det (g' : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
      a ^ 2 * (Matrix.trace (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) ^ 2 -
        4 * Matrix.det (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))) := by
    rw [h, Matrix.trace_smul, Matrix.det_smul, Fintype.card_fin, smul_eq_mul]
    ring
  rw [h']
  exact (isUnit_iff_ne_zero.mpr (pow_ne_zero 2 ha)).mul hg

theorem finite_mulSupport_norm_snd (a : (AdeleRing (𝓞 K) K)ˣ) :
    (Function.mulSupport fun v : HeightOneSpectrum (𝓞 K) => ‖((a : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v‖).Finite := by
  have h1 : ∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite,
      ((a : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v ∈ v.adicCompletionIntegers K :=
    ((a : AdeleRing (𝓞 K) K).2).2
  have h2 : ∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite,
      (((a⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v ∈
        v.adicCompletionIntegers K :=
    (((a⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2).2
  have h := Filter.eventually_cofinite.mp (h1.and h2)
  refine h.subset fun v hv => ?_
  simp only [Set.mem_setOf_eq]
  intro hcon
  obtain ⟨hi, hi'⟩ := hcon
  apply hv
  have hle : ‖((a : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v‖ ≤ 1 :=
    Valued.toNormedField.norm_le_one_iff.mpr hi
  have hle' : ‖(((a⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v‖ ≤ 1 :=
    Valued.toNormedField.norm_le_one_iff.mpr hi'
  have hmul : ((a : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v *
      (((a⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v = 1 := by
    have h2 := congrArg (fun x : AdeleRing (𝓞 K) K => (x.2 : FiniteAdeleRing (𝓞 K) K) v) a.mul_inv
    exact h2
  have hnm : ‖((a : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v‖ *
      ‖(((a⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v‖ = 1 := by
    rw [← norm_mul, hmul, norm_one]
  show ‖((a : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v‖ = 1
  nlinarith [norm_nonneg (((a : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v),
    norm_nonneg ((((a⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v)]

theorem snd_apply_mul (a b : (AdeleRing (𝓞 K) K)ˣ) (v : HeightOneSpectrum (𝓞 K)) :
    (((a * b : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v =
      ((a : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v * ((b : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v :=
  rfl

theorem tPlace (v : HeightOneSpectrum (𝓞 K)) (fv : GL (Fin 2) (v.adicCompletion K) → ℂ)
    (hfv : AutomorphicForm.IsLocalTestFn K v fv)
    (hcenv : ∀ c : GL (Fin 2) (v.adicCompletion K),
      (∃ ε : v.adicCompletion K, Valued.v ε = 1 ∧
        (c : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) = ε • (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))) →
      ∀ y : GL (Fin 2) (v.adicCompletion K), fv (c * y) = fv y)
    (gp t c : GL (Fin 2) (v.adicCompletion K)) (hgp : AutomorphicForm.IsRegularSemisimple gp)
    (a ε : v.adicCompletion K) (ha : a ≠ 0) (hε : Valued.v ε = 1)
    (ht : (t : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) = a • (gp : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)))
    (ht01 : (t : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 1 = 0)
    (ht10 : (t : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 0 = 0)
    (hc : (c : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) = (ε * a) • (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)))
    (τ : @Measure (AutomorphicForm.localCentralizer K v gp) (AutomorphicForm.localCentralizerBorel K v gp))
    (hτ : @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.localCentralizerBorel K v gp) τ)
    (hτ1 : τ (Subtype.val ⁻¹' AutomorphicForm.localIntegralSet K v) = 1)
    (τt : @Measure (AutomorphicForm.localCentralizer K v t) (AutomorphicForm.localCentralizerBorel K v t))
    (hτt : @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.localCentralizerBorel K v t) τt)
    (hτt1 : τt (Subtype.val ⁻¹' AutomorphicForm.localIntegralSet K v) = 1)
    (I It : ℂ) (hI : AutomorphicForm.IsOrbitalIntegral K v gp τ (fun y => fv (c * y)) I)
    (hIt : AutomorphicForm.IsOrbitalIntegral K v t τt fv It) : I = It := by
  have key2 : ∀ x : GL (Fin 2) (v.adicCompletion K), fv (c * (x⁻¹ * gp * x)) = fv (x⁻¹ * t * x) := by
    intro x
    set y : GL (Fin 2) (v.adicCompletion K) := x⁻¹ * t * x with hy
    have h1 : ((c * (x⁻¹ * gp * x) : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
        ε • (y : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) := by
      rw [hy, Units.val_mul, hc, smul_mul_assoc, one_mul, Units.val_mul, Units.val_mul, Units.val_mul,
        Units.val_mul, ht, Matrix.mul_smul _ a, Matrix.smul_mul a, smul_smul]
    have hprod : c * (x⁻¹ * gp * x) = (c * (x⁻¹ * gp * x) * y⁻¹) * y := by rw [inv_mul_cancel_right]
    rw [hprod]
    refine hcenv _ ⟨ε, hε, ?_⟩ y
    rw [Units.val_mul, h1, smul_mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hZ := localCentralizer_eq_of_coe_eq_smul K v gp t a ha ht
  obtain ⟨τ', hτ', hτ'1, hτ'int⟩ := exists_measure_transport K v gp t hZ τ hτ hτ1
  have hOrb : AutomorphicForm.IsOrbitalIntegral K v t τ' fv I := by
    obtain ⟨w, ⟨hw0, hwm, hwc, hw1⟩, hIv⟩ := hI
    refine ⟨w, ⟨hw0, hwm, hwc, fun x hx => ?_⟩, ?_⟩
    · rw [hτ'int]
      apply hw1 x
      show fv (c * (x⁻¹ * gp * x)) ≠ 0
      rwa [key2 x]
    · rw [hIv]
      congr 1
      funext x
      show fv (c * (x⁻¹ * gp * x)) * _ = _
      rw [key2 x]
  have hreg : AutomorphicForm.IsRegularSemisimple t := isRegularSemisimple_of_coe_eq_smul K v gp t hgp a ha ht
  exact (AutomorphicForm.eq_of_isOrbitalIntegral_of_isOrbitalIntegral_smul_diagonal_of_forall_centralUnit_mul K v
    t t hreg ht01 ht10 1 (map_one _) (by rw [one_smul]) τt hτt hτt1 τ' hτ' hτ'1 fv hfv hcenv It I hIt hOrb)

theorem perClass_vanish [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (μ : @Measure (GL (Fin 2) (AdeleRing (𝓞 K) K)) (glBorel (Fin 2) (𝓞 K) K))
    (hμ : @Measure.IsHaarMeasure (GL (Fin 2) (AdeleRing (𝓞 K) K)) _ _ (glBorel (Fin 2) (𝓞 K) K) μ)
    (ν : @Measure (GL (Fin 2) (InfiniteAdeleRing K)) (AutomorphicForm.glBorelOf (InfiniteAdeleRing K)))
    (cG : ℝ)
    (hG : ∀ (S : Finset (HeightOneSpectrum (𝓞 K)))
        (f : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ) (fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ)
        (fS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K) → ℂ),
        AEStronglyMeasurable[AutomorphicForm.glBorelOf (InfiniteAdeleRing K)] fa ν →
        (∀ v ∈ S, AEStronglyMeasurable[AutomorphicForm.localGLBorel K v] (fS v)
          (AutomorphicForm.localHaar K v)) →
        (∀ g : GL (Fin 2) (AdeleRing (𝓞 K) K),
          (∀ v ∉ S, AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K g) ∈
              AutomorphicForm.localIntegralSet K v) →
            f g = fa (AdelicLevel.glArch (𝓞 K) K g) *
              ∏ v ∈ S, fS v (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K g))) →
        (∀ g : GL (Fin 2) (AdeleRing (𝓞 K) K),
          (∃ v ∉ S, AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K g) ∉
              AutomorphicForm.localIntegralSet K v) → f g = 0) →
          ∫ g, f g ∂μ = cG * (∫ x, fa x ∂ν) * ∏ v ∈ S, ∫ y, fS v y ∂(AutomorphicForm.localHaar K v))
    (γ : GL (Fin 2) (AdeleRing (𝓞 K) K)) (hγ : AutomorphicForm.IsRegularSemisimple γ)
    (τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (AdeleRing (𝓞 K) K))))
      (AutomorphicForm.centralizerBorel (AdeleRing (𝓞 K) K) γ))
    (hτ : @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.centralizerBorel (AdeleRing (𝓞 K) K) γ) τ)
    (τa : @Measure (Subgroup.centralizer
        ({AdelicLevel.glArch (𝓞 K) K γ} : Set (GL (Fin 2) (InfiniteAdeleRing K))))
      (AutomorphicForm.centralizerBorel (InfiniteAdeleRing K) (AdelicLevel.glArch (𝓞 K) K γ)))
    (hτa : @Measure.IsHaarMeasure _ _ _
      (AutomorphicForm.centralizerBorel (InfiniteAdeleRing K) (AdelicLevel.glArch (𝓞 K) K γ)) τa)
    (τf : ∀ v : HeightOneSpectrum (𝓞 K),
      @Measure (AutomorphicForm.localCentralizer K v
          (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K γ)))
        (AutomorphicForm.localCentralizerBorel K v
          (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K γ))))
    (hτf : ∀ v : HeightOneSpectrum (𝓞 K), @Measure.IsHaarMeasure _ _ _
      (AutomorphicForm.localCentralizerBorel K v
        (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K γ))) (τf v))
    (hτf1 : ∀ v : HeightOneSpectrum (𝓞 K),
      τf v (Subtype.val ⁻¹' AutomorphicForm.localIntegralSet K v) = 1)
    (cT : ℝ) (hcT : 0 < cT)
    (hT : ∀ (S : Finset (HeightOneSpectrum (𝓞 K)))
        (W : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ) (Wa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ)
        (WS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K) → ℂ),
        AEStronglyMeasurable[AutomorphicForm.centralizerBorel (InfiniteAdeleRing K)
          (AdelicLevel.glArch (𝓞 K) K γ)] (fun t => Wa t) τa →
        (∀ v ∈ S, AEStronglyMeasurable[AutomorphicForm.localCentralizerBorel K v
          (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K γ))] (fun t => WS v t) (τf v)) →
        (∀ t : Subgroup.centralizer ({γ} : Set (GL (Fin 2) (AdeleRing (𝓞 K) K))),
          (∀ v ∉ S, AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K t) ∈
              AutomorphicForm.localIntegralSet K v) →
            W t = Wa (AdelicLevel.glArch (𝓞 K) K t) *
              ∏ v ∈ S, WS v (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K t))) →
        (∀ t : Subgroup.centralizer ({γ} : Set (GL (Fin 2) (AdeleRing (𝓞 K) K))),
          (∃ v ∉ S, AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K t) ∉
              AutomorphicForm.localIntegralSet K v) → W t = 0) →
          ∫ t, W t ∂τ = cT * (∫ t, Wa t ∂τa) * ∏ v ∈ S, ∫ t, WS v t ∂(τf v))
    (S T : Finset (HeightOneSpectrum (𝓞 K)))
    (f : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ) (fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ)
    (ff : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) → ℂ)
    (fS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K) → ℂ)
    (hf : AutomorphicForm.IsUnitFactorization K (S ∪ T) f fa ff fS)
    (u : Kˣ) (hu1 : (u : K) ≠ 1) (w : (AdeleRing (𝓞 K) K)ˣ) (hγw : γ = gammaPrime K u w)
    (I : ℂ) (hI : AutomorphicForm.IsOrbitalIntegralOn (AdeleRing (𝓞 K) K) μ γ τ f I)
    (v₀ : HeightOneSpectrum (𝓞 K)) (hv₀ : v₀ ∉ S ∪ T)
    (hbad : ¬ (‖((w : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v₀‖ = 1 ∧
      ‖algebraMap K (v₀.adicCompletion K) (u : K)‖ = 1)) : I = 0 := by
  classical
  subst hγw
  have huv1 : algebraMap K (v₀.adicCompletion K) (u : K) ≠ 1 := by
    intro h; apply hu1
    exact (algebraMap K (v₀.adicCompletion K)).injective (by rw [h, map_one])
  have hE := AutomorphicForm.exists_isOrbitalIntegralOn_adeleRing_eq_mul_prod_of_isUnitFactorization K
    μ hμ ν cG hG (gammaPrime K u w) hγ τ hτ τa hτa τf hτf hτf1 cT hcT hT (S ∪ T) f fa ff fS hf I hI
  rcases hE with ⟨hI0, -⟩ | ⟨S₁, hS₁, Ia, Iv, hIa, hIvS, hIvU, hprodE⟩
  · exact hI0
  · rw [hprodE (insert v₀ S₁) (Finset.subset_insert _ _)]
    have hIv0 : Iv v₀ = 0 := by
      have h := AutomorphicForm.eq_ite_inv_norm_sub_one_of_isOrbitalIntegral_indicator_localIntegralSet_diagonal K v₀
        (((w : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v₀) (algebraMap K (v₀.adicCompletion K) (u : K))
        huv1 _ (coe_finComponent_gammaPrime K u w v₀) (τf v₀) (hτf v₀) (hτf1 v₀) (Iv v₀) (hIvU v₀ hv₀)
      rw [h, if_neg hbad]
    rw [Finset.prod_eq_zero (Finset.mem_insert_self v₀ S₁) hIv0, mul_zero]

theorem perClass_main [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (μ : @Measure (GL (Fin 2) (AdeleRing (𝓞 K) K)) (glBorel (Fin 2) (𝓞 K) K))
    (hμ : @Measure.IsHaarMeasure (GL (Fin 2) (AdeleRing (𝓞 K) K)) _ _ (glBorel (Fin 2) (𝓞 K) K) μ)
    (ν : @Measure (GL (Fin 2) (InfiniteAdeleRing K)) (AutomorphicForm.glBorelOf (InfiniteAdeleRing K)))
    (cG : ℝ)
    (hG : ∀ (S : Finset (HeightOneSpectrum (𝓞 K)))
        (f : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ) (fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ)
        (fS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K) → ℂ),
        AEStronglyMeasurable[AutomorphicForm.glBorelOf (InfiniteAdeleRing K)] fa ν →
        (∀ v ∈ S, AEStronglyMeasurable[AutomorphicForm.localGLBorel K v] (fS v)
          (AutomorphicForm.localHaar K v)) →
        (∀ g : GL (Fin 2) (AdeleRing (𝓞 K) K),
          (∀ v ∉ S, AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K g) ∈
              AutomorphicForm.localIntegralSet K v) →
            f g = fa (AdelicLevel.glArch (𝓞 K) K g) *
              ∏ v ∈ S, fS v (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K g))) →
        (∀ g : GL (Fin 2) (AdeleRing (𝓞 K) K),
          (∃ v ∉ S, AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K g) ∉
              AutomorphicForm.localIntegralSet K v) → f g = 0) →
          ∫ g, f g ∂μ = cG * (∫ x, fa x ∂ν) * ∏ v ∈ S, ∫ y, fS v y ∂(AutomorphicForm.localHaar K v))
    (γ : GL (Fin 2) (AdeleRing (𝓞 K) K)) (hγ : AutomorphicForm.IsRegularSemisimple γ)
    (τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (AdeleRing (𝓞 K) K))))
      (AutomorphicForm.centralizerBorel (AdeleRing (𝓞 K) K) γ))
    (hτ : @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.centralizerBorel (AdeleRing (𝓞 K) K) γ) τ)
    (τa : @Measure (Subgroup.centralizer
        ({AdelicLevel.glArch (𝓞 K) K γ} : Set (GL (Fin 2) (InfiniteAdeleRing K))))
      (AutomorphicForm.centralizerBorel (InfiniteAdeleRing K) (AdelicLevel.glArch (𝓞 K) K γ)))
    (hτa : @Measure.IsHaarMeasure _ _ _
      (AutomorphicForm.centralizerBorel (InfiniteAdeleRing K) (AdelicLevel.glArch (𝓞 K) K γ)) τa)
    (τf : ∀ v : HeightOneSpectrum (𝓞 K),
      @Measure (AutomorphicForm.localCentralizer K v
          (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K γ)))
        (AutomorphicForm.localCentralizerBorel K v
          (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K γ))))
    (hτf : ∀ v : HeightOneSpectrum (𝓞 K), @Measure.IsHaarMeasure _ _ _
      (AutomorphicForm.localCentralizerBorel K v
        (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K γ))) (τf v))
    (hτf1 : ∀ v : HeightOneSpectrum (𝓞 K),
      τf v (Subtype.val ⁻¹' AutomorphicForm.localIntegralSet K v) = 1)
    (cT : ℝ) (hcT : 0 < cT)
    (hT : ∀ (S : Finset (HeightOneSpectrum (𝓞 K)))
        (W : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ) (Wa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ)
        (WS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K) → ℂ),
        AEStronglyMeasurable[AutomorphicForm.centralizerBorel (InfiniteAdeleRing K)
          (AdelicLevel.glArch (𝓞 K) K γ)] (fun t => Wa t) τa →
        (∀ v ∈ S, AEStronglyMeasurable[AutomorphicForm.localCentralizerBorel K v
          (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K γ))] (fun t => WS v t) (τf v)) →
        (∀ t : Subgroup.centralizer ({γ} : Set (GL (Fin 2) (AdeleRing (𝓞 K) K))),
          (∀ v ∉ S, AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K t) ∈
              AutomorphicForm.localIntegralSet K v) →
            W t = Wa (AdelicLevel.glArch (𝓞 K) K t) *
              ∏ v ∈ S, WS v (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K t))) →
        (∀ t : Subgroup.centralizer ({γ} : Set (GL (Fin 2) (AdeleRing (𝓞 K) K))),
          (∃ v ∉ S, AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K t) ∉
              AutomorphicForm.localIntegralSet K v) → W t = 0) →
          ∫ t, W t ∂τ = cT * (∫ t, Wa t ∂τa) * ∏ v ∈ S, ∫ t, WS v t ∂(τf v))
    (hν : @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.glBorelOf (InfiniteAdeleRing K)) ν)
    (S T : Finset (HeightOneSpectrum (𝓞 K))) (hTS : Disjoint T S)
    (f : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ) (fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ)
    (ff : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) → ℂ)
    (fS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K) → ℂ)
    (hf : AutomorphicForm.IsUnitFactorization K (S ∪ T) f fa ff fS)
    (hcen : ∀ v ∈ T, ∀ c : GL (Fin 2) (v.adicCompletion K),
      (∃ ε : v.adicCompletion K, Valued.v ε = 1 ∧
        (c : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) = ε • (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))) →
      ∀ y : GL (Fin 2) (v.adicCompletion K), fS v (c * y) = fS v y)
    (u : Kˣ) (hu1 : (u : K) ≠ 1) (p m z' : (AdeleRing (𝓞 K) K)ˣ) (hγp : γ = gammaPrime K u p)
    (hpO : ∀ v ∉ S, ((p : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v = 1)
    (hm1 : (m : AdeleRing (𝓞 K) K).1 = 1)
    (hmS : ∀ v ∈ S, ((m : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v = 1)
    (hmO : ∀ v ∉ S, ((m : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v =
      ((z' : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v)
    (hzU : ∀ v ∉ S ∪ T, ‖((z' : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v‖ = 1)
    (huv : ∀ v ∉ S ∪ T, ‖algebraMap K (v.adicCompletion K) (u : K)‖ = 1)
    (IAp : ℂ) (hIAp : AutomorphicForm.IsOrbitalIntegralOn (InfiniteAdeleRing K) ν (AdelicLevel.glArch (𝓞 K) K γ) τa fa IAp)
    (IFp : HeightOneSpectrum (𝓞 K) → ℂ)
    (hIFp : ∀ v ∈ S, AutomorphicForm.IsOrbitalIntegral K v
      (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K γ)) (τf v) (fS v) (IFp v))
    (ϖT : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletionIntegers K) (hϖT : ∀ v ∈ T, Irreducible (ϖT v))
    (tT : ∀ v : HeightOneSpectrum (𝓞 K), ℤ → GL (Fin 2) (v.adicCompletion K))
    (htT : ∀ v ∈ T, ∀ e : ℤ, (tT v e : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
      Matrix.diagonal ![(ϖT v : v.adicCompletion K) ^ e * algebraMap K (v.adicCompletion K) (u : K),
        (ϖT v : v.adicCompletion K) ^ e])
    (τT : ∀ (v : HeightOneSpectrum (𝓞 K)) (e : ℤ),
      @Measure (AutomorphicForm.localCentralizer K v (tT v e)) (AutomorphicForm.localCentralizerBorel K v (tT v e)))
    (hτT : ∀ v e, @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.localCentralizerBorel K v (tT v e)) (τT v e))
    (hτT1 : ∀ v e, τT v e (Subtype.val ⁻¹' AutomorphicForm.localIntegralSet K v) = 1)
    (IT : HeightOneSpectrum (𝓞 K) → ℤ → ℂ)
    (hIT : ∀ v ∈ T, ∀ e : ℤ, AutomorphicForm.IsOrbitalIntegral K v (tT v e) (τT v e) (fS v) (IT v e))
    (I : ℂ)
    (hI : AutomorphicForm.IsOrbitalIntegralOn (AdeleRing (𝓞 K) K) μ γ τ
      (fun g => f (AutomorphicForm.centralScalar (𝓞 K) K m * g)) I) :
    I = ((cG * cT⁻¹ : ℝ) : ℂ) *
      (((∏ᶠ v : HeightOneSpectrum (𝓞 K),
          (if v ∈ S ∪ T then (1 : ℝ) else ‖algebraMap K (v.adicCompletion K) (u : K) - 1‖))⁻¹ : ℝ) : ℂ) *
      ((IAp * ∏ v ∈ S, IFp v) * ∏ v ∈ T, IT v (NumberField.Idele.ord K v z')) := by
  classical
  subst hγp

  have huv1 : ∀ v : HeightOneSpectrum (𝓞 K), algebraMap K (v.adicCompletion K) (u : K) ≠ 1 := by
    intro v h; apply hu1
    exact (algebraMap K (v.adicCompletion K)).injective (by rw [h, map_one])
  have hmU : ∀ v ∉ S ∪ T, ‖((m : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v‖ = 1 := by
    intro v hv
    rw [hmO v (fun h => hv (Finset.mem_union_left T h))]
    exact hzU v hv
  have hγ'v := coe_finComponent_gammaPrime K u p

  have hcmv : ∀ v, ((finComponent (𝓞 K) K v (glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K m)) :
      GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
      ((m : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v • (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) :=
    fun v => coe_finComponent_glFin_centralScalar K m v
  have hcm1 : ∀ v ∈ S, finComponent (𝓞 K) K v (glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K m)) = 1 :=
    fun v hv => Units.ext (by rw [hcmv, hmS v hv, one_smul]; rfl)
  have hfm := isUnitFactorization_translate K (S ∪ T) f fa ff fS hf m hm1 hmU
  have hE := AutomorphicForm.exists_isOrbitalIntegralOn_adeleRing_eq_mul_prod_of_isUnitFactorization K
    μ hμ ν cG hG (gammaPrime K u p) hγ τ hτ τa hτa τf hτf hτf1 cT hcT hT (S ∪ T)
    (fun g => f (AutomorphicForm.centralScalar (𝓞 K) K m * g)) fa
    (fun h => ff (glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K m) * h))
    (fun v y => fS v (finComponent (𝓞 K) K v (glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K m)) * y))
    hfm I hI

  have hϖ0 : ∀ v ∈ T, ((ϖT v : v.adicCompletionIntegers K) : v.adicCompletion K) ≠ 0 := by
    intro v hvT h0
    have h := valued_irreducible K v (ϖT v) (hϖT v hvT)
    rw [h0, map_zero] at h
    exact WithZero.exp_ne_zero h.symm
  have hgpM : ∀ v ∉ S, ((finComponent (𝓞 K) K v (glFin (𝓞 K) K (gammaPrime K u p)) : GL (Fin 2) (v.adicCompletion K)) :
      Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) = Matrix.diagonal ![algebraMap K (v.adicCompletion K) (u : K), 1] := by
    intro v hvS; rw [hγ'v v, hpO v hvS, one_mul]
  have htM : ∀ v ∈ T, ((tT v (NumberField.Idele.ord K v z') : GL (Fin 2) (v.adicCompletion K)) :
      Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
      ((ϖT v : v.adicCompletionIntegers K) : v.adicCompletion K) ^ NumberField.Idele.ord K v z' •
        ((finComponent (𝓞 K) K v (glFin (𝓞 K) K (gammaPrime K u p)) : GL (Fin 2) (v.adicCompletion K)) :
          Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) := by
    intro v hvT
    rw [htT v hvT, hgpM v (Finset.disjoint_left.mp hTS hvT)]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal]

  have hTid : ∀ v ∈ T, ∀ (J Jt : ℂ),
      AutomorphicForm.IsOrbitalIntegral K v (finComponent (𝓞 K) K v (glFin (𝓞 K) K (gammaPrime K u p))) (τf v)
        (fun y => fS v (finComponent (𝓞 K) K v (glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K m)) * y)) J →
      AutomorphicForm.IsOrbitalIntegral K v (tT v (NumberField.Idele.ord K v z')) (τT v (NumberField.Idele.ord K v z'))
        (fS v) Jt → J = Jt := by
    intro v hvT J Jt hJ hJt
    have hvS : v ∉ S := Finset.disjoint_left.mp hTS hvT
    have hvST : v ∈ S ∪ T := Finset.mem_union_right S hvT
    obtain ⟨ε, hε, hzε⟩ := exists_unit_mul_zpow_ord K v (ϖT v) (hϖT v hvT) z'
    have h01 : ((tT v (NumberField.Idele.ord K v z') : GL (Fin 2) (v.adicCompletion K)) :
        Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 1 = 0 := by
      rw [htT v hvT]; simp
    have h10 : ((tT v (NumberField.Idele.ord K v z') : GL (Fin 2) (v.adicCompletion K)) :
        Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 0 = 0 := by
      rw [htT v hvT]; simp
    refine tPlace K v (fS v) (hf.2.2.1 v hvST) (hcen v hvT) _ _ _
      (isRegularSemisimple_finComponent_gammaPrime K u hu1 p v) _ ε (zpow_ne_zero _ (hϖ0 v hvT)) hε
      (htM v hvT) h01 h10 ?_ (τf v) (hτf v) (hτf1 v) _ (hτT v _) (hτT1 v _) J Jt hJ hJt
    rw [hcmv v, hmO v hvS, hzε]
  rcases hE with ⟨hI0, hcase⟩ | ⟨S₁, hS₁, Ia, Iv, hIa, hIvS, hIvU, hprodE⟩
  ·

    rw [hI0]
    suffices hΦ0 : (IAp * ∏ v ∈ S, IFp v) * ∏ v ∈ T, IT v (NumberField.Idele.ord K v z') = 0 by
      rw [hΦ0, mul_zero]
    rcases hcase with hA | ⟨v, hv, hvan⟩ | ⟨v, hv, hvU⟩
    · have hIA0 : IAp = 0 := by
        obtain ⟨w, -, hw⟩ := hIAp
        rw [hw]
        simp only [hA, zero_mul, integral_zero]
      rw [hIA0, zero_mul, zero_mul]
    · rcases Finset.mem_union.mp hv with hvS | hvT
      · have hIF0 : IFp v = 0 := by
          obtain ⟨w, -, hw⟩ := hIFp v hvS
          rw [hw]
          have hvan' : ∀ x : GL (Fin 2) (v.adicCompletion K),
              fS v (x⁻¹ * finComponent (𝓞 K) K v (glFin (𝓞 K) K (gammaPrime K u p)) * x) = 0 := by
            intro x; have h := hvan x; beta_reduce at h; rwa [hcm1 v hvS, one_mul] at h
          simp only [hvan', zero_mul, integral_zero]
        rw [Finset.prod_eq_zero hvS hIF0, mul_zero, zero_mul]
      · have hvan' : ∀ x : GL (Fin 2) (v.adicCompletion K),
            fS v (finComponent (𝓞 K) K v (glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K m)) *
              (x⁻¹ * finComponent (𝓞 K) K v (glFin (𝓞 K) K (gammaPrime K u p)) * x)) = 0 := by
          intro x; have h := hvan x; beta_reduce at h; exact h
        have hIT0 : IT v (NumberField.Idele.ord K v z') = 0 := by

          have hJ0 : AutomorphicForm.IsOrbitalIntegral K v (finComponent (𝓞 K) K v (glFin (𝓞 K) K (gammaPrime K u p))) (τf v)
              (fun y => fS v (finComponent (𝓞 K) K v (glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K m)) * y)) 0 := by
            refine ⟨fun _ => 0, ⟨fun _ => le_rfl, measurable_const, HasCompactSupport.zero, fun x hx => ?_⟩, ?_⟩
            · exact absurd (hvan' x) hx
            · simp only [hvan', zero_mul, integral_zero]
          exact ((hTid v hvT 0 _ hJ0 (hIT v hvT _))).symm
        rw [Finset.prod_eq_zero hvT hIT0, mul_zero]
    · exfalso
      apply hvU 1
      rw [inv_one, one_mul, mul_one]
      have hvS : v ∉ S := fun h => hv (Finset.mem_union_left T h)
      exact diagonal_mem_localIntegralSet K v _ _ _
        (by rw [hpO v hvS, one_mul]; exact huv v hv) (by rw [hpO v hvS]; exact norm_one) (hγ'v v)
  ·

    have hIa' : Ia = IAp := by
      haveI := hτa
      have h := AutomorphicForm.eq_inv_mul_of_isOrbitalIntegralOn_of_isOrbitalIntegralOn_smul_infiniteAdeleRing K
        (glArch (𝓞 K) K (gammaPrime K u p)) (isRegularSemisimple_glArch_gammaPrime K u hu1 p) ν hν τa
        1 one_pos fa hf.1 IAp Ia hIAp (by rw [ENNReal.ofReal_one, one_smul]; exact hIa)
      simpa using h
    have hIvS' : ∀ v ∈ S, Iv v = IFp v := by
      intro v hv
      have h := hIvS v (Finset.mem_union_left T hv)
      have hfun : (fun y : GL (Fin 2) (v.adicCompletion K) =>
          fS v (finComponent (𝓞 K) K v (glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K m)) * y)) = fS v := by
        funext y; rw [hcm1 v hv, one_mul]
      beta_reduce at h
      rw [hfun] at h
      exact AutomorphicForm.eq_of_isOrbitalIntegral_of_isOrbitalIntegral_of_isRegularSemisimple K v _
        (isRegularSemisimple_finComponent_gammaPrime K u hu1 p v) (τf v) (hτf v) (fS v)
        (hf.2.2.1 v (Finset.mem_union_left T hv)) (Iv v) (IFp v) h (hIFp v hv)
    have hIvT' : ∀ v ∈ T, Iv v = IT v (NumberField.Idele.ord K v z') :=
      fun v hvT => hTid v hvT _ _ (hIvS v (Finset.mem_union_right S hvT)) (hIT v hvT _)
    set nU : HeightOneSpectrum (𝓞 K) → ℝ := fun v =>
      if v ∈ S ∪ T then (1 : ℝ) else ‖algebraMap K (v.adicCompletion K) (u : K) - 1‖ with hnU
    have hIvO : ∀ v ∉ S ∪ T, Iv v = (((nU v)⁻¹ : ℝ) : ℂ) := by
      intro v hv
      have hvS : v ∉ S := fun h => hv (Finset.mem_union_left T h)
      have h := AutomorphicForm.eq_ite_inv_norm_sub_one_of_isOrbitalIntegral_indicator_localIntegralSet_diagonal K v
        (((p : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v) (algebraMap K (v.adicCompletion K) (u : K))
        (huv1 v) _ (hγ'v v) (τf v) (hτf v) (hτf1 v) (Iv v) (hIvU v hv)
      rw [h, hpO v hvS, norm_one, if_pos ⟨rfl, huv v hv⟩]
      simp only [hnU, if_neg hv, Complex.ofReal_inv]

    have h1 : (u : K) - 1 ≠ 0 := sub_ne_zero.mpr hu1
    have hfin : (Function.mulSupport nU).Finite := by
      refine (finite_mulSupport_norm_snd K
        (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) (Units.mk0 _ h1))).subset fun v hv => ?_
      simp only [Function.mem_mulSupport] at hv ⊢
      by_cases hvm : v ∈ S ∪ T
      · exact absurd (by simp only [hnU, if_pos hvm]) hv
      · simp only [hnU, if_neg hvm] at hv
        have he : (((Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) (Units.mk0 _ h1) :
            (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v =
            algebraMap K (v.adicCompletion K) ((u : K) - 1) := rfl
        rwa [he, map_sub, map_one]
    set T' : Finset (HeightOneSpectrum (𝓞 K)) := S₁ ∪ hfin.toFinset with hT'
    have hST' : S ∪ T ⊆ T' := hS₁.trans Finset.subset_union_left
    rw [hprodE T' Finset.subset_union_left, hIa']
    rw [← Finset.union_sdiff_of_subset hST', Finset.prod_union Finset.disjoint_sdiff,
      Finset.prod_union hTS.symm]
    rw [Finset.prod_congr rfl (fun v hv => hIvS' v hv), Finset.prod_congr rfl (fun v hv => hIvT' v hv),
      Finset.prod_congr rfl (fun v hv => hIvO v (Finset.mem_sdiff.mp hv).2)]
    have hNR : ∏ v ∈ T' \ (S ∪ T), (nU v)⁻¹ = (∏ᶠ v, nU v)⁻¹ := by
      rw [Finset.prod_inv_distrib]
      congr 1
      symm
      apply finprod_eq_prod_of_mulSupport_subset
      intro v hv
      simp only [Finset.coe_sdiff, Set.mem_diff, Finset.mem_coe]
      refine ⟨Finset.mem_union_right _ (hfin.mem_toFinset.mpr hv), fun hvm => ?_⟩
      simp only [Function.mem_mulSupport, hnU, if_pos hvm] at hv
      exact hv rfl
    have hN : ∏ v ∈ T' \ (S ∪ T), (((nU v)⁻¹ : ℝ) : ℂ) = (((∏ᶠ v, nU v)⁻¹ : ℝ) : ℂ) := by
      rw [← hNR]; push_cast; rfl
    rw [hN]
    push_cast
    ring

end AutomorphicForm.FactorCentreK

open AutomorphicForm.FactorCentreK in
open scoped Classical in
theorem solution
    (K : Type) [Field K] [NumberField K] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]
    (νZK : Measure (AdeleRing (𝓞 K) K)ˣ) [νZK.IsHaarMeasure]
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
        ξ ⟨z, Subgroup.mem_top z⟩ = 1)
    (S T : Finset (HeightOneSpectrum (𝓞 K))) (hTS : Disjoint T S)
    (hur : ∀ v ∉ S, ∀ t : (v.adicCompletion K)ˣ, Valued.v (t : v.adicCompletion K) = 1 →
      ξ ⟨Units.map (finIncl (𝓞 K) K) (localUnit (𝓞 K) K v t), Subgroup.mem_top _⟩ = 1)

    (f : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ) (fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ)
    (ff : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) → ℂ)
    (fS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K) → ℂ)
    (hf : AutomorphicForm.IsUnitFactorization K (S ∪ T) f fa ff fS)
    (hcen : ∀ v ∈ T, ∀ c : GL (Fin 2) (v.adicCompletion K),
      (∃ ε : v.adicCompletion K, Valued.v ε = 1 ∧
        (c : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) = ε • (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))) →
      ∀ y : GL (Fin 2) (v.adicCompletion K), fS v (c * y) = fS v y)

    (γ : GL (Fin 2) K) (u : Kˣ) (hu1 : (u : K) ≠ 1)
    (hγ : (γ : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 ∧ (γ : Matrix (Fin 2) (Fin 2) K) 0 1 = 0 ∧
      (γ : Matrix (Fin 2) (Fin 2) K) 0 0 / (γ : Matrix (Fin 2) (Fin 2) K) 1 1 = (u : K))
    (cτK : ℝ) (hcτK : 0 < cτK)
    (τK : Measure (Subgroup.centralizer ({AutomorphicForm.globalPoints (𝓞 K) K γ} : Set (GL (Fin 2) (AdeleRing (𝓞 K) K)))))
    [τK.IsHaarMeasure]
    (hτKc : ∀ g : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ,
      ∫ t : Subgroup.centralizer ({AutomorphicForm.globalPoints (𝓞 K) K γ} : Set (GL (Fin 2) (AdeleRing (𝓞 K) K))),
          g (t : GL (Fin 2) (AdeleRing (𝓞 K) K)) ∂τK =
        cτK * ∫ p : (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ, g (diagUnits2 p.1 p.2) ∂(νZK.prod νZK))
    (IK : (AdeleRing (𝓞 K) K)ˣ → ℂ)
    (hIK : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      AutomorphicForm.IsOrbitalIntegralOn (AdeleRing (𝓞 K) K) (adelicGLHaar (Fin 2) (𝓞 K) K)
        (AutomorphicForm.globalPoints (𝓞 K) K γ) τK
        (fun g : GL (Fin 2) (AdeleRing (𝓞 K) K) => f (AutomorphicForm.centralScalar (𝓞 K) K z * g)) (IK z))

    (νA : @Measure (GL (Fin 2) (InfiniteAdeleRing K)) (AutomorphicForm.glBorelOf (InfiniteAdeleRing K)))
    (hνA : @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.glBorelOf (InfiniteAdeleRing K)) νA)
    (cG : ℝ)
    (hG : ∀ (S : Finset (HeightOneSpectrum (𝓞 K)))
        (f : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ) (fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ)
        (fS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K) → ℂ),
        AEStronglyMeasurable[AutomorphicForm.glBorelOf (InfiniteAdeleRing K)] fa νA →
        (∀ v ∈ S, AEStronglyMeasurable[AutomorphicForm.localGLBorel K v] (fS v)
          (AutomorphicForm.localHaar K v)) →
        (∀ g : GL (Fin 2) (AdeleRing (𝓞 K) K),
          (∀ v ∉ S, AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K g) ∈
              AutomorphicForm.localIntegralSet K v) →
            f g = fa (AdelicLevel.glArch (𝓞 K) K g) *
              ∏ v ∈ S, fS v (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K g))) →
        (∀ g : GL (Fin 2) (AdeleRing (𝓞 K) K),
          (∃ v ∉ S, AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K g) ∉
              AutomorphicForm.localIntegralSet K v) → f g = 0) →
          ∫ g, f g ∂(adelicGLHaar (Fin 2) (𝓞 K) K) =
            cG * (∫ x, fa x ∂νA) * ∏ v ∈ S, ∫ y, fS v y ∂(AutomorphicForm.localHaar K v))
    (τG : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      Measure (Subgroup.centralizer ({(AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)} : Set (GL (Fin 2) (AdeleRing (𝓞 K) K)))))
    (hτG : ∀ z, (τG z).IsHaarMeasure)
    (hτGc : ∀ z, ∀ g : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ,
      ∫ t : Subgroup.centralizer ({(AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)} : Set (GL (Fin 2) (AdeleRing (𝓞 K) K))),
          g (t : GL (Fin 2) (AdeleRing (𝓞 K) K)) ∂(τG z) =
        cτK * ∫ p : (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ, g (diagUnits2 p.1 p.2) ∂(νZK.prod νZK))
    (τA : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      @Measure (Subgroup.centralizer
          ({AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)} : Set (GL (Fin 2) (InfiniteAdeleRing K))))
        (AutomorphicForm.centralizerBorel (InfiniteAdeleRing K) (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))))
    (hτA : ∀ z, @Measure.IsHaarMeasure _ _ _
      (AutomorphicForm.centralizerBorel (InfiniteAdeleRing K) (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))) (τA z))
    (τF : ∀ (z : (AdeleRing (𝓞 K) K)ˣ) (v : HeightOneSpectrum (𝓞 K)),
      @Measure (AutomorphicForm.localCentralizer K v
          (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))))
        (AutomorphicForm.localCentralizerBorel K v
          (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)))))
    (hτF : ∀ z v, @Measure.IsHaarMeasure _ _ _
      (AutomorphicForm.localCentralizerBorel K v
        (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)))) (τF z v))
    (hτF1 : ∀ z v, τF z v (Subtype.val ⁻¹' AutomorphicForm.localIntegralSet K v) = 1)
    (cT : ℝ) (hcT : 0 < cT)
    (hT : ∀ (z : (AdeleRing (𝓞 K) K)ˣ) (S' : Finset (HeightOneSpectrum (𝓞 K)))
        (W : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ) (Wa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ)
        (WS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K) → ℂ),
        AEStronglyMeasurable[AutomorphicForm.centralizerBorel (InfiniteAdeleRing K)
          (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))] (fun t => Wa t) (τA z) →
        (∀ v ∈ S', AEStronglyMeasurable[AutomorphicForm.localCentralizerBorel K v
          (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)))]
            (fun t => WS v t) (τF z v)) →
        (∀ t : Subgroup.centralizer ({(AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)} : Set (GL (Fin 2) (AdeleRing (𝓞 K) K))),
          (∀ v ∉ S', AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K t) ∈
              AutomorphicForm.localIntegralSet K v) →
            W t = Wa (AdelicLevel.glArch (𝓞 K) K t) *
              ∏ v ∈ S', WS v (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K t))) →
        (∀ t : Subgroup.centralizer ({(AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)} : Set (GL (Fin 2) (AdeleRing (𝓞 K) K))),
          (∃ v ∉ S', AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K t) ∉
              AutomorphicForm.localIntegralSet K v) → W t = 0) →
          ∫ t, W t ∂(τG z) = cT * (∫ t, Wa t ∂(τA z)) * ∏ v ∈ S', ∫ t, WS v t ∂(τF z v))

    (PZ : UnramifiedWhittaker.ProductMeasureData S νZK)
    (hPo : PZ.ord = NumberField.Idele.ord K) (hPp : PZ.projS = NumberField.Idele.partAt K S)
    (hPν : ENNReal.ofReal PZ.c • PZ.νS =
      Measure.map (NumberField.Idele.partAt K S)
        (νZK.restrict (NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K (↑S) : Set (AdeleRing (𝓞 K) K)ˣ)))

    (IA : (AdeleRing (𝓞 K) K)ˣ → ℂ)
    (hIA : ∀ z, AutomorphicForm.IsOrbitalIntegralOn (InfiniteAdeleRing K) νA
      (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)) (τA z) fa (IA z))
    (IF : (AdeleRing (𝓞 K) K)ˣ → HeightOneSpectrum (𝓞 K) → ℂ)
    (hIF : ∀ z, ∀ v ∈ S, AutomorphicForm.IsOrbitalIntegral K v
      (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))) (τF z v) (fS v) (IF z v))

    (hWint : Integrable (fun zS : (AdeleRing (𝓞 K) K)ˣ => ((ξ ⟨zS, Subgroup.mem_top zS⟩ : ℂˣ) : ℂ) *
      (IA zS * ∏ v ∈ S, IF zS v)) PZ.νS)
    (ϖT : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletionIntegers K) (hϖT : ∀ v ∈ T, Irreducible (ϖT v))
    (tT : ∀ v : HeightOneSpectrum (𝓞 K), ℤ → GL (Fin 2) (v.adicCompletion K))
    (htT : ∀ v ∈ T, ∀ e : ℤ, (tT v e : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
      Matrix.diagonal ![(ϖT v : v.adicCompletion K) ^ e * algebraMap K (v.adicCompletion K) (u : K),
        (ϖT v : v.adicCompletion K) ^ e])
    (τT : ∀ (v : HeightOneSpectrum (𝓞 K)) (e : ℤ),
      @Measure (AutomorphicForm.localCentralizer K v (tT v e)) (AutomorphicForm.localCentralizerBorel K v (tT v e)))
    (hτT : ∀ v e, @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.localCentralizerBorel K v (tT v e)) (τT v e))
    (hτT1 : ∀ v e, τT v e (Subtype.val ⁻¹' AutomorphicForm.localIntegralSet K v) = 1)
    (IT : HeightOneSpectrum (𝓞 K) → ℤ → ℂ)
    (hIT : ∀ v ∈ T, ∀ e : ℤ, AutomorphicForm.IsOrbitalIntegral K v (tT v e) (τT v e) (fS v) (IT v e))

    (hITsum : ∀ v ∈ T, Summable fun e : ℤ =>
      ‖((ξ ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K v), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) ^ e * IT v e‖) :
    ∫ z : (AdeleRing (𝓞 K) K)ˣ, ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * IK z ∂νZK =
      ((cG * cT⁻¹ * PZ.c : ℝ) : ℂ) *
        (if ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → v ∉ T → NumberField.Idele.ord K v (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) = 0
          then (1 : ℂ) else 0) *
        (if h1 : (u : K) - 1 ≠ 0 then
            ((NumberField.TateGlobal.ideleNorm K
                (NumberField.Idele.partAt K S (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) (Units.mk0 ((u : K) - 1) h1))) : ℝ) : ℂ)
          else 0) *
        (∏ v ∈ T, ((‖algebraMap K (v.adicCompletion K) (u : K) - 1‖ : ℝ) : ℂ) *
            ∑' e : ℤ, ((ξ ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K v), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) ^ e *
              IT v e) *
        ∫ zS : (AdeleRing (𝓞 K) K)ˣ, ((ξ ⟨zS, Subgroup.mem_top zS⟩ : ℂˣ) : ℂ) *
            (IA zS * ∏ v ∈ S, IF zS v) ∂PZ.νS := by
  classical
  obtain ⟨hγ10, hγ01, hγu⟩ := hγ

  have hdetγ : Matrix.det (γ : Matrix (Fin 2) (Fin 2) K) ≠ 0 := by
    have h := (Matrix.GeneralLinearGroup.det γ).ne_zero
    rwa [Matrix.GeneralLinearGroup.val_det_apply] at h
  have hγ11 : (γ : Matrix (Fin 2) (Fin 2) K) 1 1 ≠ 0 := by
    intro h; apply hdetγ; rw [Matrix.det_fin_two, h, hγ10]; ring
  have hγ00 : (γ : Matrix (Fin 2) (Fin 2) K) 0 0 = (γ : Matrix (Fin 2) (Fin 2) K) 1 1 * (u : K) := by
    rw [← hγu, mul_div_cancel₀ _ hγ11]
  set d : Kˣ := Units.mk0 _ hγ11 with hd
  set dA : (AdeleRing (𝓞 K) K)ˣ := Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) d with hdA
  have huAv : ∀ v : HeightOneSpectrum (𝓞 K), (((Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v =
      algebraMap K (v.adicCompletion K) (u : K) := fun v => rfl
  have hM1 : AutomorphicForm.globalPoints (𝓞 K) K γ = gammaPrime K u dA := by
    apply Units.ext
    rw [coe_gammaPrime]
    ext i j
    fin_cases i <;> fin_cases j
    · show algebraMap K (AdeleRing (𝓞 K) K) ((γ : Matrix (Fin 2) (Fin 2) K) 0 0) = _
      rw [hγ00, map_mul]; simp; rfl
    · show algebraMap K (AdeleRing (𝓞 K) K) ((γ : Matrix (Fin 2) (Fin 2) K) 0 1) = _
      rw [hγ01, map_zero]; simp
    · show algebraMap K (AdeleRing (𝓞 K) K) ((γ : Matrix (Fin 2) (Fin 2) K) 1 0) = _
      rw [hγ10, map_zero]; simp
    · show algebraMap K (AdeleRing (𝓞 K) K) ((γ : Matrix (Fin 2) (Fin 2) K) 1 1) = _
      simp; rfl

  have h1 : (u : K) - 1 ≠ 0 := sub_ne_zero.mpr hu1
  set a1 : Kˣ := Units.mk0 ((u : K) - 1) h1 with ha1
  set nU : HeightOneSpectrum (𝓞 K) → ℝ := fun v =>
    if v ∈ S ∪ T then (1 : ℝ) else ‖algebraMap K (v.adicCompletion K) (a1 : K)‖ with hnU
  have hnUv : ∀ v ∉ S ∪ T, nU v = ‖algebraMap K (v.adicCompletion K) (u : K) - 1‖ := by
    intro v hv; simp only [hnU, if_neg hv, ha1, Units.val_mk0, map_sub, map_one]
  set N₀ : ℝ := ∏ᶠ v, nU v with hN₀
  have hFE : NumberField.TateGlobal.ideleNorm K
        (NumberField.Idele.partAt K S (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) a1)) *
      (∏ v ∈ T, ‖algebraMap K (v.adicCompletion K) (a1 : K)‖) * N₀ = 1 :=
    NumberField.TateGlobal.ideleNorm_partAt_mul_prod_norm_mul_finprod_norm_eq_one K S T hTS a1
  have hN₀ne : N₀ ≠ 0 := by
    intro h0; rw [h0, mul_zero] at hFE; exact zero_ne_one hFE
  have huv1 : ∀ v : HeightOneSpectrum (𝓞 K), algebraMap K (v.adicCompletion K) (u : K) ≠ 1 := by
    intro v h; apply hu1
    exact (algebraMap K (v.adicCompletion K)).injective (by rw [h, map_one])
  set Φ : (AdeleRing (𝓞 K) K)ˣ → ℂ := fun w => IA w * ∏ v ∈ S, IF w v with hΦ
  set U : Set (AdeleRing (𝓞 K) K)ˣ :=
    (NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K (↑(S ∪ T) : Set (HeightOneSpectrum (𝓞 K))) :
      Set (AdeleRing (𝓞 K) K)ˣ) with hU
  set G : (AdeleRing (𝓞 K) K)ˣ → ℂ :=
    U.indicator (fun w => Φ (NumberField.Idele.partAt K S w) * ∏ v ∈ T, IT v (NumberField.Idele.ord K v w)) with hGdef
  set cU : ℂ := (if ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → v ∉ T → NumberField.Idele.ord K v (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) = 0
    then (1 : ℂ) else 0) with hcU
  set C : ℂ := ((cG * cT⁻¹ : ℝ) : ℂ) * ((N₀⁻¹ : ℝ) : ℂ) with hC
  have hμ := NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 K) K

  have key : ∀ z : (AdeleRing (𝓞 K) K)ˣ, IK z = C * cU * G (z * dA) := by
    intro z

    have hconj : ∀ (x : GL (Fin 2) (AdeleRing (𝓞 K) K)) (w : (AdeleRing (𝓞 K) K)ˣ) (g : GL (Fin 2) (AdeleRing (𝓞 K) K)),
        AutomorphicForm.centralScalar (𝓞 K) K w * (x⁻¹ * g * x) =
          x⁻¹ * (AutomorphicForm.centralScalar (𝓞 K) K w * g) * x := by
      intro x w g
      simp only [← mul_assoc]
      rw [centralScalar_comm K w x⁻¹]
    obtain ⟨z', hz'⟩ : ∃ z' : (AdeleRing (𝓞 K) K)ˣ, z * dA = z' := ⟨_, rfl⟩
    rw [hz']
    obtain ⟨p, hp⟩ : ∃ p : (AdeleRing (𝓞 K) K)ˣ, NumberField.Idele.partAt K S z' = p := ⟨_, rfl⟩
    have hpS : ∀ v ∈ S, ((p : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v =
        ((z' : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v :=
      fun v hv => by rw [← hp]; exact NumberField.Idele.partAt_snd_of_mem K S z' hv
    have hpO : ∀ v ∉ S, ((p : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v = 1 :=
      fun v hv => by rw [← hp]; exact NumberField.Idele.partAt_snd_of_not_mem K S z' hv
    by_cases hgood : z' ∈ U ∧ ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → v ∉ T → NumberField.Idele.ord K v (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) = 0
    ·

      obtain ⟨hzU, hu0⟩ := hgood
      have hcU1 : cU = 1 := by simp only [hcU, if_pos hu0]
      have hGz : G z' = Φ p * ∏ v ∈ T, IT v (NumberField.Idele.ord K v z') := by
        simp only [hGdef, Set.indicator_of_mem hzU, hp]
      rw [hcU1, mul_one, hGz]
      have hzU' : ∀ v ∉ S ∪ T, ‖((z' : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v‖ = 1 := by
        intro v hv
        exact (mem_unitIdelesOutside_iff_norm K _ z').mp hzU v (by simpa using hv)
      have huv : ∀ v ∉ S ∪ T, ‖algebraMap K (v.adicCompletion K) (u : K)‖ = 1 := by
        intro v hv
        rw [Finset.mem_union, not_or] at hv
        rw [← huAv, ← ord_eq_zero_iff_norm]
        exact hu0 v hv.1 hv.2

      obtain ⟨m, hm⟩ : ∃ m : (AdeleRing (𝓞 K) K)ˣ, z' * p⁻¹ = m := ⟨_, rfl⟩
      have hmp : m * p = z' := by rw [← hm, inv_mul_cancel_right]
      have hm1 : (m : AdeleRing (𝓞 K) K).1 = 1 := by
        have h : ((m : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 * ((p : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 =
            ((z' : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 := by
          rw [← hmp]; rfl
        have hp1 : ((p : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 = ((z' : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 := by
          rw [← hp]; exact NumberField.Idele.partAt_fst K S z'
        rw [hp1] at h
        have hu : IsUnit (((z' : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1) :=
          (Units.isUnit z').map (RingHom.fst _ _)
        exact hu.mul_right_cancel (h.trans (one_mul _).symm)
      have hmv : ∀ v, ((m : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v *
          ((p : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v =
          ((z' : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v := by
        intro v; rw [← snd_apply_mul, hmp]
      have hmS : ∀ v ∈ S, ((m : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v = 1 := by
        intro v hv
        have h := hmv v
        rw [hpS v hv] at h
        have hz0 : ((z' : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v ≠ 0 := by
          intro h0
          have hval := NumberField.Idele.valued_snd_ne_zero K v z'
          rw [h0, map_zero] at hval
          exact hval rfl
        exact (mul_left_eq_self₀.mp h).resolve_right hz0
      have hmO : ∀ v ∉ S, ((m : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v =
          ((z' : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v := by
        intro v hv
        have h := hmv v
        rwa [hpO v hv, mul_one] at h

      have hO : AutomorphicForm.IsOrbitalIntegralOn (AdeleRing (𝓞 K) K) (adelicGLHaar (Fin 2) (𝓞 K) K)
          (AutomorphicForm.centralScalar (𝓞 K) K p * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1) (τG p)
          (fun g => f (AutomorphicForm.centralScalar (𝓞 K) K m * g)) (IK z) := by
        refine isOrbitalIntegralOn_transport K _ _ τK (τG p) cτK (νZK.prod νZK) hτKc (hτGc p)
          (fun g => f (AutomorphicForm.centralScalar (𝓞 K) K z * g))
          (fun g => f (AutomorphicForm.centralScalar (𝓞 K) K m * g)) (fun x => ?_) (IK z) (hIK z)
        show f (AutomorphicForm.centralScalar (𝓞 K) K z * (x⁻¹ * AutomorphicForm.globalPoints (𝓞 K) K γ * x)) =
          f (AutomorphicForm.centralScalar (𝓞 K) K m * (x⁻¹ * gammaPrime K u p * x))
        rw [hconj, hconj, hM1, centralScalar_mul_gammaPrime, centralScalar_mul_gammaPrime, hmp, hz']
      have hmain := perClass_main K (adelicGLHaar (Fin 2) (𝓞 K) K) hμ νA cG hG _
        (isRegularSemisimple_gammaPrime K u hu1 p) (τG p) (hτG p) (τA p) (hτA p) (τF p) (hτF p) (hτF1 p)
        cT hcT (hT p) hνA S T hTS f fa ff fS hf hcen u hu1 p m z' rfl hpO hm1 hmS hmO hzU' huv
        (IA p) (hIA p) (IF p) (hIF p) ϖT hϖT tT htT τT hτT hτT1 IT hIT (IK z) hO
      have hNeq : (∏ᶠ v : HeightOneSpectrum (𝓞 K),
          (if v ∈ S ∪ T then (1 : ℝ) else ‖algebraMap K (v.adicCompletion K) (u : K) - 1‖)) = N₀ := by
        rw [hN₀]
        congr 1
        funext v
        simp only [hnU, ha1, Units.val_mk0, map_sub, map_one]
      rw [hmain, hNeq]
    ·

      have hR : C * cU * G z' = 0 := by
        rcases not_and_or.mp hgood with hzU | hu0
        · simp only [hGdef, Set.indicator_of_notMem hzU, mul_zero]
        · simp only [hcU, if_neg hu0, mul_zero, zero_mul]
      rw [hR]

      have hbad : ∃ v₀, v₀ ∉ S ∪ T ∧
          ¬ (‖((z' : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v₀‖ = 1 ∧
             ‖algebraMap K (v₀.adicCompletion K) (u : K)‖ = 1) := by
        by_contra hcon
        push Not at hcon
        apply hgood
        constructor
        · rw [hU, SetLike.mem_coe, mem_unitIdelesOutside_iff_norm]
          intro v hv
          exact (hcon v (by simpa using hv)).1
        · intro v hvS hvT
          rw [ord_eq_zero_iff_norm, huAv]
          exact (hcon v (by simp [hvS, hvT])).2
      obtain ⟨v₀, hv₀, hv₀bad⟩ := hbad
      have hO : AutomorphicForm.IsOrbitalIntegralOn (AdeleRing (𝓞 K) K) (adelicGLHaar (Fin 2) (𝓞 K) K)
          (AutomorphicForm.centralScalar (𝓞 K) K z' * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1) (τG z') f (IK z) := by
        refine isOrbitalIntegralOn_transport K _ _ τK (τG z') cτK (νZK.prod νZK) hτKc (hτGc z')
          (fun g => f (AutomorphicForm.centralScalar (𝓞 K) K z * g)) f (fun x => ?_) (IK z) (hIK z)
        show f (AutomorphicForm.centralScalar (𝓞 K) K z * (x⁻¹ * AutomorphicForm.globalPoints (𝓞 K) K γ * x)) =
          f (x⁻¹ * gammaPrime K u z' * x)
        rw [hconj, hM1, centralScalar_mul_gammaPrime, hz']
      exact perClass_vanish K (adelicGLHaar (Fin 2) (𝓞 K) K) hμ νA cG hG _
        (isRegularSemisimple_gammaPrime K u hu1 z') (τG z') (hτG z') (τA z') (hτA z') (τF z') (hτF z') (hτF1 z')
        cT hcT (hT z') S T f fa ff fS hf u hu1 z' rfl (IK z) hO v₀ hv₀ hv₀bad

  have hint : ∫ z : (AdeleRing (𝓞 K) K)ˣ, ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * IK z ∂νZK =
      C * cU * ∫ z : (AdeleRing (𝓞 K) K)ˣ, ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * G (z * dA) ∂νZK := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    beta_reduce
    rw [key z]; ring
  have hC0 := NumberField.Idele.integral_mul_indicator_unitIdelesOutside_mul_prod_translate_eq_mul_integral_mul_prod_tsum
    K νZK ξ hξc hξt S T hTS hur PZ hPo hPp d Φ hWint IT hITsum
  rw [hint]
  erw [hC0]

  rw [dif_pos h1]
  have hN₀inv : (N₀⁻¹ : ℝ) = NumberField.TateGlobal.ideleNorm K
      (NumberField.Idele.partAt K S (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) a1)) *
      ∏ v ∈ T, ‖algebraMap K (v.adicCompletion K) (u : K) - 1‖ := by
    have hT' : ∏ v ∈ T, ‖algebraMap K (v.adicCompletion K) (a1 : K)‖ =
        ∏ v ∈ T, ‖algebraMap K (v.adicCompletion K) (u : K) - 1‖ := by
      refine Finset.prod_congr rfl fun v _ => ?_
      simp only [ha1, Units.val_mk0, map_sub, map_one]
    rw [← hT']
    field_simp
    linarith [hFE]
  have hprodT : ∏ v ∈ T, (((‖algebraMap K (v.adicCompletion K) (u : K) - 1‖ : ℝ) : ℂ) *
      ∑' e : ℤ, ((ξ ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K v), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) ^ e * IT v e) =
      ((∏ v ∈ T, ‖algebraMap K (v.adicCompletion K) (u : K) - 1‖ : ℝ) : ℂ) *
      ∏ v ∈ T, ∑' e : ℤ, ((ξ ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K v), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) ^ e * IT v e := by
    rw [Finset.prod_mul_distrib]; push_cast; rfl
  rw [hprodT]
  simp only [hC]
  rw [hN₀inv]
  push_cast
  ring

end S_AutomorphicForm_integral_mul_orbital_centralScalar_eq_mul_ideleNorm_mul_prod_tsum_mul_integral_of_isUnitFactorization_of_integrable
end P2MW
export P2MW.S_AutomorphicForm_integral_mul_orbital_centralScalar_eq_mul_ideleNorm_mul_prod_tsum_mul_integral_of_isUnitFactorization_of_integrable (solution)
