-- Prove2me | solution 1 for AutomorphicForm.exists_nhd_whittakerCoefficient_diagOne_sPartMeasure_lt_top
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/4e6eb79f-e13e-5996-a3ec-90a689499613

import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_BoundedGenuineCuspRealization
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_NumberField_AdelicFourier
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_UnramifiedWhittaker_ZetaIntegrand
import Definitions.Def_IsDedekindDomain_FiniteUnitIdeles
import Definitions.Def_IsDedekindDomain_FiniteUnitIdelesOutside
import Definitions.Def_NumberField_IdeleBox
import Theorems.Thm_AutomorphicForm_continuous_whittakerCoefficient
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_nhd_whittakerCoefficient_diagOne_sPartMeasure_lt_top
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions"

set_option autoImplicit false
set_option maxHeartbeats 800000

open NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar MeasureTheory
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain NumberField.TateGlobal
open UnramifiedWhittaker
open scoped Pointwise

theorem solution
    (F : Type) [Field F] [NumberField F]
    (D : Set (AdelicGL2 (𝓞 F) F))
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (hψ : IsGlobalAddChar F ψ)
    (G : AdelicGL2 (𝓞 F) F → ℂ) (hGc : Continuous G)
    (hMG : ∃ C : ℝ, ∃ M : ℕ, ∀ g : AdelicGL2 (𝓞 F) F,
      ‖G g‖ ≤ C * max (ideleNorm F (Matrix.GeneralLinearGroup.det g))
        (ideleNorm F (Matrix.GeneralLinearGroup.det g))⁻¹ ^ M)
    (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (hχ : IsIdeleClassChar (𝓞 F) F χ) (hχc : Continuous χ)
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (a₀ : (AdeleRing (𝓞 F) F)ˣ)
    (ha₀ : ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S → ((a₀ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 v = 1)
    (s₁ : ℂ)
    (hW : whittakerCoefficient F (productionPinsOf F D
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ψ G 1 (diagOne a₀) ≠ 0) :
    ∃ (Ω K N : Set (AdeleRing (𝓞 F) F)ˣ) (r R M₁ X : ℝ),
      MeasurableSet[NumberField.Idele.ideleBorel F] Ω ∧ MeasurableSet[NumberField.Idele.ideleBorel F] K ∧ NumberField.Idele.sPartMeasure F S Ωᶜ = 0 ∧ NumberField.Idele.sPartMeasure F S K < ⊤ ∧ 0 < r ∧
      IsOpen N ∧ a₀ ∈ N ∧ N ⊆ K ∧
      (∀ s : ℂ, Measurable[NumberField.Idele.ideleBorel F] fun a => zetaIntegrand (fun g => whittakerCoefficient F (productionPinsOf F D
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ψ G 1 g) χ s a) ∧
      (∀ a ∈ K, ‖whittakerCoefficient F (productionPinsOf F D
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ψ G 1 (diagOne a)‖ ≤ M₁ ∧ ‖((χ a : ℂˣ) : ℂ)‖ ≤ X ∧ r ≤ ideleNorm F a ∧ ideleNorm F a ≤ R) ∧
      zetaIntegrand (fun g => whittakerCoefficient F (productionPinsOf F D
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ψ G 1 g) χ s₁ a₀ ≠ 0 ∧
      (∀ a ∈ Ω, a ∈ N →
        ‖zetaIntegrand (fun g => whittakerCoefficient F (productionPinsOf F D
          (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
          (adelicBox F)) ψ G 1 g) χ s₁ a₀‖ ^ 2 / 2 ≤
        (zetaIntegrand (fun g => whittakerCoefficient F (productionPinsOf F D
          (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
          (adelicBox F)) ψ G 1 g) χ s₁ a *
         star (zetaIntegrand (fun g => whittakerCoefficient F (productionPinsOf F D
          (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
          (adelicBox F)) ψ G 1 g) χ s₁ a₀)).re) ∧
      (∀ a, NumberField.Idele.partAt F S a = a ↔ a ∈ Ω) := by
  classical
  letI : MeasurableSpace (AdeleRing (𝓞 F) F)ˣ := NumberField.Idele.ideleBorel F
  haveI : BorelSpace (AdeleRing (𝓞 F) F)ˣ := NumberField.Idele.borelSpace_ideleBorel F
  haveI : (NumberField.Idele.idelicHaar F).IsHaarMeasure := NumberField.Idele.isHaarMeasure_idelicHaar F

  have hval : Continuous fun a : (AdeleRing (𝓞 F) F)ˣ =>
      ((diagOne a : GL (Fin 2) (AdeleRing (𝓞 F) F)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) := by
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [diagOne_coe_apply] <;>
      first | exact Units.continuous_val | exact continuous_const
  have hdiag : Continuous (fun a : (AdeleRing (𝓞 F) F)ˣ => (diagOne a : GL (Fin 2) (AdeleRing (𝓞 F) F))) := by
    refine Units.continuous_iff.mpr ⟨hval, ?_⟩
    have h2 : Continuous fun a : (AdeleRing (𝓞 F) F)ˣ =>
        ((diagOne a⁻¹ : GL (Fin 2) (AdeleRing (𝓞 F) F)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) :=
      hval.comp continuous_inv
    simpa only [map_inv] using h2
  have hWc : Continuous fun a : (AdeleRing (𝓞 F) F)ˣ => whittakerCoefficient F (productionPinsOf F D
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ψ G 1 (diagOne a) :=
    (AutomorphicForm.continuous_whittakerCoefficient F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
      (fun v => heckeGen (𝓞 F) F v) ψ hψ.continuous G hGc 1).comp hdiag
  have hχc' : Continuous fun a : (AdeleRing (𝓞 F) F)ˣ => ((χ a : ℂˣ) : ℂ) := Units.continuous_val.comp hχc
  have hNc : Continuous fun a : (AdeleRing (𝓞 F) F)ˣ => ((ideleNorm F a : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (NumberField.TateGlobal.continuous_ideleNorm F)
  have hZc : ∀ s : ℂ, Continuous fun a : (AdeleRing (𝓞 F) F)ˣ => zetaIntegrand (fun g => whittakerCoefficient F
        (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ψ G 1 g) χ s a := by
    intro s
    simp only [zetaIntegrand]
    exact (hWc.mul hχc').mul (hNc.cpow continuous_const fun a => Complex.ofReal_mem_slitPlane.mpr (ideleNorm_pos a))

  obtain ⟨K, hKc, hKn⟩ := exists_compact_mem_nhds a₀
  have ha₀K : a₀ ∈ K := mem_of_mem_nhds hKn
  obtain ⟨M₁, hM₁⟩ := hKc.exists_bound_of_continuousOn hWc.continuousOn
  obtain ⟨X, hX⟩ := hKc.exists_bound_of_continuousOn hχc'.continuousOn
  obtain ⟨amin, -, hmin⟩ := hKc.exists_isMinOn ⟨a₀, ha₀K⟩ (NumberField.TateGlobal.continuous_ideleNorm F).continuousOn
  obtain ⟨R, hR⟩ := hKc.exists_bound_of_continuousOn (NumberField.TateGlobal.continuous_ideleNorm F).continuousOn

  have hZ₀ : zetaIntegrand (fun g => whittakerCoefficient F
        (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ψ G 1 g) χ s₁ a₀ ≠ 0 := by
    simp only [zetaIntegrand]
    refine mul_ne_zero (mul_ne_zero hW (Units.ne_zero _)) ?_
    rw [Ne, Complex.cpow_eq_zero_iff, not_and_or]
    exact Or.inl (by exact_mod_cast (ideleNorm_pos a₀).ne')

  set Z₀ : ℂ := zetaIntegrand (fun g => whittakerCoefficient F
        (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ψ G 1 g) χ s₁ a₀ with hZ₀def
  have hfc : Continuous fun a : (AdeleRing (𝓞 F) F)ˣ => (zetaIntegrand (fun g => whittakerCoefficient F
        (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ψ G 1 g) χ s₁ a * star Z₀).re :=
    Complex.continuous_re.comp ((hZc s₁).mul continuous_const)
  have hself : ‖Z₀‖ ^ 2 / 2 < (Z₀ * star Z₀).re := by
    have h1 : (Z₀ * star Z₀).re = ‖Z₀‖ ^ 2 := by
      rw [Complex.star_def, Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
    rw [h1]
    have : 0 < ‖Z₀‖ ^ 2 := pow_pos (norm_pos_iff.mpr hZ₀) 2
    linarith
  refine ⟨{a | NumberField.Idele.partAt F S a = a}, K,
    {a | ‖Z₀‖ ^ 2 / 2 < (zetaIntegrand (fun g => whittakerCoefficient F
        (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ψ G 1 g) χ s₁ a * star Z₀).re} ∩ interior K,
    ideleNorm F amin, R, M₁, X, ?_, hKc.isClosed.measurableSet, ?_, ?_, ideleNorm_pos amin,
    (isOpen_lt continuous_const hfc).inter isOpen_interior, ⟨hself, mem_interior_iff_mem_nhds.mpr hKn⟩,
    fun a ha => interior_subset ha.2, fun s => (hZc s).measurable, ?_, hZ₀, fun a _ haN => le_of_lt haN.1,
    fun a => Iff.rfl⟩

  · exact (isClosed_eq (NumberField.Idele.continuous_partAt F S) continuous_id).measurableSet

  · have hΩm : MeasurableSet {a : (AdeleRing (𝓞 F) F)ˣ | NumberField.Idele.partAt F S a = a} :=
      (isClosed_eq (NumberField.Idele.continuous_partAt F S) continuous_id).measurableSet
    have hidem : ∀ a : (AdeleRing (𝓞 F) F)ˣ,
        NumberField.Idele.partAt F S (NumberField.Idele.partAt F S a) = NumberField.Idele.partAt F S a := by
      intro a
      refine Units.ext (Prod.ext rfl (Subtype.ext (funext fun v => ?_)))
      by_cases hv : v ∈ S
      · exact (NumberField.Idele.partAt_snd_of_mem F S _ hv)
      · exact (NumberField.Idele.partAt_snd_of_not_mem F S _ hv).trans (NumberField.Idele.partAt_snd_of_not_mem F S _ hv).symm
    simp only [NumberField.Idele.sPartMeasure]
    rw [Measure.map_apply (NumberField.Idele.measurable_partAt F S) hΩm.compl]
    have hempty : NumberField.Idele.partAt F S ⁻¹' {a | NumberField.Idele.partAt F S a = a}ᶜ = ∅ := by
      ext a
      simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_not]
      exact hidem a
    rw [hempty, measure_empty]

  · simp only [NumberField.Idele.sPartMeasure]
    rw [Measure.map_apply (NumberField.Idele.measurable_partAt F S) hKc.isClosed.measurableSet,
      Measure.restrict_apply ((NumberField.Idele.measurable_partAt F S) hKc.isClosed.measurableSet)]
    set C₁ : Set (AdeleRing (𝓞 F) F) :=
      (({1} : Set (InfiniteAdeleRing F)) ×ˢ AdelicLevel.integralFiniteAdeles (𝓞 F) F : Set (AdeleRing (𝓞 F) F))
      with hC₁
    have hC₁c : IsCompact C₁ := isCompact_singleton.prod (AdelicLevel.isCompact_integralFiniteAdeles (𝓞 F) F)
    set W : Set (AdeleRing (𝓞 F) F)ˣ :=
      (Units.embedProduct (AdeleRing (𝓞 F) F)) ⁻¹' (C₁ ×ˢ (MulOpposite.op '' C₁)) with hWdef
    have hWc' : IsCompact W :=
      Units.isClosedEmbedding_embedProduct.isCompact_preimage (hC₁c.prod (hC₁c.image MulOpposite.continuous_op))
    have hsub : NumberField.Idele.partAt F S ⁻¹' K ∩
        (NumberField.AdeleRing.unitIdelesOutside (𝓞 F) F (↑S) : Set (AdeleRing (𝓞 F) F)ˣ) ⊆ K * W := by
      rintro a ⟨haK, haU⟩
      have haU' : a ∈ NumberField.AdeleRing.unitIdelesOutside (𝓞 F) F (↑S ∪ {v | v ∈ ([] : List (HeightOneSpectrum (𝓞 F)))}) := by
        simpa using haU
      have hdec := NumberField.Idele.eq_partAt_mul_prod_mul_unitPart F S [] (by simp) List.nodup_nil a haU'
      simp only [List.map_nil, List.prod_nil, mul_one] at hdec
      refine Set.mem_mul.mpr ⟨NumberField.Idele.partAt F S a, haK, NumberField.Idele.unitPart F S a, ?_, hdec.symm⟩
      have hu := NumberField.Idele.finitePartUnits_unitPart_mem_unitIdeles F S a
      have hfst := NumberField.Idele.unitPart_fst F S a
      have hinvfst : (((NumberField.Idele.unitPart F S a)⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 = 1 := by
        have h := congrArg (fun x : AdeleRing (𝓞 F) F => x.1) (NumberField.Idele.unitPart F S a).inv_val
        change (NumberField.Idele.unitPart F S a).inv.1 * ((NumberField.Idele.unitPart F S a : (AdeleRing (𝓞 F) F)ˣ) :
          AdeleRing (𝓞 F) F).1 = 1 at h
        rw [hfst, mul_one] at h
        exact h
      refine ⟨⟨?_, ?_⟩, ⟨(((NumberField.Idele.unitPart F S a)⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F), ⟨?_, ?_⟩, rfl⟩⟩
      · exact hfst
      · exact hu.1
      · exact hinvfst
      · intro v
        have := hu.2 v
        rwa [← map_inv] at this
    calc NumberField.Idele.idelicHaar F (NumberField.Idele.partAt F S ⁻¹' K ∩
          (NumberField.AdeleRing.unitIdelesOutside (𝓞 F) F (↑S) : Set (AdeleRing (𝓞 F) F)ˣ))
        ≤ NumberField.Idele.idelicHaar F (K * W) := measure_mono hsub
      _ < ⊤ := (hKc.mul hWc').measure_lt_top

  · intro a ha
    refine ⟨hM₁ a ha, hX a ha, hmin ha, ?_⟩
    have := hR a ha
    rw [Real.norm_eq_abs] at this
    exact (le_abs_self _).trans this

end S_AutomorphicForm_exists_nhd_whittakerCoefficient_diagOne_sPartMeasure_lt_top
end P2MW
export P2MW.S_AutomorphicForm_exists_nhd_whittakerCoefficient_diagOne_sPartMeasure_lt_top (solution)
