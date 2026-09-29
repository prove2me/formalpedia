-- Prove2me | solution 1 for AutomorphicForm.integral_mul_conj_weylIntertwiningIntegral_sigmaAdelicAct_eq_of_sigmaInvariant_and_of_sigmaReversed_of_principalLevel_of_ne_bot
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/6e3bc6aa-410f-5efe-a703-7d5840ffab5e

import Theorems.Thm_AutomorphicForm_integral_mul_conj_axis_continuation_weylIntertwiningIntegral_eq_of_swap_pair_of_principalLevel_of_ne_bot
import Theorems.Thm_AutomorphicForm_isInducedSection_and_isArchKFinite_and_axis_continuation_comp_sigmaAdelicAct_symm_of_flat_family_of_principalLevel
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_integral_mul_conj_weylIntertwiningIntegral_sigmaAdelicAct_eq_of_sigmaInvariant_and_of_sigmaReversed_of_principalLevel_of_ne_bot
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instMeasurableSpaceRestrictedProduct_definitions instBorelSpaceRestrictedProduct_definitions MeasureTheory.instMeasurableNegSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableMulSubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableAddSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableInvSubtypeMemSubgroup_definitions"
p2m_attr_erase "simp" "UnramifiedWhittaker.ProductMeasureData.mk.injEq UnramifiedWhittaker.ProductMeasureData.mk.sizeOf_spec NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply LanglandsTunnell.RankinSelberg.rs22GlobalIntegral_zero_left LanglandsTunnell.RankinSelberg.rs22LocalIntegral_zero_left LanglandsTunnell.RankinSelberg.rs22GlobalIntegral_zero_right ContinuousAddEquiv.preimage_mulLeft_smul LanglandsTunnell.ArchPlace.complexTestFun_zero_apply LanglandsTunnell.ArchPlace.norm_anglePhase LanglandsTunnell.ArchPlace.realTestFun_zero_apply"

set_option autoImplicit false
set_option maxHeartbeats 6400000

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open scoped TensorProduct Pointwise ComplexConjugate NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

noncomputable section

namespace R4AdjSigma

open AutomorphicForm

section Alpha

variable (L : Type) [Field L] [NumberField L]

set_option quotPrecheck false in
local notation "αL" => (((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 L) L))).toHomUnits)

theorem cpowChar_val_add (hα : ∀ x, 0 < ((αL x : ℝˣ) : ℝ)) (s₁ s₂ : ℂ) (z : (AdeleRing (𝓞 L) L)ˣ) :
    ((cpowChar αL hα (s₁ + s₂) z : ℂˣ) : ℂ) =
    ((cpowChar αL hα s₁ z : ℂˣ) : ℂ) *
    ((cpowChar αL hα s₂ z : ℂˣ) : ℂ) := by
  rw [cpowChar_apply_val, cpowChar_apply_val, cpowChar_apply_val]
  exact Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr (hα z).ne')

theorem mul_cpowChar_mul_cpowChar_neg (hα : ∀ x, 0 < ((αL x : ℝˣ) : ℝ)) (χ : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ)
    (a : ℂ) : χ * cpowChar αL hα a * cpowChar αL hα (-a) = χ := by
  apply MonoidHom.ext; intro z; apply Units.ext
  rw [MonoidHom.mul_apply, MonoidHom.mul_apply, Units.val_mul, Units.val_mul, mul_assoc,
    ← cpowChar_val_add, add_neg_cancel, cpowChar_apply_val, Complex.cpow_zero, mul_one]

theorem etaFst_mul_cpowChar (hα : ∀ x, 0 < ((αL x : ℝˣ) : ℝ)) (μ : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ) (a s : ℂ) :
    etaFst (μ * cpowChar αL hα a) αL hα s = etaFst μ αL hα (s + a) := by
  apply MonoidHom.ext; intro z; apply Units.ext
  rw [etaFst_apply, etaFst_apply, MonoidHom.mul_apply, Units.val_mul, Units.val_mul, Units.val_mul,
    show s + a + 1 / 2 = a + (s + 1 / 2) by ring, cpowChar_val_add L hα a (s + 1 / 2) z, mul_assoc]

theorem etaSnd_mul_cpowChar (hα : ∀ x, 0 < ((αL x : ℝˣ) : ℝ)) (ν : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ) (a s : ℂ) :
    etaSnd (ν * cpowChar αL hα (-a)) αL hα s = etaSnd ν αL hα (s + a) := by
  apply MonoidHom.ext; intro z; apply Units.ext
  rw [etaSnd_apply, etaSnd_apply, MonoidHom.mul_apply, Units.val_mul, Units.val_mul, Units.val_mul,
    show -(s + a + 1 / 2) = -a + -(s + 1 / 2) by ring, cpowChar_val_add L hα (-a) (-(s + 1 / 2)) z, mul_assoc]

end Alpha

section Levels

variable (L : Type) [Field L] [NumberField L]

theorem idealBound_mono {N N' : Ideal (𝓞 L)} (h : N ≤ N') (w : HeightOneSpectrum (𝓞 L)) :
    idealBound (𝓞 L) N w ≤ idealBound (𝓞 L) N' w := by
  by_cases hN : N = ⊥
  · subst hN
    rw [idealBound_bot]
    exact zero_le'
  have hN' : N' ≠ ⊥ := fun h' => hN (le_bot_iff.mp (h' ▸ h))
  rw [idealBound_of_ne_bot hN, idealBound_of_ne_bot hN', WithZero.exp_le_exp, neg_le_neg_iff, Nat.cast_le]
  exact Associates.count_le_count_of_le (Associates.mk_ne_zero.mpr hN)
    (Associates.irreducible_mk.mpr w.irreducible) (Associates.mk_le_mk_of_dvd (Ideal.dvd_iff_le.mpr h))

theorem levelOne_mono {N N' : Ideal (𝓞 L)} (h : N ≤ N') :
    levelOne (𝓞 L) L N ≤ levelOne (𝓞 L) L N' := by
  intro g hg
  rw [mem_levelOne_iff, mem_finiteLevelOne_iff] at hg ⊢
  have hball : idealBall (𝓞 L) L N ⊆ idealBall (𝓞 L) L N' :=
    fun _ hx w => (hx w).trans (idealBound_mono L h w)
  exact ⟨⟨⟨hg.1.integral, hball hg.1.lowerLeft⟩, hball hg.1.lowerRight⟩,
    ⟨⟨hg.2.integral, hball hg.2.lowerLeft⟩, hball hg.2.lowerRight⟩⟩

theorem principalLevel_mono {N N' : Ideal (𝓞 L)} (h : N ≤ N') :
    principalLevel (𝓞 L) L N ≤ principalLevel (𝓞 L) L N' :=
  inf_le_inf (levelOne_mono L h) (Subgroup.map_mono (levelOne_mono L h))

theorem principalLevel_inf_fin_mono {N N' : Ideal (𝓞 L)} (h : N ≤ N') :
    principalLevel (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L ≤ principalLevel (𝓞 L) L N' ⊓ finiteAdelicGL2Subgroup L :=
  inf_le_inf (principalLevel_mono L h) le_rfl

omit [NumberField L] in
theorem inf_ne_bot {N N' : Ideal (𝓞 L)} (hN : N ≠ ⊥) (hN' : N' ≠ ⊥) : N ⊓ N' ≠ ⊥ := fun h =>
  (mul_ne_zero hN hN') (le_bot_iff.mp (h ▸ (Ideal.mul_le_inf : N * N' ≤ N ⊓ N')))

end Levels

section Shift

variable (L : Type) [Field L] [NumberField L]

attribute [local instance] NumberField.AdelicHaar.adeleBorel

set_option quotPrecheck false in
local notation "αL" => (((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 L) L))).toHomUnits)

theorem shift_family (hα : ∀ x, 0 < ((αL x : ℝˣ) : ℝ)) (μ ν : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ) (a : ℂ)
    (μ₁ ν₁ : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ) (hμ₁ : μ₁ = μ * cpowChar αL hα a) (hν₁ : ν₁ = ν * cpowChar αL hα (-a))
    (N N' : Ideal (𝓞 L)) (hNN' : N' ≤ N)
    (f : ℂ → AdelicGL2 (𝓞 L) L → ℂ)
    (hf : ∀ s, IsInducedSection (𝓞 L) L (etaFst μ αL hα s) (etaSnd ν αL hα s) (f s))
    (hfK : ∀ s, IsArchKFinite L (f s))
    (hff : ∀ s, IsKfSmooth L (f s))
    (hfjc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 L) L => f p.1 p.2))
    (hfhol : ∀ g, Differentiable ℂ (fun s => f s g))
    (hfKu : ∀ w : InfinitePlace L, ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup L w) → ℂ),
      FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 L) L),
        (fun k : ↥(archRowIsometrySubgroup L w) => f s (g * (k : AdelicGL2 (𝓞 L) L))) ∈ W)
    (hflat : ∀ (s : ℂ) (k : adelicMaximalCompact L),
      f s (k : AdelicGL2 (𝓞 L) L) = f 0 (k : AdelicGL2 (𝓞 L) L))
    (hflev : ∀ (s : ℂ) (g : AdelicGL2 (𝓞 L) L),
      ∀ u ∈ principalLevel (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L, f s (g * u) = f s g) :
    (∀ s, IsInducedSection (𝓞 L) L (etaFst μ₁ αL hα s)
      (etaSnd ν₁ αL hα s) ((fun s g => f (s + a) g) s)) ∧
    (∀ s, IsArchKFinite L ((fun s g => f (s + a) g) s)) ∧
    (∀ s, IsKfSmooth L ((fun s g => f (s + a) g) s)) ∧
    Continuous (fun p : ℂ × AdelicGL2 (𝓞 L) L => (fun s g => f (s + a) g) p.1 p.2) ∧
    (∀ g, Differentiable ℂ (fun s => (fun s g => f (s + a) g) s g)) ∧
    (∀ w : InfinitePlace L, ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup L w) → ℂ),
      FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 L) L),
        (fun k : ↥(archRowIsometrySubgroup L w) => (fun s g => f (s + a) g) s (g * (k : AdelicGL2 (𝓞 L) L))) ∈ W) ∧
    (∀ (s : ℂ) (k : adelicMaximalCompact L),
      (fun s g => f (s + a) g) s (k : AdelicGL2 (𝓞 L) L) = (fun s g => f (s + a) g) 0 (k : AdelicGL2 (𝓞 L) L)) ∧
    (∀ (s : ℂ) (g : AdelicGL2 (𝓞 L) L),
      ∀ u ∈ principalLevel (𝓞 L) L N' ⊓ finiteAdelicGL2Subgroup L,
        (fun s g => f (s + a) g) s (g * u) = (fun s g => f (s + a) g) s g) := by
  refine ⟨fun s => ?_, fun s => hfK (s + a), fun s => hff (s + a), ?_, fun g => ?_, fun w => ?_, fun s k => ?_,
    fun s g u hu => hflev (s + a) g u (principalLevel_inf_fin_mono L hNN' hu)⟩
  · rw [hμ₁, hν₁, etaFst_mul_cpowChar, etaSnd_mul_cpowChar]; exact hf (s + a)
  · exact hfjc.comp ((continuous_fst.add continuous_const).prodMk continuous_snd)
  · exact (hfhol g).comp (differentiable_id.add_const a)
  · obtain ⟨W, hW, hmem⟩ := hfKu w
    exact ⟨W, hW, fun s g => hmem (s + a) g⟩
  · show f (s + a) k = f (0 + a) k
    rw [hflat (s + a) k, hflat (0 + a) k]

theorem shift_continuation (a : ℂ) (ha : a.re = 0)
    (f : ℂ → AdelicGL2 (𝓞 L) L → ℂ) (O : Set ℂ) (E Nn : ℂ → AdelicGL2 (𝓞 L) L → ℂ)
    (h : IsOpen O ∧ IsPreconnected O ∧ {s : ℂ | s.re = 0} ⊆ O ∧ {s : ℂ | 1 / 2 < s.re} ⊆ O ∧
      (∀ g : AdelicGL2 (𝓞 L) L, AnalyticOnNhd ℂ (fun s => E s g) O) ∧
      (∀ g : AdelicGL2 (𝓞 L) L, AnalyticOnNhd ℂ (fun s => Nn s g) O) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 L) L => E p.1 p.2) (O ×ˢ Set.univ) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 L) L => Nn p.1 p.2) (O ×ˢ Set.univ) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 L) L,
        E s g = f s g + ∑' ξ : L, f s (adelicWeyl (𝓞 L) L
          * unipotentGL2 (algebraMap L (AdeleRing (𝓞 L) L) ξ) * g)) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 L) L,
        Nn s g = weylIntertwiningIntegral (𝓞 L) L (adelicAddHaar (𝓞 L) L) (f s) g)) :
    IsOpen {s : ℂ | s + a ∈ O} ∧ IsPreconnected {s : ℂ | s + a ∈ O} ∧
      {s : ℂ | s.re = 0} ⊆ {s : ℂ | s + a ∈ O} ∧ {s : ℂ | 1 / 2 < s.re} ⊆ {s : ℂ | s + a ∈ O} ∧
      (∀ g : AdelicGL2 (𝓞 L) L, AnalyticOnNhd ℂ (fun s => (fun s g => E (s + a) g) s g) {s : ℂ | s + a ∈ O}) ∧
      (∀ g : AdelicGL2 (𝓞 L) L, AnalyticOnNhd ℂ (fun s => (fun s g => Nn (s + a) g) s g) {s : ℂ | s + a ∈ O}) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 L) L => (fun s g => E (s + a) g) p.1 p.2) ({s : ℂ | s + a ∈ O} ×ˢ Set.univ) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 L) L => (fun s g => Nn (s + a) g) p.1 p.2) ({s : ℂ | s + a ∈ O} ×ˢ Set.univ) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 L) L,
        (fun s g => E (s + a) g) s g = (fun s g => f (s + a) g) s g + ∑' ξ : L, (fun s g => f (s + a) g) s (adelicWeyl (𝓞 L) L
          * unipotentGL2 (algebraMap L (AdeleRing (𝓞 L) L) ξ) * g)) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 L) L,
        (fun s g => Nn (s + a) g) s g =
          weylIntertwiningIntegral (𝓞 L) L (adelicAddHaar (𝓞 L) L) ((fun s g => f (s + a) g) s) g) := by
  obtain ⟨hO, hOc, hax, hhalf, hEan, hNan, hEc, hNc, hEf, hNf⟩ := h
  have hpre : {s : ℂ | s + a ∈ O} = (Homeomorph.addRight a) ⁻¹' O := rfl
  have hre : ∀ s : ℂ, (s + a).re = s.re := fun s => by rw [Complex.add_re, ha, add_zero]
  have hmaps : Set.MapsTo (fun s : ℂ => s + a) {s : ℂ | s + a ∈ O} O := fun s hs => hs
  have hcsh : Continuous fun p : ℂ × AdelicGL2 (𝓞 L) L => (p.1 + a, p.2) :=
    (continuous_fst.add continuous_const).prodMk continuous_snd
  have hmaps2 : Set.MapsTo (fun p : ℂ × AdelicGL2 (𝓞 L) L => (p.1 + a, p.2))
      ({s : ℂ | s + a ∈ O} ×ˢ Set.univ) (O ×ˢ Set.univ) :=
    fun p hp => ⟨hp.1, Set.mem_univ _⟩
  refine ⟨?_, ?_, fun s hs => ?_, fun s hs => ?_, fun g => ?_, fun g => ?_, ?_, ?_, fun s hs g => ?_, fun s hs g => ?_⟩
  · rw [hpre]; exact (Homeomorph.addRight a).continuous.isOpen_preimage O hO
  · rw [hpre]; exact (Homeomorph.addRight a).isPreconnected_preimage.mpr hOc
  · show s + a ∈ O
    exact hax (show (s + a).re = 0 by rw [hre]; exact hs)
  · show s + a ∈ O
    exact hhalf (show 1 / 2 < (s + a).re by rw [hre]; exact hs)
  · exact (hEan g).comp (analyticOnNhd_id.add analyticOnNhd_const) hmaps
  · exact (hNan g).comp (analyticOnNhd_id.add analyticOnNhd_const) hmaps
  · exact hEc.comp hcsh.continuousOn hmaps2
  · exact hNc.comp hcsh.continuousOn hmaps2
  · exact hEf (s + a) (by rw [hre]; exact hs) g
  · exact hNf (s + a) (by rw [hre]; exact hs) g

end Shift

end R4AdjSigma

end

open AutomorphicForm R4AdjSigma in
open scoped TensorProduct.RightActions in
theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (N : Ideal (𝓞 L)) (_hN : N ≠ ⊥) :
    let αm : (AdeleRing (𝓞 L) L)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 L) L))).toHomUnits
    letI := adeleBorel (𝓞 L) L
    ∀ (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ)
      (_hμ : IsUnitaryChar (𝓞 L) L μ) (_hν : IsUnitaryChar (𝓞 L) L ν)
      (_hμF : IsIdeleClassChar (𝓞 L) L μ) (_hνF : IsIdeleClassChar (𝓞 L) L ν)
      (_hμk : Continuous fun x : (AdeleRing (𝓞 L) L)ˣ => ((μ x : ℂˣ) : ℂ))
      (_hνk : Continuous fun x : (AdeleRing (𝓞 L) L)ˣ => ((ν x : ℂˣ) : ℂ))
      (φf : ℂ → AdelicGL2 (𝓞 L) L → ℂ)
      (_hφf : ∀ s, IsInducedSection (𝓞 L) L (etaFst μ αm hαm s) (etaSnd ν αm hαm s) (φf s))
      (_hφfK : ∀ s, IsArchKFinite L (φf s))
      (_hφff : ∀ s, IsKfSmooth L (φf s))
      (_hφfjc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 L) L => φf p.1 p.2))
      (_hφfhol : ∀ g, Differentiable ℂ (fun s => φf s g))
      (_hφfKu : ∀ w : InfinitePlace L, ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup L w) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 L) L),
          (fun k : ↥(archRowIsometrySubgroup L w) => φf s (g * (k : AdelicGL2 (𝓞 L) L))) ∈ W)
      (_hφflat : ∀ (s : ℂ) (k : adelicMaximalCompact L),
        φf s (k : AdelicGL2 (𝓞 L) L) = φf 0 (k : AdelicGL2 (𝓞 L) L))
      (_hφflev : ∀ (s : ℂ) (g : AdelicGL2 (𝓞 L) L),
        ∀ u ∈ principalLevel (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L, φf s (g * u) = φf s g)
      (ψf : ℂ → AdelicGL2 (𝓞 L) L → ℂ)
      (_hψf : ∀ s, IsInducedSection (𝓞 L) L (etaFst μ αm hαm s) (etaSnd ν αm hαm s) (ψf s))
      (_hψfK : ∀ s, IsArchKFinite L (ψf s))
      (_hψff : ∀ s, IsKfSmooth L (ψf s))
      (_hψfjc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 L) L => ψf p.1 p.2))
      (_hψfhol : ∀ g, Differentiable ℂ (fun s => ψf s g))
      (_hψfKu : ∀ w : InfinitePlace L, ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup L w) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 L) L),
          (fun k : ↥(archRowIsometrySubgroup L w) => ψf s (g * (k : AdelicGL2 (𝓞 L) L))) ∈ W)
      (_hψflat : ∀ (s : ℂ) (k : adelicMaximalCompact L),
        ψf s (k : AdelicGL2 (𝓞 L) L) = ψf 0 (k : AdelicGL2 (𝓞 L) L))
      (_hψflev : ∀ (s : ℂ) (g : AdelicGL2 (𝓞 L) L),
        ∀ u ∈ principalLevel (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L, ψf s (g * u) = ψf s g)
      (Oφ : Set ℂ) (Eφ Nφ : ℂ → AdelicGL2 (𝓞 L) L → ℂ)
      (_hEφ :
      IsOpen Oφ ∧ IsPreconnected Oφ ∧ {s : ℂ | s.re = 0} ⊆ Oφ ∧ {s : ℂ | 1 / 2 < s.re} ⊆ Oφ ∧
      (∀ g : AdelicGL2 (𝓞 L) L, AnalyticOnNhd ℂ (fun s => Eφ s g) Oφ) ∧
      (∀ g : AdelicGL2 (𝓞 L) L, AnalyticOnNhd ℂ (fun s => Nφ s g) Oφ) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 L) L => Eφ p.1 p.2) (Oφ ×ˢ Set.univ) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 L) L => Nφ p.1 p.2) (Oφ ×ˢ Set.univ) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 L) L,
        Eφ s g = φf s g + ∑' ξ : L, φf s (adelicWeyl (𝓞 L) L
          * unipotentGL2 (algebraMap L (AdeleRing (𝓞 L) L) ξ) * g)) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 L) L,
        Nφ s g = weylIntertwiningIntegral (𝓞 L) L (adelicAddHaar (𝓞 L) L) (φf s) g))
      (Oψ : Set ℂ) (Eψ Nψ : ℂ → AdelicGL2 (𝓞 L) L → ℂ)
      (_hEψ :
      IsOpen Oψ ∧ IsPreconnected Oψ ∧ {s : ℂ | s.re = 0} ⊆ Oψ ∧ {s : ℂ | 1 / 2 < s.re} ⊆ Oψ ∧
      (∀ g : AdelicGL2 (𝓞 L) L, AnalyticOnNhd ℂ (fun s => Eψ s g) Oψ) ∧
      (∀ g : AdelicGL2 (𝓞 L) L, AnalyticOnNhd ℂ (fun s => Nψ s g) Oψ) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 L) L => Eψ p.1 p.2) (Oψ ×ˢ Set.univ) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 L) L => Nψ p.1 p.2) (Oψ ×ˢ Set.univ) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 L) L,
        Eψ s g = ψf s g + ∑' ξ : L, ψf s (adelicWeyl (𝓞 L) L
          * unipotentGL2 (algebraMap L (AdeleRing (𝓞 L) L) ξ) * g)) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 L) L,
        Nψ s g = weylIntertwiningIntegral (𝓞 L) L (adelicAddHaar (𝓞 L) L) (ψf s) g)),
      ((∀ z : (AdeleRing (𝓞 L) L)ˣ, μ (D.unitsAct σ.symm z) = μ z) → (∀ z : (AdeleRing (𝓞 L) L)ˣ, ν (D.unitsAct σ.symm z) = ν z) →
        ∀ θ : ℝ, (∀ z : (AdeleRing (𝓞 L) L)ˣ, μ z = ν z * cpowChar αm hαm ((θ : ℂ) * Complex.I) z) →
        (∫ k, φf (((-(θ / 2) : ℝ) : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 L) L) * conj ((fun g => ((((adelicAddHaar (𝓞 L) L) (adelicBox L)).toReal : ℂ))⁻¹ * Nψ (((-(θ / 2) : ℝ) : ℂ) * Complex.I) g) (AutomorphicForm.sigmaAdelicAct K L D σ.symm (k : AdelicGL2 (𝓞 L) L))) ∂(AutomorphicForm.maximalCompactHaar L)) =
        (∫ k, (fun g => ((((adelicAddHaar (𝓞 L) L) (adelicBox L)).toReal : ℂ))⁻¹ * Nφ (((-(θ / 2) : ℝ) : ℂ) * Complex.I) g) (k : AdelicGL2 (𝓞 L) L) * conj (ψf (((-(θ / 2) : ℝ) : ℂ) * Complex.I) (AutomorphicForm.sigmaAdelicAct K L D σ.symm (k : AdelicGL2 (𝓞 L) L))) ∂(AutomorphicForm.maximalCompactHaar L))) ∧
      (∀ τ : ℝ, (∀ z : (AdeleRing (𝓞 L) L)ˣ, μ (D.unitsAct σ.symm z) = ν z * cpowChar αm hαm ((τ : ℂ) * Complex.I) z) →
        (∀ z : (AdeleRing (𝓞 L) L)ˣ, ν (D.unitsAct σ.symm z) = μ z * cpowChar αm hαm (-((τ : ℂ) * Complex.I)) z) →
        (∃ z : (AdeleRing (𝓞 L) L)ˣ, μ (D.unitsAct σ.symm z) ≠ μ z ∨ ν (D.unitsAct σ.symm z) ≠ ν z) →
        (∫ k, φf (((-(τ / 2) : ℝ) : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 L) L) * conj ((fun g => ((((adelicAddHaar (𝓞 L) L) (adelicBox L)).toReal : ℂ))⁻¹ * Nψ (((-(τ / 2) : ℝ) : ℂ) * Complex.I) g) (AutomorphicForm.sigmaAdelicAct K L D σ.symm (k : AdelicGL2 (𝓞 L) L))) ∂(AutomorphicForm.maximalCompactHaar L)) =
        (∫ k, (fun g => ((((adelicAddHaar (𝓞 L) L) (adelicBox L)).toReal : ℂ))⁻¹ * Nφ (((-(τ / 2) : ℝ) : ℂ) * Complex.I) g) (k : AdelicGL2 (𝓞 L) L) * conj (ψf (((-(τ / 2) : ℝ) : ℂ) * Complex.I) (AutomorphicForm.sigmaAdelicAct K L D σ.symm (k : AdelicGL2 (𝓞 L) L))) ∂(AutomorphicForm.maximalCompactHaar L))) := by
  intro αm hαm μ ν hμ hν hμF hνF hμk hνk φf hφf hφfK hφff hφfjc hφfhol hφfKu _hφflat hφflev
    ψf hψf hψfK hψff hψfjc hψfhol hψfKu hψflat hψflev Oφ Eφ Nφ hEφ Oψ Eψ Nψ hEψ

  have hNσ0 : N.comap (MulSemiringAction.toRingEquiv (L ≃ₐ[K] L) (𝓞 L) σ.symm : 𝓞 L →+* 𝓞 L) ≠ ⊥ := by
    intro h
    obtain ⟨x, hxN, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot _hN
    have hx : (MulSemiringAction.toRingEquiv (L ≃ₐ[K] L) (𝓞 L) σ.symm).symm x ∈
        N.comap (MulSemiringAction.toRingEquiv (L ≃ₐ[K] L) (𝓞 L) σ.symm : 𝓞 L →+* 𝓞 L) := by
      rw [Ideal.mem_comap]
      show (MulSemiringAction.toRingEquiv (L ≃ₐ[K] L) (𝓞 L) σ.symm)
        ((MulSemiringAction.toRingEquiv (L ≃ₐ[K] L) (𝓞 L) σ.symm).symm x) ∈ N
      rw [RingEquiv.apply_symm_apply]; exact hxN
    rw [h, Ideal.mem_bot] at hx
    apply hx0
    have := congrArg (MulSemiringAction.toRingEquiv (L ≃ₐ[K] L) (𝓞 L) σ.symm) hx
    rwa [RingEquiv.apply_symm_apply, map_zero] at this
  have hN₀0 : N ⊓ N.comap (MulSemiringAction.toRingEquiv (L ≃ₐ[K] L) (𝓞 L) σ.symm : 𝓞 L →+* 𝓞 L) ≠ ⊥ :=
    inf_ne_bot L _hN hNσ0
  have hφflev₀ : ∀ (s : ℂ) (g : AdelicGL2 (𝓞 L) L),
      ∀ u ∈ principalLevel (𝓞 L) L
          (N ⊓ N.comap (MulSemiringAction.toRingEquiv (L ≃ₐ[K] L) (𝓞 L) σ.symm : 𝓞 L →+* 𝓞 L)) ⊓
        finiteAdelicGL2Subgroup L, φf s (g * u) = φf s g :=
    fun s g u hu => hφflev s g u (principalLevel_inf_fin_mono L inf_le_left hu)
  refine ⟨?_, ?_⟩
  ·
    intro hμinv hνinv θ hθ
    obtain ⟨T1, T2, T3, T4, T5, T6, T7, T8, T9⟩ :=
      AutomorphicForm.isInducedSection_and_isArchKFinite_and_axis_continuation_comp_sigmaAdelicAct_symm_of_flat_family_of_principalLevel
        K L D σ N hαm μ ν μ ν (fun z => (hμinv z).symm) (fun z => (hνinv z).symm)
        ψf hψf hψfK hψff hψfjc hψfhol hψfKu hψflat hψflev Oψ Eψ Nψ hEψ
    have hθ' : μ = ν * cpowChar αm hαm ((θ : ℂ) * Complex.I) := MonoidHom.ext hθ
    have hnare : ((-((θ : ℂ) * Complex.I))).re = 0 := by simp [Complex.mul_re]
    obtain ⟨B1, B2, B3, B4, B5, B6, _B7, B8⟩ :=
      shift_family L hαm μ ν (-((θ : ℂ) * Complex.I)) ν μ
        (by rw [hθ']; exact (mul_cpowChar_mul_cpowChar_neg L hαm ν ((θ : ℂ) * Complex.I)).symm)
        (by rw [neg_neg]; exact hθ')
        _ _ inf_le_right (fun s g => ψf s (AutomorphicForm.sigmaAdelicAct K L D σ.symm g)) T1 T2 T3 T4 T5 T6 T7 T8
    have CB := shift_continuation L (-((θ : ℂ) * Complex.I)) hnare (fun s g => ψf s (AutomorphicForm.sigmaAdelicAct K L D σ.symm g)) Oψ
      (fun s g => Eψ s (AutomorphicForm.sigmaAdelicAct K L D σ.symm g)) (fun s g => Nψ s (AutomorphicForm.sigmaAdelicAct K L D σ.symm g)) T9
    have H := AutomorphicForm.integral_mul_conj_axis_continuation_weylIntertwiningIntegral_eq_of_swap_pair_of_principalLevel_of_ne_bot
      L _ hN₀0 hαm μ ν hμ hν hμF hνF hμk hνk
      φf hφf hφfK hφff hφfjc hφfhol hφfKu hφflev₀
      (fun s g => ψf (s + (-((θ : ℂ) * Complex.I))) (AutomorphicForm.sigmaAdelicAct K L D σ.symm g)) B1 B2 B3 B4 B5 B6 B8
      Oφ Eφ Nφ hEφ
      {s : ℂ | s + (-((θ : ℂ) * Complex.I)) ∈ Oψ} (fun s g => Eψ (s + (-((θ : ℂ) * Complex.I))) (AutomorphicForm.sigmaAdelicAct K L D σ.symm g))
      (fun s g => Nψ (s + (-((θ : ℂ) * Complex.I))) (AutomorphicForm.sigmaAdelicAct K L D σ.symm g)) CB (-(θ / 2))
    have hc : -((((-(θ / 2) : ℝ) : ℂ)) * Complex.I) + (-((θ : ℂ) * Complex.I)) = ((((-(θ / 2) : ℝ) : ℂ)) * Complex.I) := by push_cast; ring
    simp only [hc] at H
    simp only []
    exact H
  ·
    intro τ h1 h2 _h3
    have hbre : (((τ : ℂ) * Complex.I)).re = 0 := by simp [Complex.mul_re]
    have hnbre : ((-((τ : ℂ) * Complex.I))).re = 0 := by rw [Complex.neg_re, hbre, neg_zero]
    obtain ⟨T1, T2, T3, T4, T5, T6, T7, T8, T9⟩ :=
      AutomorphicForm.isInducedSection_and_isArchKFinite_and_axis_continuation_comp_sigmaAdelicAct_symm_of_flat_family_of_principalLevel
        K L D σ N hαm μ ν (ν * cpowChar αm hαm ((τ : ℂ) * Complex.I)) (μ * cpowChar αm hαm (-((τ : ℂ) * Complex.I)))
        (fun z => by rw [MonoidHom.mul_apply]; exact (h1 z).symm)
        (fun z => by rw [MonoidHom.mul_apply]; exact (h2 z).symm)
        ψf hψf hψfK hψff hψfjc hψfhol hψfKu hψflat hψflev Oψ Eψ Nψ hEψ
    obtain ⟨B1, B2, B3, B4, B5, B6, _B7, B8⟩ :=
      shift_family L hαm (ν * cpowChar αm hαm ((τ : ℂ) * Complex.I)) (μ * cpowChar αm hαm (-((τ : ℂ) * Complex.I))) (-((τ : ℂ) * Complex.I)) ν μ
        (mul_cpowChar_mul_cpowChar_neg L hαm ν ((τ : ℂ) * Complex.I)).symm (mul_cpowChar_mul_cpowChar_neg L hαm μ (-((τ : ℂ) * Complex.I))).symm
        _ _ inf_le_right (fun s g => ψf s (AutomorphicForm.sigmaAdelicAct K L D σ.symm g)) T1 T2 T3 T4 T5 T6 T7 T8
    have CB := shift_continuation L (-((τ : ℂ) * Complex.I)) hnbre (fun s g => ψf s (AutomorphicForm.sigmaAdelicAct K L D σ.symm g)) Oψ
      (fun s g => Eψ s (AutomorphicForm.sigmaAdelicAct K L D σ.symm g)) (fun s g => Nψ s (AutomorphicForm.sigmaAdelicAct K L D σ.symm g)) T9
    have H := AutomorphicForm.integral_mul_conj_axis_continuation_weylIntertwiningIntegral_eq_of_swap_pair_of_principalLevel_of_ne_bot
      L _ hN₀0 hαm μ ν hμ hν hμF hνF hμk hνk
      φf hφf hφfK hφff hφfjc hφfhol hφfKu hφflev₀
      (fun s g => ψf (s + (-((τ : ℂ) * Complex.I))) (AutomorphicForm.sigmaAdelicAct K L D σ.symm g)) B1 B2 B3 B4 B5 B6 B8
      Oφ Eφ Nφ hEφ
      {s : ℂ | s + (-((τ : ℂ) * Complex.I)) ∈ Oψ} (fun s g => Eψ (s + (-((τ : ℂ) * Complex.I))) (AutomorphicForm.sigmaAdelicAct K L D σ.symm g))
      (fun s g => Nψ (s + (-((τ : ℂ) * Complex.I))) (AutomorphicForm.sigmaAdelicAct K L D σ.symm g)) CB (-(τ / 2))
    have hc : -((((-(τ / 2) : ℝ) : ℂ)) * Complex.I) + (-((τ : ℂ) * Complex.I)) = ((((-(τ / 2) : ℝ) : ℂ)) * Complex.I) := by push_cast; ring
    simp only [hc] at H
    simp only []
    exact H

end S_AutomorphicForm_integral_mul_conj_weylIntertwiningIntegral_sigmaAdelicAct_eq_of_sigmaInvariant_and_of_sigmaReversed_of_principalLevel_of_ne_bot
end P2MW
export P2MW.S_AutomorphicForm_integral_mul_conj_weylIntertwiningIntegral_sigmaAdelicAct_eq_of_sigmaInvariant_and_of_sigmaReversed_of_principalLevel_of_ne_bot (solution)
