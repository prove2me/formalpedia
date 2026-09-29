-- Prove2me | solution 1 for AutomorphicForm.analyticOnNhd_and_continuousOn_weylIntertwiningIntegral_family_of_re_gt_half
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/94de42fb-32e9-5c6b-bcab-dfd4ec5e6a0c

import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_RowIsometryInvariance
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Mathlib.MeasureTheory.Measure.Haar.DistribChar
import Mathlib.Analysis.Meromorphic.Order
import Theorems.Thm_AutomorphicForm_exists_mem_adelicBorel_mul_eq
import Theorems.Thm_AutomorphicForm_isInducedSection_adelicHeight_cpow
import Theorems.Thm_AutomorphicForm_weylIntertwiningIntegrand_integrable_of_re_gt_half
import Theorems.Thm_NumberField_AdelicHeight_exists_forall_mul_adelicHeight_le_adelicHeight_mul_of_isCompact
import Theorems.Thm_AutomorphicForm_isInducedSection_indicator_bottomRow_mul_adelicHeight_cpow
import Theorems.Thm_AutomorphicForm_weylIntertwiningIntegral_meromorphicOn_of_isInducedSection_family
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_analyticOnNhd_and_continuousOn_weylIntertwiningIntegral_family_of_re_gt_half
p2m_attr_erase "instance" "instCountableOfNumberField_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions"
p2m_attr_erase "simp" "LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply LanglandsTunnell.TateLocal.conductorExponentAt_one LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq LanglandsTunnell.ArchPlace.complexTestFun_zero_apply LanglandsTunnell.ArchPlace.norm_anglePhase LanglandsTunnell.ArchPlace.realTestFun_zero_apply"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicHeight NumberField.AdelicLevel
p2m_open "AutomorphicForm P2MW.S_AutomorphicForm_analyticOnNhd_and_continuousOn_weylIntertwiningIntegral_family_of_re_gt_half.AutomorphicForm"
open scoped NNReal

namespace SphericalCollapse

p2m_open "IsDedekindDomain AutomorphicForm P2MW.S_AutomorphicForm_analyticOnNhd_and_continuousOn_weylIntertwiningIntegral_family_of_re_gt_half.AutomorphicForm AutomorphicForm.WindowedSiegel"

section Local

variable {K : Type*} [NormedField K] [IsUltrametricDist K]

private theorem rowMaxNorm_mul_le_of_entries (g k : GL (Fin 2) K)
    (hk : ∀ i j, ‖(k : Matrix (Fin 2) (Fin 2) K) i j‖ ≤ 1) :
    rowMaxNorm ((g * k : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
      ≤ rowMaxNorm (g : Matrix (Fin 2) (Fin 2) K) := by
  have hcoe : ((g * k : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
      = (g : Matrix (Fin 2) (Fin 2) K) * (k : Matrix (Fin 2) (Fin 2) K) := rfl
  have hentry : ∀ j : Fin 2,
      ‖((g : Matrix (Fin 2) (Fin 2) K) * (k : Matrix (Fin 2) (Fin 2) K)) 1 j‖
        ≤ rowMaxNorm (g : Matrix (Fin 2) (Fin 2) K) := by
    intro j
    rw [Matrix.mul_apply, Fin.sum_univ_two]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · rw [norm_mul]
      calc ‖(g : Matrix (Fin 2) (Fin 2) K) 1 0‖ * ‖(k : Matrix (Fin 2) (Fin 2) K) 0 j‖
          ≤ ‖(g : Matrix (Fin 2) (Fin 2) K) 1 0‖ * 1 :=
            mul_le_mul_of_nonneg_left (hk 0 j) (norm_nonneg _)
        _ = ‖(g : Matrix (Fin 2) (Fin 2) K) 1 0‖ := mul_one _
        _ ≤ rowMaxNorm (g : Matrix (Fin 2) (Fin 2) K) := le_max_left _ _
    · rw [norm_mul]
      calc ‖(g : Matrix (Fin 2) (Fin 2) K) 1 1‖ * ‖(k : Matrix (Fin 2) (Fin 2) K) 1 j‖
          ≤ ‖(g : Matrix (Fin 2) (Fin 2) K) 1 1‖ * 1 :=
            mul_le_mul_of_nonneg_left (hk 1 j) (norm_nonneg _)
        _ = ‖(g : Matrix (Fin 2) (Fin 2) K) 1 1‖ := mul_one _
        _ ≤ rowMaxNorm (g : Matrix (Fin 2) (Fin 2) K) := le_max_right _ _
  rw [hcoe]
  exact max_le (hentry 0) (hentry 1)

private theorem finLocalHeight_mul_of_entries (g k : GL (Fin 2) K)
    (hk : ∀ i j, ‖(k : Matrix (Fin 2) (Fin 2) K) i j‖ ≤ 1)
    (hk' : ∀ i j, ‖((k⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) i j‖ ≤ 1) :
    finLocalHeight (g * k) = finLocalHeight g := by
  have h1 := rowMaxNorm_mul_le_of_entries g k hk
  have h2 := rowMaxNorm_mul_le_of_entries (g * k) k⁻¹ hk'
  rw [mul_inv_cancel_right] at h2
  have hrow : rowMaxNorm ((g * k : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
      = rowMaxNorm (g : Matrix (Fin 2) (Fin 2) K) := le_antisymm h1 h2
  have hd : ‖(k : Matrix (Fin 2) (Fin 2) K).det‖ ≤ 1 := norm_det_le_one hk
  have hd' : ‖((k⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det‖ ≤ 1 := norm_det_le_one hk'
  have hcoe_inv : (k : Matrix (Fin 2) (Fin 2) K) * ((k⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
      = ((k * k⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) := rfl
  have hprod : ‖(k : Matrix (Fin 2) (Fin 2) K).det‖
      * ‖((k⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det‖ = 1 := by
    rw [← norm_mul, ← Matrix.det_mul, hcoe_inv, mul_inv_cancel, Units.val_one, Matrix.det_one,
      norm_one]
  have hdet1 : ‖(k : Matrix (Fin 2) (Fin 2) K).det‖ = 1 := by
    refine le_antisymm hd ?_
    by_contra hlt
    push Not at hlt
    have := mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) hlt hd'
    rw [hprod] at this
    exact lt_irrefl _ this
  have hcoe : ((g * k : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
      = (g : Matrix (Fin 2) (Fin 2) K) * (k : Matrix (Fin 2) (Fin 2) K) := rfl
  have hdetmul : ‖((g * k : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det‖
      = ‖(g : Matrix (Fin 2) (Fin 2) K).det‖ := by
    rw [hcoe, Matrix.det_mul, norm_mul, hdet1, mul_one]
  unfold finLocalHeight
  rw [hdetmul, hrow]

end Local

section Adelic

variable (F : Type) [Field F] [NumberField F]

private theorem finHeight_mul_of_mem (g : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F))
    {k : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)} (hk : k ∈ finiteIntegralGL2 (𝓞 F) F) :
    finHeight F (g * k) = finHeight F g := by
  rw [mem_finiteIntegralGL2_iff] at hk
  unfold finHeight
  refine finprod_congr fun v => ?_
  rw [map_mul]
  refine finLocalHeight_mul_of_entries _ _ (fun i j => ?_) (fun i j => ?_)
  · rw [finComponent_apply]
    exact norm_le_one_of_mem_adicCompletionIntegers (hk.1 i j v)
  · rw [← map_inv, finComponent_apply]
    exact norm_le_one_of_mem_adicCompletionIntegers (hk.2 i j v)

private theorem adelicHeight_mul_of_mem (g : AdelicGL2 (𝓞 F) F) {k : AdelicGL2 (𝓞 F) F}
    (hkf : glFin (𝓞 F) F k ∈ finiteIntegralGL2 (𝓞 F) F)
    (hkinf : ∀ w : InfinitePlace F, IsRowIsometry (archComponent F w (glArch (𝓞 F) F k))) :
    adelicHeight F (g * k) = adelicHeight F g := by
  unfold adelicHeight
  rw [map_mul, map_mul, archHeight_mul_rowIsometry F _ hkinf, finHeight_mul_of_mem F _ hkf]

private theorem adelicHeight_one' : adelicHeight F (1 : AdelicGL2 (𝓞 F) F) = 1 := by
  unfold adelicHeight
  rw [map_one, map_one, archHeight_one, finHeight_eq_one_of_mem (one_mem _), mul_one]

end Adelic

end SphericalCollapse

namespace AutomorphicForm
p2m_export "AutomorphicForm" "IsInducedSection AdelicGL2 IsIdeleClassChar IsUnitaryChar unipotentGL2 norm_cpowChar_apply etaFst etaSnd etaSnd_apply norm_etaFst_apply_of_unitary adelicWeyl weylIntertwiningIntegral IsKfSmooth IsArchKFinite adelicMaximalCompact isCompact_adelicMaximalCompact exists_mem_adelicBorel_mul_eq isInducedSection_adelicHeight_cpow weylIntertwiningIntegrand_integrable_of_re_gt_half isInducedSection_indicator_bottomRow_mul_adelicHeight_cpow weylIntertwiningIntegral_meromorphicOn_of_isInducedSection_family"
namespace HolM
p2m_open "AutomorphicForm"

open IsDedekindDomain

variable (F : Type) [Field F] [NumberField F]

theorem countable_ideal : Countable (Ideal (𝓞 F)) := by
  have h : (Set.univ : Set (Ideal (𝓞 F))) = ⋃ n : ℕ, {I : Ideal (𝓞 F) | Ideal.absNorm I = n} := by
    ext I
    simp only [Set.mem_univ, Set.mem_iUnion, Set.mem_setOf_eq, true_iff]
    exact ⟨_, rfl⟩
  rw [← Set.countable_univ_iff, h]
  exact Set.countable_iUnion fun n => (Ideal.finite_setOf_absNorm_eq n).countable

theorem countable_heightOneSpectrum : Countable (HeightOneSpectrum (𝓞 F)) := by
  haveI := countable_ideal F
  exact Function.Injective.countable fun v w (h : v.asIdeal = w.asIdeal) => HeightOneSpectrum.ext h

theorem firstCountableTopology_finiteAdeleRing : FirstCountableTopology (FiniteAdeleRing (𝓞 F) F) := by
  haveI := countable_heightOneSpectrum F
  refine ⟨fun x => ?_⟩

  set S : Set (HeightOneSpectrum (𝓞 F)) := {v | x v ∈ (v.adicCompletionIntegers F : Set (v.adicCompletion F))}
    with hS
  have hSc : Filter.cofinite ≤ Filter.principal S := Filter.le_principal_iff.2 x.2
  let x' : RestrictedProduct (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) (Filter.principal S) :=
    ⟨fun v => x v, Filter.eventually_principal.2 fun v hv => hv⟩
  have hx : RestrictedProduct.inclusion (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) hSc x' = x := rfl
  have hopen : ∀ v : HeightOneSpectrum (𝓞 F), IsOpen (v.adicCompletionIntegers F : Set (v.adicCompletion F)) :=
    fun v => Valued.isOpen_valuationSubring _
  haveI : (nhds x').IsCountablyGenerated := by
    rw [RestrictedProduct.isEmbedding_coe_of_principal.nhds_eq_comap x']
    exact Filter.comap.isCountablyGenerated _ _
  have h := RestrictedProduct.nhds_eq_map_inclusion hopen hSc x'
  have key := h.symm ▸ Filter.map.isCountablyGenerated (nhds x')
    (RestrictedProduct.inclusion (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) hSc)
  rw [← hx]
  exact key

theorem firstCountableTopology_adeleRing : FirstCountableTopology (AdeleRing (𝓞 F) F) := by
  haveI := firstCountableTopology_finiteAdeleRing F
  haveI : FirstCountableTopology (InfiniteAdeleRing F) :=
    inferInstanceAs (FirstCountableTopology ((w : InfinitePlace F) → w.Completion))
  exact inferInstanceAs (FirstCountableTopology (InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F))

theorem firstCountableTopology_adelicGL2 : FirstCountableTopology (AdelicGL2 (𝓞 F) F) := by
  haveI := firstCountableTopology_adeleRing F
  haveI : FirstCountableTopology (Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) :=
    inferInstanceAs (FirstCountableTopology (Fin 2 → Fin 2 → AdeleRing (𝓞 F) F))
  haveI : FirstCountableTopology (Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))ᵐᵒᵖ :=
    ⟨fun m => by
      rw [← MulOpposite.op_unop m, ← MulOpposite.map_op_nhds]
      exact Filter.map.isCountablyGenerated _ _⟩
  refine ⟨fun u => ?_⟩
  rw [Units.isEmbedding_embedProduct.nhds_eq_comap u]
  exact Filter.comap.isCountablyGenerated _ _

end AutomorphicForm.HolM

namespace AutomorphicForm
p2m_export "AutomorphicForm" "IsInducedSection AdelicGL2 IsIdeleClassChar IsUnitaryChar unipotentGL2 norm_cpowChar_apply etaFst etaSnd etaSnd_apply norm_etaFst_apply_of_unitary adelicWeyl weylIntertwiningIntegral IsKfSmooth IsArchKFinite adelicMaximalCompact isCompact_adelicMaximalCompact exists_mem_adelicBorel_mul_eq isInducedSection_adelicHeight_cpow weylIntertwiningIntegrand_integrable_of_re_gt_half isInducedSection_indicator_bottomRow_mul_adelicHeight_cpow weylIntertwiningIntegral_meromorphicOn_of_isInducedSection_family"
namespace HolM
p2m_open "AutomorphicForm"

variable (F : Type) [Field F] [NumberField F]

theorem rpow_le_rpow_add_rpow {t q p₁ p₂ : ℝ} (ht : 0 ≤ t) (hp₁ : 0 ≤ p₁) (h₁ : p₁ ≤ q) (h₂ : q ≤ p₂) :
    t ^ q ≤ t ^ p₁ + t ^ p₂ := by
  by_cases h : 1 ≤ t
  · exact le_add_of_nonneg_of_le (Real.rpow_nonneg ht _) (Real.rpow_le_rpow_of_exponent_le h h₂)
  · have h' : t ≤ 1 := le_of_lt (not_le.1 h)
    exact le_add_of_le_of_nonneg (Real.rpow_le_rpow_of_exponent_ge' ht h' hp₁ h₁) (Real.rpow_nonneg ht _)

open SphericalCollapse NumberField.AdelicLevel AutomorphicForm.WindowedSiegel in

theorem family_bound
    (α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ)
    (hαdef : α = ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits)
    (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
    (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (hμ : IsUnitaryChar (𝓞 F) F μ) (hν : IsUnitaryChar (𝓞 F) F ν)
    (φ : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
    (hφ : ∀ s, IsInducedSection (𝓞 F) F (etaFst μ α hα s) (etaSnd ν α hα s) (φ s))
    (hφjc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 F) F => φ p.1 p.2))
    (S : Set ℂ) (hS : IsCompact S) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ S, ∀ g : AdelicGL2 (𝓞 F) F,
      ‖φ s g‖ ≤ C * adelicHeight F g ^ (s.re + 1 / 2) := by
  subst hαdef
  obtain ⟨C₀, hC₀⟩ :=
    (hS.prod (isCompact_adelicMaximalCompact F)).exists_bound_of_continuousOn hφjc.continuousOn
  obtain ⟨-, h1u, hind⟩ := AutomorphicForm.isInducedSection_adelicHeight_cpow F
  refine ⟨max C₀ 0, le_max_right _ _, fun s hs g => ?_⟩
  have hflat := hind hα s
  obtain ⟨b, k, hb, hkf, hkinf, rfl⟩ := AutomorphicForm.exists_mem_adelicBorel_mul_eq F g
  have hk : k ∈ adelicMaximalCompact F := ⟨hkf, hkinf⟩
  have h1 := hφ s b hb k
  have h2 := hflat b hb 1
  simp only [mul_one, adelicHeight_one' F, Complex.ofReal_one, Complex.one_cpow] at h2
  have nF : ∀ (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ), IsUnitaryChar (𝓞 F) F χ → ∀ x,
      ‖((etaFst χ _ hα s x : ℂˣ) : ℂ)‖ =
        ((((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits x
          : ℝˣ) : ℝ) ^ (s.re + 1 / 2) :=
    fun χ hχ x => norm_etaFst_apply_of_unitary hχ _ hα s x
  have nS : ∀ (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ), IsUnitaryChar (𝓞 F) F χ → ∀ x,
      ‖((etaSnd χ _ hα s x : ℂˣ) : ℂ)‖ =
        ((((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits x
          : ℝˣ) : ℝ) ^ (-(s + 1 / 2)).re := by
    intro χ hχ x
    rw [etaSnd_apply, Units.val_mul, norm_mul, hχ x, one_mul, norm_cpowChar_apply]
  have hnorm : ‖φ s (b * k)‖ = ‖((adelicHeight F b : ℝ) : ℂ) ^ (s + 1 / 2)‖ * ‖φ s k‖ := by
    rw [h1, h2, norm_mul, norm_mul, norm_mul, nF μ hμ, nS ν hν, nF 1 h1u, nS 1 h1u]
  rw [hnorm, Complex.norm_cpow_eq_rpow_re_of_pos (adelicHeight_pos b), adelicHeight_mul_of_mem F b hkf hkinf,
    mul_comm]
  have hre : (s + 1 / 2).re = s.re + 1 / 2 := by simp
  rw [hre]
  have hφk : ‖φ s k‖ ≤ max C₀ 0 := (hC₀ (s, k) ⟨hs, hk⟩).trans (le_max_left _ _)
  exact mul_le_mul_of_nonneg_right hφk (Real.rpow_nonneg (adelicHeight_pos b).le _)

end AutomorphicForm.HolM

theorem solution
    (F : Type) [Field F] [NumberField F] :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∀ (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
      (_hμ : IsUnitaryChar (𝓞 F) F μ) (_hν : IsUnitaryChar (𝓞 F) F ν)
      (_hμic : IsIdeleClassChar (𝓞 F) F μ) (_hνic : IsIdeleClassChar (𝓞 F) F ν)
      (φ : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
      (_hφ : ∀ s, IsInducedSection (𝓞 F) F (etaFst μ α hα s) (etaSnd ν α hα s) (φ s))
      (_hφK : ∀ s, IsArchKFinite F (φ s))
      (_hφf : ∀ s, IsKfSmooth F (φ s))
      (_hφjc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 F) F => φ p.1 p.2))
      (_hφhol : ∀ g, Differentiable ℂ (fun s => φ s g)),
    letI := adeleBorel (𝓞 F) F
    (∀ g : AdelicGL2 (𝓞 F) F, AnalyticOnNhd ℂ
        (fun s => weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (φ s) g)
        {s : ℂ | 1 / 2 < s.re}) ∧
    ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 F) F =>
        weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (φ p.1) p.2)
      ({s : ℂ | 1 / 2 < s.re} ×ˢ Set.univ) := by
  intro α hα μ ν hμ hν hμic hνic φ hφ hφK hφf hφjc hφhol
  letI : MeasurableSpace (AdeleRing (𝓞 F) F) := adeleBorel (𝓞 F) F
  have hαdef : α = ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
      (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits := rfl
  have hO : IsOpen {s : ℂ | 1 / 2 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hopen : IsOpen ({s : ℂ | 1 / 2 < s.re} ×ˢ (Set.univ : Set (AdelicGL2 (𝓞 F) F))) :=
    hO.prod isOpen_univ

  have hH : ∀ p : ℝ, 1 < p → Integrable (fun x : AdeleRing (𝓞 F) F =>
      adelicHeight F ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 x) ^ p) (adelicAddHaar (𝓞 F) F) := by
    intro p hp
    have h1 : IsUnitaryChar (𝓞 F) F (1 : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) := fun x => by simp
    have hsph := AutomorphicForm.isInducedSection_indicator_bottomRow_mul_adelicHeight_cpow F hα
      ((p - 1 / 2 : ℝ) : ℂ) ∅ (fun _ => 1) (by simp)
    obtain ⟨hφ₀, hφ₀c, -⟩ := hsph
    have hσ : (1 : ℝ) / 2 < (((p - 1 / 2 : ℝ) : ℂ)).re := by
      rw [Complex.ofReal_re]; linarith
    have hint := AutomorphicForm.weylIntertwiningIntegrand_integrable_of_re_gt_half F hα 1 1 h1 h1 _ hσ _
      hφ₀ hφ₀c 1
    refine hint.norm.congr (ae_of_all _ fun x => ?_)
    simp only [Finset.notMem_empty, IsEmpty.forall_iff, implies_true, if_true, mul_one]
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (adelicHeight_pos _)]
    congr 1
    simp

  have hjc : ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 F) F =>
      weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (φ p.1) p.2)
      ({s : ℂ | 1 / 2 < s.re} ×ˢ Set.univ) := by
    haveI := AutomorphicForm.HolM.firstCountableTopology_adelicGL2 F
    refine hopen.continuousOn_iff.2 ?_
    rintro ⟨s₀, g₀⟩ ⟨hs₀, -⟩
    have hs₀' : 1 / 2 < s₀.re := hs₀
    set δ : ℝ := (s₀.re - 1 / 2) / 2 with hδ
    have hδ0 : 0 < δ := by rw [hδ]; linarith
    set p₁ : ℝ := s₀.re - δ + 1 / 2 with hp₁
    set p₂ : ℝ := s₀.re + δ + 1 / 2 with hp₂
    have hp₁1 : 1 < p₁ := by rw [hp₁, hδ]; linarith
    have hp₂1 : 1 < p₂ := by rw [hp₂, hδ]; linarith

    set Sb : Set ℂ := Metric.closedBall s₀ δ with hSb
    have hSbc : IsCompact Sb := isCompact_closedBall _ _
    have hSre : ∀ s ∈ Sb, s₀.re - δ ≤ s.re ∧ s.re ≤ s₀.re + δ := by
      intro s hs
      have h := Metric.mem_closedBall.1 hs
      rw [Complex.dist_eq] at h
      have habs : |s.re - s₀.re| ≤ δ := by
        rw [← Complex.sub_re]; exact (Complex.abs_re_le_norm (s - s₀)).trans h
      constructor
      · linarith [(abs_le.1 habs).1]
      · linarith [(abs_le.1 habs).2]
    obtain ⟨C, hC0, hC⟩ := AutomorphicForm.HolM.family_bound F α hαdef hα μ ν hμ hν φ hφ hφjc Sb hSbc

    obtain ⟨Cg, hCgc, hCg₀⟩ := exists_compact_mem_nhds g₀
    obtain ⟨κ, K, hκ, hK⟩ :=
      NumberField.AdelicHeight.exists_forall_mul_adelicHeight_le_adelicHeight_mul_of_isCompact F Cg hCgc
    have hK0 : 0 ≤ K := by
      have h := (hK 1 g₀ (mem_of_mem_nhds hCg₀)).2
      rw [one_mul] at h
      have := adelicHeight_pos (F := F) g₀
      have h1' := adelicHeight_pos (F := F) (1 : AdelicGL2 (𝓞 F) F)
      nlinarith
    show ContinuousAt (fun p : ℂ × AdelicGL2 (𝓞 F) F =>
      ∫ x, φ p.1 ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 x * p.2) ∂(adelicAddHaar (𝓞 F) F)) (s₀, g₀)
    refine MeasureTheory.continuousAt_of_dominated
      (bound := fun x => C * (K ^ p₁ * adelicHeight F ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 x) ^ p₁ +
        K ^ p₂ * adelicHeight F ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 x) ^ p₂)) ?_ ?_ ?_ ?_
    · filter_upwards [hopen.mem_nhds (show ((s₀, g₀) : ℂ × AdelicGL2 (𝓞 F) F) ∈
          {s : ℂ | 1 / 2 < s.re} ×ˢ (Set.univ : Set (AdelicGL2 (𝓞 F) F)) from ⟨hs₀', Set.mem_univ _⟩)] with p hp
      have hc : Continuous (φ p.1) := hφjc.comp (continuous_const.prodMk continuous_id)
      exact (AutomorphicForm.weylIntertwiningIntegrand_integrable_of_re_gt_half F hα μ ν hμ hν p.1 hp.1 (φ p.1)
        (hφ p.1) hc p.2).aestronglyMeasurable
    · have hnb : Sb ×ˢ Cg ∈ nhds ((s₀, g₀) : ℂ × AdelicGL2 (𝓞 F) F) :=
        prod_mem_nhds (Metric.closedBall_mem_nhds s₀ hδ0) hCg₀
      filter_upwards [hnb] with p hp
      refine ae_of_all _ fun x => ?_
      obtain ⟨hps, hpg⟩ := hp
      set y : AdelicGL2 (𝓞 F) F := (adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 x with hy
      have hle := (hK y p.2 hpg).2
      have hHy := (adelicHeight_pos (F := F) y).le
      have hq₁ : p₁ ≤ p.1.re + 1 / 2 := by rw [hp₁]; linarith [(hSre p.1 hps).1]
      have hq₂ : p.1.re + 1 / 2 ≤ p₂ := by rw [hp₂]; linarith [(hSre p.1 hps).2]
      have hq0 : 0 ≤ p.1.re + 1 / 2 := by linarith
      calc ‖φ p.1 (y * p.2)‖ ≤ C * adelicHeight F (y * p.2) ^ (p.1.re + 1 / 2) := hC p.1 hps _
        _ ≤ C * (K * adelicHeight F y) ^ (p.1.re + 1 / 2) :=
            mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (adelicHeight_pos _).le hle hq0) hC0
        _ ≤ C * ((K * adelicHeight F y) ^ p₁ + (K * adelicHeight F y) ^ p₂) :=
            mul_le_mul_of_nonneg_left (AutomorphicForm.HolM.rpow_le_rpow_add_rpow (mul_nonneg hK0 hHy)
              (by linarith) hq₁ hq₂) hC0
        _ = C * (K ^ p₁ * adelicHeight F y ^ p₁ + K ^ p₂ * adelicHeight F y ^ p₂) := by
            rw [Real.mul_rpow hK0 hHy, Real.mul_rpow hK0 hHy]
    · exact (((hH p₁ hp₁1).const_mul _).add ((hH p₂ hp₂1).const_mul _)).const_mul _
    · exact ae_of_all _ fun x =>
        (hφjc.comp (continuous_fst.prodMk (continuous_const.mul continuous_snd))).continuousAt
  refine ⟨fun g => ?_, hjc⟩

  intro x hx
  obtain ⟨M', hM', heq⟩ :=
    AutomorphicForm.weylIntertwiningIntegral_meromorphicOn_of_isInducedSection_family F hα μ ν hμ hν hμic hνic
      φ hφ hφK hφf hφjc hφhol g
  have hev : (fun s => weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (φ s) g) =ᶠ[nhds x] M' := by
    filter_upwards [hO.mem_nhds hx] with s hs
    exact (heq s hs).symm
  have hmer : MeromorphicAt (fun s => weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (φ s) g) x :=
    (hM' x (Set.mem_univ x)).congr (hev.symm.filter_mono nhdsWithin_le_nhds)
  have hcont : ContinuousAt (fun s => weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (φ s) g) x := by
    have h2 : ContinuousAt (fun p : ℂ × AdelicGL2 (𝓞 F) F =>
        weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (φ p.1) p.2) (x, g) :=
      (hjc (x, g) ⟨hx, Set.mem_univ _⟩).continuousAt ((hopen).mem_nhds ⟨hx, Set.mem_univ _⟩)
    have h3 : Continuous (fun s : ℂ => ((s, g) : ℂ × AdelicGL2 (𝓞 F) F)) := continuous_id.prodMk continuous_const
    exact ContinuousAt.comp (f := fun s : ℂ => ((s, g) : ℂ × AdelicGL2 (𝓞 F) F)) h2 h3.continuousAt
  exact hmer.analyticAt hcont

end S_AutomorphicForm_analyticOnNhd_and_continuousOn_weylIntertwiningIntegral_family_of_re_gt_half
end P2MW
export P2MW.S_AutomorphicForm_analyticOnNhd_and_continuousOn_weylIntertwiningIntegral_family_of_re_gt_half (solution)
