-- Prove2me | solution 1 for AutomorphicForm.RankinSelberg.lintegral_torus_pair_lt_top_of_ball_surgery
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/8cce7f54-3cbe-5019-8a0d-d69c53b01989

import Definitions.Def_AutomorphicForm_RankinSelbergQuotientIntegral
import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_RowIsometryInvariance
import Definitions.Def_AutomorphicForm_ArchDerivCasimir
import Definitions.Def_NumberField_AdelicTraceFin
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Mathlib.MeasureTheory.Measure.Haar.DistribChar
import Mathlib
import Theorems.Thm_AutomorphicForm_RankinSelberg_whittakerCoefficient_mul_conj_mul_section_diagOne_mul_eq_of_ball_surgery
import Theorems.Thm_NumberField_Idele_integrable_sPartMeasure_empty_of_norm_le_ideleNorm_rpow_mul_prod_min_one_rpow_of_norm_le_rpow_neg
import Theorems.Thm_NumberField_Idele_lintegral_mul_prod_ord_sPartMeasure_eq_lintegral_sPartMeasure_empty_mul_prod_tsum
import Theorems.Thm_NumberField_TateGlobal_ideleNorm_eq_prod_norm_infinitePlace_pow_mult_of_snd_eq_one
import Theorems.Thm_NumberField_TateGlobal_ideleNorm_eq_one_of_fst_eq_one_of_finitePartUnits_mem_unitIdeles
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_RankinSelberg_lintegral_torus_pair_lt_top_of_ball_surgery
p2m_attr_erase "instance" "instCountableOfNumberField_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open NumberField.TateGlobal AutomorphicForm AutomorphicForm.WindowedSiegel IsDedekindDomain
open scoped ENNReal NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel

noncomputable section

namespace RS40P5

open NumberField.Idele NumberField.AdeleRing Set Filter Topology

variable (K : Type) [Field K] [NumberField K]

theorem snd_mul (a b : (AdeleRing (𝓞 K) K)ˣ) (v : HeightOneSpectrum (𝓞 K)) :
    (((a * b : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).2 v = ((a : AdeleRing (𝓞 K) K)).2 v * ((b : AdeleRing (𝓞 K) K)).2 v :=
  rfl

theorem fst_mul (a b : (AdeleRing (𝓞 K) K)ˣ) :
    (((a * b : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).1 = ((a : AdeleRing (𝓞 K) K)).1 * ((b : AdeleRing (𝓞 K) K)).1 :=
  rfl

theorem snd_inv (a : (AdeleRing (𝓞 K) K)ˣ) (v : HeightOneSpectrum (𝓞 K)) :
    (((a⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).2 v = (((a : AdeleRing (𝓞 K) K)).2 v)⁻¹ := by
  have h : ((a : AdeleRing (𝓞 K) K)).2 v * (((a⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).2 v = 1 := by
    have : (((a * a⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).2 v = 1 := by rw [mul_inv_cancel]; rfl
    exact this
  exact eq_inv_of_mul_eq_one_right h

theorem fst_inv_mul_self (a : (AdeleRing (𝓞 K) K)ˣ) :
    (((a⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).1 * ((a : AdeleRing (𝓞 K) K)).1 = 1 := by
  have : (((a⁻¹ * a : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).1 = 1 := by rw [inv_mul_cancel]; rfl
  exact this

theorem fst_inv_eq_one_of_fst_eq_one {a : (AdeleRing (𝓞 K) K)ˣ} (ha : ((a : AdeleRing (𝓞 K) K)).1 = 1) :
    (((a⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).1 = 1 := by
  have h := fst_inv_mul_self K a
  rwa [ha, mul_one] at h

theorem snd_ne_zero (a : (AdeleRing (𝓞 K) K)ˣ) (v : HeightOneSpectrum (𝓞 K)) : ((a : AdeleRing (𝓞 K) K)).2 v ≠ 0 := by
  intro h
  have h1 : (((a * a⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).2 v = 1 := by rw [mul_inv_cancel]; rfl
  rw [snd_mul, h, zero_mul] at h1
  exact zero_ne_one h1

theorem norm_nu_eq_one (ωx ωy ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (w : ℝ)
    (hωx : ∀ z : (AdeleRing (𝓞 K) K)ˣ, ‖((ωx z : ℂˣ) : ℂ)‖ = NumberField.TateGlobal.ideleNorm K z ^ w)
    (hωy : ∀ z : (AdeleRing (𝓞 K) K)ˣ, ‖((ωy z : ℂˣ) : ℂ)‖ = NumberField.TateGlobal.ideleNorm K z ^ w)
    (hων : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      ((ωx z : ℂˣ) : ℂ) * (starRingEnd ℂ) ((ωy z : ℂˣ) : ℂ) * ((ν z : ℂˣ) : ℂ) =
        ((NumberField.TateGlobal.ideleNorm K z ^ (2 * w) : ℝ) : ℂ))
    (z : (AdeleRing (𝓞 K) K)ˣ) : ‖((ν z : ℂˣ) : ℂ)‖ = 1 := by
  have hN := NumberField.TateGlobal.ideleNorm_pos (F := K) z
  have h := congrArg (fun x : ℂ => ‖x‖) (hων z)
  simp only [norm_mul, Complex.norm_conj, hωx, hωy, Complex.norm_real, Real.norm_eq_abs] at h
  rw [abs_of_pos (Real.rpow_pos_of_pos hN _), show (2 * w) = w + w by ring, Real.rpow_add hN] at h
  have hpos : 0 < NumberField.TateGlobal.ideleNorm K z ^ w * NumberField.TateGlobal.ideleNorm K z ^ w :=
    mul_pos (Real.rpow_pos_of_pos hN _) (Real.rpow_pos_of_pos hN _)
  have : NumberField.TateGlobal.ideleNorm K z ^ w * NumberField.TateGlobal.ideleNorm K z ^ w * ‖((ν z : ℂˣ) : ℂ)‖ =
      NumberField.TateGlobal.ideleNorm K z ^ w * NumberField.TateGlobal.ideleNorm K z ^ w * 1 := by rw [h, mul_one]
  exact mul_left_cancel₀ hpos.ne' this

theorem norm_prod_localChar_eq_one (ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hν : ∀ z, ‖((ν z : ℂˣ) : ℂ)‖ = 1)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (d : (v : HeightOneSpectrum (𝓞 K)) → (v.adicCompletion K)ˣ) :
    ‖(∏ v ∈ S, ((localChar ν v (d v) : ℂˣ) : ℂ))‖ = 1 := by
  rw [norm_prod]
  exact Finset.prod_eq_one fun v _ => by rw [NumberField.TateGlobal.localChar_apply]; exact hν _

theorem snd_apply_one_one_ne_zero (S : Finset (HeightOneSpectrum (𝓞 K))) (e : WithZero (Multiplicative ℤ))
    (k : AdelicGL2 (𝓞 K) K) (hk : k ∈ adelicMaximalCompact K) {v : HeightOneSpectrum (𝓞 K)}
    (hsupp : Valued.v (((k : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 0).2 v) ≤
        Valued.v (((k : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 1).2 v) * e) :
    (((k : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 1).2 v) ≠ 0 := by
  intro h0
  have h10 : (((k : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 0).2 v) = 0 := by
    rw [h0, map_zero, zero_mul] at hsupp
    exact (Valuation.zero_iff _).1 (le_antisymm hsupp zero_le')

  set M : GL (Fin 2) (v.adicCompletion K) := finComponent (𝓞 K) K v (glFin (𝓞 K) K k) with hM
  have hdet : (M : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).1 M.isUnit).ne_zero
  have hM10 : (M : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 0 = 0 := by
    rw [hM, finComponent_apply, glFin_apply]; exact h10
  have hM11 : (M : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 1 = 0 := by
    rw [hM, finComponent_apply, glFin_apply]; exact h0
  rw [Matrix.det_fin_two, hM10, hM11, mul_zero, mul_zero, sub_zero] at hdet
  exact hdet rfl

theorem norm_finf_eq_norm_section
    (S : Finset (HeightOneSpectrum (𝓞 K))) (n : ℕ)
    (ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hν : ∀ z, ‖((ν z : ℂˣ) : ℂ)‖ = 1)
    (finf : AdelicGL2 (𝓞 K) K → ℂ) (φ : ℂ → AdelicGL2 (𝓞 K) K → ℂ)
    (hφval : ∀ (s : ℂ) (k kinf : AdelicGL2 (𝓞 K) K) (d : (v : HeightOneSpectrum (𝓞 K)) → (v.adicCompletion K)ˣ),
        glFin (𝓞 K) K k ∈ finiteIntegralGL2 (𝓞 K) K →
        (∀ pl : InfinitePlace K, IsRowIsometry (archComponent K pl (glArch (𝓞 K) K k))) →
        glFin (𝓞 K) K kinf = 1 → glArch (𝓞 K) K kinf = glArch (𝓞 K) K k →
        (∀ v ∈ S, (((k : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 1).2 v) = (d v : v.adicCompletion K)) →
        (∀ v ∈ S, Valued.v (((k : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 0).2 v) ≤
            Valued.v (((k : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 1).2 v) *
              ((Multiplicative.ofAdd (-(n : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) →
          φ s k = (∏ v ∈ S, ((localChar ν v (d v) : ℂˣ) : ℂ)) * finf kinf)
    (s : ℂ) (k : AdelicGL2 (𝓞 K) K) (hk : k ∈ adelicMaximalCompact K)
    (hsupp : ∀ v ∈ S, Valued.v (((k : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 0).2 v) ≤
        Valued.v (((k : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 1).2 v) *
          ((Multiplicative.ofAdd (-(n : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) :
    ‖finf (adelicArchGLIncl K (glArch (𝓞 K) K k))‖ = ‖φ s k‖ := by
  classical
  obtain ⟨hfin, harch⟩ := (mem_adelicMaximalCompact_iff (K := K)).1 hk
  set d : (v : HeightOneSpectrum (𝓞 K)) → (v.adicCompletion K)ˣ := fun v =>
    if h : (((k : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 1).2 v) ≠ 0 then Units.mk0 _ h else 1 with hd
  have hval := hφval s k (adelicArchGLIncl K (glArch (𝓞 K) K k)) d hfin harch (glFin_adelicArchGLIncl K _)
    (glArch_adelicArchGLIncl K _) (fun v hv => ?_) hsupp
  · rw [hval, norm_mul, norm_prod_localChar_eq_one K ν hν, one_mul]
  · have hne := snd_apply_one_one_ne_zero K S _ k hk (hsupp v hv)
    simp only [hd, dif_pos hne, Units.val_mk0]

theorem exists_bound_on_maximalCompact (f : AdelicGL2 (𝓞 K) K → ℂ) (hf : Continuous f) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ k ∈ adelicMaximalCompact K, ‖f k‖ ≤ B := by
  obtain ⟨C, hC⟩ := (isCompact_adelicMaximalCompact K).exists_bound_of_continuousOn hf.continuousOn
  exact ⟨max C 0, le_max_right _ _, fun k hk => (hC k hk).trans (le_max_left _ _)⟩

theorem valued_eq_of_ball (S : Finset (HeightOneSpectrum (𝓞 K))) (t₀ ρ t : (AdeleRing (𝓞 K) K)ˣ) (nb : ℕ) (hnb : 0 < nb)
    (hρ : ∀ v ∈ S, Valued.v (((ρ : AdeleRing (𝓞 K) K)).2 v) = 1)
    (hball : ∀ v ∈ S, Valued.v ((((t * ρ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).2 v - ((t₀ : AdeleRing (𝓞 K) K)).2 v) ≤
        Valued.v (((t₀ : AdeleRing (𝓞 K) K)).2 v) * ((Multiplicative.ofAdd (-(nb : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) :
    ∀ v ∈ S, Valued.v (((t : AdeleRing (𝓞 K) K)).2 v) = Valued.v (((t₀ : AdeleRing (𝓞 K) K)).2 v) := by
  intro v hv
  have h0 : Valued.v (((t₀ : AdeleRing (𝓞 K) K)).2 v) ≠ 0 := fun h => snd_ne_zero K t₀ v ((Valuation.zero_iff _).1 h)
  have he1 : ((Multiplicative.ofAdd (-(nb : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) < 1 := by
    rw [← WithZero.coe_one, WithZero.coe_lt_coe, ← ofAdd_zero, Multiplicative.ofAdd_lt]; omega
  have hlt : Valued.v ((((t * ρ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).2 v - ((t₀ : AdeleRing (𝓞 K) K)).2 v) <
      Valued.v (((t₀ : AdeleRing (𝓞 K) K)).2 v) := by
    refine lt_of_le_of_lt (hball v hv) ?_
    have hcexp : Valued.v (((t₀ : AdeleRing (𝓞 K) K)).2 v) = WithZero.exp (-ord K v t₀) := valued_snd_eq_exp_neg_ord K v t₀
    rw [hcexp, show ((Multiplicative.ofAdd (-(nb : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) = WithZero.exp (-(nb : ℤ)) from rfl,
      ← WithZero.exp_add, WithZero.exp_lt_exp]
    omega
  have h1 := Valuation.map_eq_of_sub_lt Valued.v hlt
  rw [snd_mul, map_mul, hρ v hv, mul_one] at h1
  exact h1

theorem ideleNorm_eq_of_shell (S : Finset (HeightOneSpectrum (𝓞 K))) (t₀ t : (AdeleRing (𝓞 K) K)ˣ)
    (ht₀inf : ((t₀ : AdeleRing (𝓞 K) K)).1 = 1)
    (ht₀ : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → ((t₀ : AdeleRing (𝓞 K) K)).2 v = 1)
    (ht : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → ((t : AdeleRing (𝓞 K) K)).2 v = 1)
    (hshell : ∀ v ∈ S, Valued.v (((t : AdeleRing (𝓞 K) K)).2 v) = Valued.v (((t₀ : AdeleRing (𝓞 K) K)).2 v)) :
    NumberField.TateGlobal.ideleNorm K t = NumberField.TateGlobal.ideleNorm K (partAt K ∅ t) * NumberField.TateGlobal.ideleNorm K t₀ := by

  set u : (AdeleRing (𝓞 K) K)ˣ := (partAt K ∅ t)⁻¹ * t * t₀⁻¹ with hu
  have hu1 : ((u : AdeleRing (𝓞 K) K)).1 = 1 := by
    have hp : (((partAt K ∅ t)⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 * ((t : AdeleRing (𝓞 K) K)).1 = 1 := by
      have h := fst_inv_mul_self K (partAt K ∅ t)
      rwa [partAt_fst] at h
    rw [hu, fst_mul, fst_mul, hp, one_mul, fst_inv_eq_one_of_fst_eq_one K ht₀inf]
  have huv : ∀ v : HeightOneSpectrum (𝓞 K), Valued.v (((u : AdeleRing (𝓞 K) K)).2 v) = 1 := by
    intro v
    rw [hu, snd_mul, snd_mul, snd_inv, snd_inv, partAt_snd_of_not_mem K ∅ t (Finset.notMem_empty v), inv_one, one_mul,
      map_mul, map_inv₀]
    by_cases hv : v ∈ S
    · rw [hshell v hv, mul_inv_cancel₀]
      exact fun h => snd_ne_zero K t₀ v ((Valuation.zero_iff _).1 h)
    · rw [ht v hv, ht₀ v hv, map_one, inv_one, mul_one]
  have hunit : finitePartUnits (𝓞 K) K u ∈ IsDedekindDomain.FiniteAdeleRing.unitIdeles (𝓞 K) K := by
    rw [IsDedekindDomain.FiniteAdeleRing.mem_unitIdeles_iff]
    constructor
    · intro v
      rw [val_finitePartUnits, HeightOneSpectrum.mem_adicCompletionIntegers]
      exact (huv v).le
    · intro v
      rw [← map_inv, val_finitePartUnits, HeightOneSpectrum.mem_adicCompletionIntegers]
      have : Valued.v ((((u⁻¹ : (AdeleRing (𝓞 K) K)ˣ)) : AdeleRing (𝓞 K) K).2 v) = 1 := by
        rw [snd_inv, map_inv₀, huv v, inv_one]
      exact this.le
  have hnu : NumberField.TateGlobal.ideleNorm K u = 1 :=
    NumberField.TateGlobal.ideleNorm_eq_one_of_fst_eq_one_of_finitePartUnits_mem_unitIdeles K u hu1 hunit
  have ht_eq : t = partAt K ∅ t * u * t₀ := by rw [hu]; group
  conv_lhs => rw [ht_eq]
  rw [NumberField.TateGlobal.ideleNorm_mul, NumberField.TateGlobal.ideleNorm_mul, hnu, mul_one]

end RS40P5

namespace RS40P5

open NumberField.Idele NumberField.AdeleRing Set Filter Topology

variable (K : Type) [Field K] [NumberField K]

theorem idele_ext {a b : (AdeleRing (𝓞 K) K)ˣ} (h1 : ((a : AdeleRing (𝓞 K) K)).1 = ((b : AdeleRing (𝓞 K) K)).1)
    (h2 : ∀ v, ((a : AdeleRing (𝓞 K) K)).2 v = ((b : AdeleRing (𝓞 K) K)).2 v) : a = b := by
  apply Units.ext
  exact Prod.ext h1 (RestrictedProduct.ext _ _ fun v => h2 v)

theorem partAt_empty_partAt_empty (a : (AdeleRing (𝓞 K) K)ˣ) : partAt K ∅ (partAt K ∅ a) = partAt K ∅ a := by
  apply idele_ext K
  · rw [partAt_fst, partAt_fst]
  · intro v
    rw [partAt_snd_of_not_mem K ∅ _ (Finset.notMem_empty v), partAt_snd_of_not_mem K ∅ _ (Finset.notMem_empty v)]

theorem partAt_empty_eq_of_fst_eq {a b : (AdeleRing (𝓞 K) K)ˣ}
    (h : ((a : AdeleRing (𝓞 K) K)).1 = ((b : AdeleRing (𝓞 K) K)).1) : partAt K ∅ a = partAt K ∅ b := by
  apply idele_ext K
  · rw [partAt_fst, partAt_fst, h]
  · intro v
    rw [partAt_snd_of_not_mem K ∅ _ (Finset.notMem_empty v), partAt_snd_of_not_mem K ∅ _ (Finset.notMem_empty v)]

theorem partAt_empty_snd (a : (AdeleRing (𝓞 K) K)ˣ) : ((partAt K ∅ a : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 = 1 :=
  RestrictedProduct.ext _ _ fun v => partAt_snd_of_not_mem K ∅ a (Finset.notMem_empty v)

theorem valued_eq_iff_ord_eq (v : HeightOneSpectrum (𝓞 K)) (t t₀ : (AdeleRing (𝓞 K) K)ˣ) :
    Valued.v (((t : AdeleRing (𝓞 K) K)).2 v) = Valued.v (((t₀ : AdeleRing (𝓞 K) K)).2 v) ↔ ord K v t = ord K v t₀ := by
  rw [valued_snd_eq_exp_neg_ord, valued_snd_eq_exp_neg_ord, WithZero.exp_injective.eq_iff, neg_inj]

theorem fst_apply_ne_zero (a : (AdeleRing (𝓞 K) K)ˣ) (pl : InfinitePlace K) : ((a : AdeleRing (𝓞 K) K)).1 pl ≠ 0 := by
  intro h
  have h1 : (((a * a⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).1 pl = 1 := by rw [mul_inv_cancel]; rfl
  have : (((a * a⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).1 pl =
      ((a : AdeleRing (𝓞 K) K)).1 pl * (((a⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).1 pl := rfl
  rw [this, h, zero_mul] at h1
  exact zero_ne_one h1

theorem continuous_fst_apply (pl : InfinitePlace K) :
    Continuous fun a : (AdeleRing (𝓞 K) K)ˣ => ((a : AdeleRing (𝓞 K) K)).1 pl :=
  ((continuous_apply pl).comp continuous_fst).comp Units.continuous_val

theorem continuous_norm_fst_apply (pl : InfinitePlace K) :
    Continuous fun a : (AdeleRing (𝓞 K) K)ˣ => ‖((a : AdeleRing (𝓞 K) K)).1 pl‖ :=
  continuous_norm.comp (continuous_fst_apply K pl)

theorem continuous_snd_apply (v : HeightOneSpectrum (𝓞 K)) :
    Continuous fun t : (AdeleRing (𝓞 K) K)ˣ => ((t : AdeleRing (𝓞 K) K)).2 v :=
  ((RestrictedProduct.continuous_eval v).comp continuous_snd).comp Units.continuous_val

theorem measurable_rpow_norm_fst (pl : InfinitePlace K) (e : ℝ) :
    Measurable fun a : (AdeleRing (𝓞 K) K)ˣ => ‖((a : AdeleRing (𝓞 K) K)).1 pl‖ ^ e :=
  (continuous_norm_fst_apply K pl).measurable.pow_const e

theorem measurable_ideleNorm_rpow (e : ℝ) :
    Measurable fun a : (AdeleRing (𝓞 K) K)ˣ => NumberField.TateGlobal.ideleNorm K a ^ e :=
  (NumberField.TateGlobal.continuous_ideleNorm K).measurable.pow_const e

theorem measurableSet_shell (S : Finset (HeightOneSpectrum (𝓞 K))) (t₀ : (AdeleRing (𝓞 K) K)ˣ) :
    MeasurableSet {t : (AdeleRing (𝓞 K) K)ˣ | ∀ v ∈ S, Valued.v (((t : AdeleRing (𝓞 K) K)).2 v) = Valued.v (((t₀ : AdeleRing (𝓞 K) K)).2 v)} := by
  have hrepr : {t : (AdeleRing (𝓞 K) K)ˣ | ∀ v ∈ S, Valued.v (((t : AdeleRing (𝓞 K) K)).2 v) = Valued.v (((t₀ : AdeleRing (𝓞 K) K)).2 v)} =
      ⋂ v ∈ S, (fun t : (AdeleRing (𝓞 K) K)ˣ => ((t : AdeleRing (𝓞 K) K)).2 v) ⁻¹'
        {u | Valued.v u = Valued.v (((t₀ : AdeleRing (𝓞 K) K)).2 v)} := by
    ext t; simp only [mem_setOf_eq, mem_iInter, mem_preimage]
  rw [hrepr]
  refine MeasurableSet.biInter (S.countable_toSet) fun v _ => ?_

  obtain ⟨ϖ, hϖ0, hϖ⟩ := exists_valued_eq_exp_neg (K := K) v 1
  set c : v.adicCompletion K := ((t₀ : AdeleRing (𝓞 K) K)).2 v with hc
  have hc0 : c ≠ 0 := snd_ne_zero K t₀ v
  have hsph : {u : v.adicCompletion K | Valued.v u = Valued.v c} =
      {u | Valued.v u ≤ Valued.v c} \ {u | Valued.v u ≤ Valued.v (c * ϖ)} := by
    ext u
    simp only [mem_setOf_eq, mem_diff, not_le, map_mul, hϖ]
    have hcexp : Valued.v c = WithZero.exp (-ord K v t₀) := valued_snd_eq_exp_neg_ord K v t₀
    constructor
    · intro h
      refine ⟨h.le, ?_⟩
      rw [h, hcexp, ← WithZero.exp_add, WithZero.exp_lt_exp]; omega
    · rintro ⟨h1, h2⟩
      refine le_antisymm h1 ?_

      rcases eq_or_ne (Valued.v u) 0 with hu0 | hu0
      · rw [hu0] at h2; exact absurd h2 (not_lt.2 zero_le')
      · obtain ⟨k, hk⟩ : ∃ k : ℤ, Valued.v u = WithZero.exp k := ⟨_, (WithZero.coe_unzero hu0).symm⟩
        rw [hk, hcexp] at h1 h2 ⊢
        rw [← WithZero.exp_add, WithZero.exp_lt_exp] at h2
        rw [WithZero.exp_le_exp] at h1 ⊢
        omega
  rw [hsph, Set.preimage_diff]
  exact ((isOpen_setOf_valued_le v c hc0).preimage (continuous_snd_apply K v)).measurableSet.diff
    ((isOpen_setOf_valued_le v (c * ϖ) (mul_ne_zero hc0 hϖ0)).preimage (continuous_snd_apply K v)).measurableSet

end RS40P5

open RS40P5 NumberField.Idele MeasureTheory Set in
theorem solution
    (K : Type) [Field K] [NumberField K] :
    let α : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits
    ∀ (hα : ∀ t, 0 < ((α t : ℝˣ) : ℝ))
      (S : Finset (HeightOneSpectrum (𝓞 K)))
      (D₀ : Set (AdelicGL2 (𝓞 K) K))

      (ωx ωy : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (w : ℝ)
      (_hωx : ∀ z : (AdeleRing (𝓞 K) K)ˣ, ‖((ωx z : ℂˣ) : ℂ)‖ = NumberField.TateGlobal.ideleNorm K z ^ w)
      (_hωy : ∀ z : (AdeleRing (𝓞 K) K)ˣ, ‖((ωy z : ℂˣ) : ℂ)‖ = NumberField.TateGlobal.ideleNorm K z ^ w)
      (ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
      (_hων : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
        ((ωx z : ℂˣ) : ℂ) * (starRingEnd ℂ) ((ωy z : ℂˣ) : ℂ) * ((ν z : ℂˣ) : ℂ) =
          ((NumberField.TateGlobal.ideleNorm K z ^ (2 * w) : ℝ) : ℂ))

      (x₀ : AdelicGL2 (𝓞 K) K → ℂ)
      (nb : ℕ) (_hnb : 0 < nb)
      (_hx₀cong : ∀ (g k : AdelicGL2 (𝓞 K) K), k ∈ finiteAdelicGL2Subgroup K →
        glFin (𝓞 K) K k ∈ finiteIntegralGL2 (𝓞 K) K →
        (∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → finComponent (𝓞 K) K v (glFin (𝓞 K) K k) = 1) →
        (∀ v ∈ S, ∀ i j : Fin 2,
          Valued.v ((((k : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j -
              (1 : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j)).2 v) ≤
            ((Multiplicative.ofAdd (-(nb : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) →
        x₀ (g * k) = x₀ g)
      (_hxlarge : ∀ g : AdelicGL2 (𝓞 K) K, glArch (𝓞 K) K g = 1 → ∀ M : ℕ,
        ∃ Cg : ℝ, ∀ k : AdelicGL2 (𝓞 K) K, glFin (𝓞 K) K k = 1 →
          (∀ pl : InfinitePlace K, IsRowIsometry (archComponent K pl (glArch (𝓞 K) K k))) →
          ∀ a : (AdeleRing (𝓞 K) K)ˣ, ((a : AdeleRing (𝓞 K) K)).2 = 1 → ∀ pl : InfinitePlace K,
            ‖whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x₀ 1
          (diagOne a * k * g)‖ ≤
              Cg * NumberField.TateGlobal.ideleNorm K a ^ (w / 2) * ‖((a : AdeleRing (𝓞 K) K)).1 pl‖ ^ (-(M : ℝ)))

      (t₀ : (AdeleRing (𝓞 K) K)ˣ) (_ht₀inf : ((t₀ : AdeleRing (𝓞 K) K)).1 = 1)
      (_ht₀ : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → ((t₀ : AdeleRing (𝓞 K) K)).2 v = 1)
      (m : ℕ)
      (_ht₀box : ∀ v ∈ S, Valued.v (((t₀ : AdeleRing (𝓞 K) K)).2 v) ≤
        ((Multiplicative.ofAdd (m : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)))
      (k₀ : AdelicGL2 (𝓞 K) K) (_hk₀ : k₀ ∈ maximalCompactAt K S)
      (κ : AdelicGL2 (𝓞 K) K) (_hκ : κ = AdelicDock.finEmbed (𝓞 K) K (glFin (𝓞 K) K k₀))

      (r : ℕ) (u : Fin r → AdeleRing (𝓞 K) K) (cs : Fin r → ℂ)
      (_husupp : ∀ i, (u i).1 = 0 ∧ ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → (u i).2 v = 0)
      (_hWmult : ∀ (t : (AdeleRing (𝓞 K) K)ˣ) (g' : AdelicGL2 (𝓞 K) K),
        (∀ i, g' * unipotentGL2 (u i) = unipotentGL2 (u i) * g') →
        whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) (fun g => ∑ i, cs i * x₀ (g * unipotentGL2 (u i) * κ)) 1
          (diagOne t * g') =
          (∑ i, cs i * NumberField.StandardAddChar.stdAddChar K ((t : AdeleRing (𝓞 K) K) * u i)) *
            whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) (fun g => x₀ (g * κ)) 1
          (diagOne t * g'))
      (_hμball : ∀ t : (AdeleRing (𝓞 K) K)ˣ,
        (∀ v ∈ S, Valued.v (((t : AdeleRing (𝓞 K) K)).2 v) ≤
            ((Multiplicative.ofAdd (m : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) →
        (∑ i, cs i * NumberField.StandardAddChar.stdAddChar K ((t : AdeleRing (𝓞 K) K) * u i)) =
          if ∀ v ∈ S, Valued.v (((t : AdeleRing (𝓞 K) K)).2 v - ((t₀ : AdeleRing (𝓞 K) K)).2 v) ≤
              Valued.v (((t₀ : AdeleRing (𝓞 K) K)).2 v) *
                ((Multiplicative.ofAdd (-(nb : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) then 1 else 0)
      (_hboxvan : ∀ k : AdelicGL2 (𝓞 K) K, glFin (𝓞 K) K k = 1 →
        (∀ pl : InfinitePlace K, IsRowIsometry (archComponent K pl (glArch (𝓞 K) K k))) →
        ∀ t : (AdeleRing (𝓞 K) K)ˣ,
          (∃ v ∈ S, ((Multiplicative.ofAdd (m : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) <
            Valued.v (((t : AdeleRing (𝓞 K) K)).2 v)) →
          whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x₀ 1
          (diagOne t * k * κ) = 0)

      (x : AdelicGL2 (𝓞 K) K → ℂ) (_hxsum : ∀ g, x g = ∑ i, cs i * x₀ (g * (unipotentGL2 (u i) * κ)))
      (_hxG : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) K) (g : AdelicGL2 (𝓞 K) K), x (globalPoints (𝓞 K) K γ * g) = x g)
      (_hxZ : ∀ (z : (AdeleRing (𝓞 K) K)ˣ) (g : AdelicGL2 (𝓞 K) K), x (centralScalar (𝓞 K) K z * g) = ((ωx z : ℂˣ) : ℂ) * x g)
      (_hxKS : ∀ k ∈ maximalCompactAway K S, ∀ g : AdelicGL2 (𝓞 K) K, x (g * k) = x g)
      (n : ℕ) (_hn : 0 < n)
      (_hxlow : ∀ (γ : AdeleRing (𝓞 K) K) (g : AdelicGL2 (𝓞 K) K), γ.1 = 0 →
        (∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → γ.2 v = 0) →
        (∀ v ∈ S, Valued.v (γ.2 v) ≤
          ((Multiplicative.ofAdd (-(n : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) →
        x (g * lowerUnipotentGL2 γ) = x g)

      (y : AdelicGL2 (𝓞 K) K → ℂ)
      (_hyG : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) K) (g : AdelicGL2 (𝓞 K) K), y (globalPoints (𝓞 K) K γ * g) = y g)
      (_hyZ : ∀ (z : (AdeleRing (𝓞 K) K)ˣ) (g : AdelicGL2 (𝓞 K) K), y (centralScalar (𝓞 K) K z * g) = ((ωy z : ℂˣ) : ℂ) * y g)
      (_hyKS : ∀ k ∈ maximalCompactAway K S, ∀ g : AdelicGL2 (𝓞 K) K, y (g * k) = y g)
      (_hycong : ∀ (g k : AdelicGL2 (𝓞 K) K), k ∈ finiteAdelicGL2Subgroup K →
        glFin (𝓞 K) K k ∈ finiteIntegralGL2 (𝓞 K) K →
        (∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → finComponent (𝓞 K) K v (glFin (𝓞 K) K k) = 1) →
        (∀ v ∈ S, ∀ i j : Fin 2,
          Valued.v ((((k : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j -
              (1 : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j)).2 v) ≤
            ((Multiplicative.ofAdd (-(nb : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) →
        y (g * k) = y g)
      (_hylow : ∀ (γ : AdeleRing (𝓞 K) K) (g : AdelicGL2 (𝓞 K) K), γ.1 = 0 →
        (∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → γ.2 v = 0) →
        (∀ v ∈ S, Valued.v (γ.2 v) ≤
          ((Multiplicative.ofAdd (-(n : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) →
        y (g * lowerUnipotentGL2 γ) = y g)
      (_hylarge : ∀ g : AdelicGL2 (𝓞 K) K, glArch (𝓞 K) K g = 1 → ∀ M : ℕ,
        ∃ Cg : ℝ, ∀ k : AdelicGL2 (𝓞 K) K, glFin (𝓞 K) K k = 1 →
          (∀ pl : InfinitePlace K, IsRowIsometry (archComponent K pl (glArch (𝓞 K) K k))) →
          ∀ a : (AdeleRing (𝓞 K) K)ˣ, ((a : AdeleRing (𝓞 K) K)).2 = 1 → ∀ pl : InfinitePlace K,
            ‖whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) y 1
          (diagOne a * k * g)‖ ≤
              Cg * NumberField.TateGlobal.ideleNorm K a ^ (w / 2) * ‖((a : AdeleRing (𝓞 K) K)).1 pl‖ ^ (-(M : ℝ)))

      (finf : AdelicGL2 (𝓞 K) K → ℂ)
      (φ : ℂ → AdelicGL2 (𝓞 K) K → ℂ)
      (_hφ : ∀ s, IsInducedSection (𝓞 K) K (etaFst 1 α hα s) (etaSnd ν α hα s) (φ s))
      (_hφjc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 K) K => φ p.1 p.2))
      (_hφKS : ∀ s, ∀ k ∈ maximalCompactAway K S, ∀ g : AdelicGL2 (𝓞 K) K, φ s (g * k) = φ s g)
      (_hφsupp : ∀ (s : ℂ) (k : AdelicGL2 (𝓞 K) K),
        glFin (𝓞 K) K k ∈ finiteIntegralGL2 (𝓞 K) K →
        (∀ pl : InfinitePlace K, IsRowIsometry (archComponent K pl (glArch (𝓞 K) K k))) →
        (∃ v ∈ S, ¬ Valued.v (((k : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 0).2 v) ≤
            Valued.v (((k : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 1).2 v) *
              ((Multiplicative.ofAdd (-(n : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) →
          φ s k = 0)
      (_hφval : ∀ (s : ℂ) (k kinf : AdelicGL2 (𝓞 K) K) (d : (v : HeightOneSpectrum (𝓞 K)) → (v.adicCompletion K)ˣ),
        glFin (𝓞 K) K k ∈ finiteIntegralGL2 (𝓞 K) K →
        (∀ pl : InfinitePlace K, IsRowIsometry (archComponent K pl (glArch (𝓞 K) K k))) →
        glFin (𝓞 K) K kinf = 1 → glArch (𝓞 K) K kinf = glArch (𝓞 K) K k →
        (∀ v ∈ S, (((k : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 1).2 v) = (d v : v.adicCompletion K)) →
        (∀ v ∈ S, Valued.v (((k : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 0).2 v) ≤
            Valued.v (((k : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 1).2 v) *
              ((Multiplicative.ofAdd (-(n : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) →
          φ s k = (∏ v ∈ S, ((localChar ν v (d v) : ℂˣ) : ℂ)) * finf kinf)

      (δx Cx : ℝ) (_hδx : 0 < δx)
      (_hCx : ∀ k : AdelicGL2 (𝓞 K) K, glFin (𝓞 K) K k = 1 →
        (∀ pl : InfinitePlace K, IsRowIsometry (archComponent K pl (glArch (𝓞 K) K k))) →
        ∀ a : (AdeleRing (𝓞 K) K)ˣ, ((a : AdeleRing (𝓞 K) K)).2 = 1 →
          ‖whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x₀ 1
          (diagOne a * k * (diagOne t₀ * κ))‖ ≤
            Cx * ∏ pl : InfinitePlace K, (‖((a : AdeleRing (𝓞 K) K)).1 pl‖ ^ ((pl.mult : ℝ) * w / 2) *
              (min 1 ‖((a : AdeleRing (𝓞 K) K)).1 pl‖) ^ δx))
      (δy Cy : ℝ) (_hδy : 0 < δy)
      (_hCy : ∀ k : AdelicGL2 (𝓞 K) K, glFin (𝓞 K) K k = 1 →
        (∀ pl : InfinitePlace K, IsRowIsometry (archComponent K pl (glArch (𝓞 K) K k))) →
        ∀ a : (AdeleRing (𝓞 K) K)ˣ, ((a : AdeleRing (𝓞 K) K)).2 = 1 →
          ‖whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) y 1
          (diagOne a * k * (diagOne t₀))‖ ≤
            Cy * ∏ pl : InfinitePlace K, (‖((a : AdeleRing (𝓞 K) K)).1 pl‖ ^ ((pl.mult : ℝ) * w / 2) *
              (min 1 ‖((a : AdeleRing (𝓞 K) K)).1 pl‖) ^ δy)),
    ∀ s : ℂ, 1 / 2 - (δx + δy) / 2 < s.re →
      (∫⁻ t, ∫⁻ k,
        ‖whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x 1
          (diagOne t * (k : AdelicGL2 (𝓞 K) K)) *
            (starRingEnd ℂ) (whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) y 1
          (diagOne t * (k : AdelicGL2 (𝓞 K) K))) *
            φ s (diagOne t * (k : AdelicGL2 (𝓞 K) K))‖ₑ *
          ENNReal.ofReal (NumberField.TateGlobal.ideleNorm K t ^ (-w - 1))
        ∂(maximalCompactHaar K) ∂(NumberField.Idele.sPartMeasure K S)) < ∞ := by
  intro α hα S D₀ ωx ωy w hωx hωy ν hων x₀ nb hnb hx₀cong hxlarge t₀ ht₀inf ht₀ m ht₀box k₀ hk₀ κ hκ r u cs husupp
    hWmult hμball hboxvan x hxsum hxG hxZ hxKS n hn hxlow y hyG hyZ hyKS hycong hylow hylarge finf φ hφ hφjc hφKS
    hφsupp hφval δx Cx hδx hCx δy Cy hδy hCy s hs
  classical

  set pins := productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
    (adelicBox K) with hpins
  set ψ := NumberField.StandardAddChar.stdAddChar K with hψ
  set σ : ℝ := s.re with hσ
  set cc : ℝ := σ - 1 / 2 with hcc
  set e : WithZero (Multiplicative ℤ) := ((Multiplicative.ofAdd (-(n : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) with he
  set eb : WithZero (Multiplicative ℤ) := ((Multiplicative.ofAdd (-(nb : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) with heb
  have hN0 : ∀ a : (AdeleRing (𝓞 K) K)ˣ, 0 < NumberField.TateGlobal.ideleNorm K a := fun a => NumberField.TateGlobal.ideleNorm_pos a

  obtain ⟨Bs, hBs0, hBs⟩ := exists_bound_on_maximalCompact K (φ s) (hφjc.comp (continuous_const.prodMk continuous_id))
  have hν1 : ∀ z, ‖((ν z : ℂˣ) : ℂ)‖ = 1 := norm_nu_eq_one K ωx ωy ν w hωx hωy hων

  have hadm_one : glFin (𝓞 K) K (1 : AdelicGL2 (𝓞 K) K) = 1 ∧
      ∀ pl : InfinitePlace K, IsRowIsometry (archComponent K pl (glArch (𝓞 K) K (1 : AdelicGL2 (𝓞 K) K))) :=
    ⟨map_one _, ((mem_adelicMaximalCompact_iff (K := K)).1 (one_mem _)).2⟩
  have hgx1 : glArch (𝓞 K) K (diagOne t₀ * κ) = 1 := by
    rw [map_mul, hκ, AdelicDock.glArch_finEmbed, mul_one]
    refine Units.ext (Matrix.ext fun i j => ?_)
    rw [glArch_apply, diagOne_coe_apply, Units.val_one]
    fin_cases i <;> fin_cases j <;> (try simp [Matrix.diagonal, ht₀inf]) <;> rfl

  choose CxM hCxM using fun M : ℕ => hxlarge (diagOne t₀ * κ) hgx1 M

  set Px : (AdeleRing (𝓞 K) K)ˣ → ℝ := fun a => ∏ pl : InfinitePlace K, (‖((a : AdeleRing (𝓞 K) K)).1 pl‖ ^ ((pl.mult : ℝ) * w / 2) *
    (min 1 ‖((a : AdeleRing (𝓞 K) K)).1 pl‖) ^ δx) with hPx
  set Py : (AdeleRing (𝓞 K) K)ˣ → ℝ := fun a => ∏ pl : InfinitePlace K, (‖((a : AdeleRing (𝓞 K) K)).1 pl‖ ^ ((pl.mult : ℝ) * w / 2) *
    (min 1 ‖((a : AdeleRing (𝓞 K) K)).1 pl‖) ^ δy) with hPy
  set Lx : ℕ × InfinitePlace K → (AdeleRing (𝓞 K) K)ˣ → ℝ := fun p a =>
    CxM p.1 * NumberField.TateGlobal.ideleNorm K a ^ (w / 2) * ‖((a : AdeleRing (𝓞 K) K)).1 p.2‖ ^ (-(p.1 : ℝ)) with hLx
  set Ex : (AdeleRing (𝓞 K) K)ˣ → ℝ≥0∞ := fun a => ENNReal.ofReal (Cx * Px a) ⊓ ⨅ p : ℕ × InfinitePlace K, ENNReal.ofReal (Lx p a)
    with hEx
  set Ey : (AdeleRing (𝓞 K) K)ˣ → ℝ≥0∞ := fun a => ENNReal.ofReal (Cy * Py a) with hEy

  have hPmeas : ∀ δ : ℝ, Measurable fun a : (AdeleRing (𝓞 K) K)ˣ => ∏ pl : InfinitePlace K,
      (‖((a : AdeleRing (𝓞 K) K)).1 pl‖ ^ ((pl.mult : ℝ) * w / 2) * (min 1 ‖((a : AdeleRing (𝓞 K) K)).1 pl‖) ^ δ) := by
    intro δ
    refine Finset.measurable_prod _ fun pl _ => ?_
    exact (measurable_rpow_norm_fst K pl _).mul ((measurable_const.min (continuous_norm_fst_apply K pl).measurable).pow_const δ)
  have hExm : Measurable Ex := by
    refine (Measurable.ennreal_ofReal (measurable_const.mul (hPmeas δx))).inf (Measurable.iInf fun p => ?_)
    exact Measurable.ennreal_ofReal ((measurable_const.mul (measurable_ideleNorm_rpow K _)).mul (measurable_rpow_norm_fst K _ _))
  have hEym : Measurable Ey := Measurable.ennreal_ofReal (measurable_const.mul (hPmeas δy))

  have hExdom : ∀ kk : AdelicGL2 (𝓞 K) K, glFin (𝓞 K) K kk = 1 →
      (∀ pl : InfinitePlace K, IsRowIsometry (archComponent K pl (glArch (𝓞 K) K kk))) →
      ∀ a : (AdeleRing (𝓞 K) K)ˣ, ((a : AdeleRing (𝓞 K) K)).2 = 1 →
        ‖whittakerCoefficient K pins ψ x₀ 1 (diagOne a * kk * (diagOne t₀ * κ))‖ₑ ≤ Ex a := by
    intro kk hk1 hk2 a ha
    rw [← ofReal_norm_eq_enorm]
    refine le_inf (ENNReal.ofReal_le_ofReal (hCx kk hk1 hk2 a ha)) (le_iInf fun p => ENNReal.ofReal_le_ofReal ?_)
    exact hCxM p.1 kk hk1 hk2 a ha p.2
  have hEydom : ∀ kk : AdelicGL2 (𝓞 K) K, glFin (𝓞 K) K kk = 1 →
      (∀ pl : InfinitePlace K, IsRowIsometry (archComponent K pl (glArch (𝓞 K) K kk))) →
      ∀ a : (AdeleRing (𝓞 K) K)ˣ, ((a : AdeleRing (𝓞 K) K)).2 = 1 →
        ‖whittakerCoefficient K pins ψ y 1 (diagOne a * kk * diagOne t₀)‖ₑ ≤ Ey a := by
    intro kk hk1 hk2 a ha
    rw [← ofReal_norm_eq_enorm]
    exact ENNReal.ofReal_le_ofReal (hCy kk hk1 hk2 a ha)
  have hExfin : ∀ a, Ex a ≠ ⊤ := fun a => ne_top_of_le_ne_top ENNReal.ofReal_ne_top inf_le_left
  have hEyfin : ∀ a, Ey a ≠ ⊤ := fun a => ENNReal.ofReal_ne_top

  have hPpos : ∀ (δ : ℝ) (a : (AdeleRing (𝓞 K) K)ˣ), 0 < ∏ pl : InfinitePlace K,
      (‖((a : AdeleRing (𝓞 K) K)).1 pl‖ ^ ((pl.mult : ℝ) * w / 2) * (min 1 ‖((a : AdeleRing (𝓞 K) K)).1 pl‖) ^ δ) := by
    intro δ a
    refine Finset.prod_pos fun pl _ => mul_pos (Real.rpow_pos_of_pos ?_ _) (Real.rpow_pos_of_pos (lt_min one_pos ?_) _) <;>
      exact norm_pos_iff.2 (fst_apply_ne_zero K a pl)
  have hCx0 : 0 ≤ Cx := by
    have h := hCx 1 hadm_one.1 hadm_one.2 1 rfl
    have hp := hPpos δx 1
    exact nonneg_of_mul_nonneg_left ((norm_nonneg _).trans h) hp
  have hCy0 : 0 ≤ Cy := by
    have h := hCy 1 hadm_one.1 hadm_one.2 1 rfl
    have hp := hPpos δy 1
    exact nonneg_of_mul_nonneg_left ((norm_nonneg _).trans h) hp
  have hLx0 : ∀ (p : ℕ × InfinitePlace K) (a : (AdeleRing (𝓞 K) K)ˣ), ((a : AdeleRing (𝓞 K) K)).2 = 1 → 0 ≤ Lx p a :=
    fun p a ha => (norm_nonneg _).trans (hCxM p.1 1 hadm_one.1 hadm_one.2 a ha p.2)

  set F : (AdeleRing (𝓞 K) K)ˣ → ℝ := fun a => NumberField.TateGlobal.ideleNorm K a ^ (cc - w) * (Ex a).toReal * (Ey a).toReal
    with hF
  have hFm : Measurable F :=
    ((measurable_ideleNorm_rpow K _).mul (ENNReal.measurable_toReal.comp hExm)).mul (ENNReal.measurable_toReal.comp hEym)
  have hF0 : ∀ a, 0 ≤ F a := fun a => mul_nonneg (mul_nonneg (Real.rpow_nonneg (hN0 a).le _) ENNReal.toReal_nonneg) ENNReal.toReal_nonneg
  have hnormF : ∀ a, ‖F a‖ = F a := fun a => Real.norm_of_nonneg (hF0 a)

  have hprodN : ∀ a : (AdeleRing (𝓞 K) K)ˣ, ((a : AdeleRing (𝓞 K) K)).2 = 1 → ∀ ex : ℝ,
      ∏ pl : InfinitePlace K, ‖((a : AdeleRing (𝓞 K) K)).1 pl‖ ^ ((pl.mult : ℝ) * ex) = NumberField.TateGlobal.ideleNorm K a ^ ex := by
    intro a ha ex
    rw [NumberField.TateGlobal.ideleNorm_eq_prod_norm_infinitePlace_pow_mult_of_snd_eq_one K a ha,
      ← Real.finset_prod_rpow _ _ (fun pl _ => pow_nonneg (norm_nonneg _) _)]
    refine Finset.prod_congr rfl fun pl _ => ?_
    rw [Real.rpow_natCast_mul (norm_nonneg _)]
  have hPsplit : ∀ (δ : ℝ) (a : (AdeleRing (𝓞 K) K)ˣ), ((a : AdeleRing (𝓞 K) K)).2 = 1 →
      ∏ pl : InfinitePlace K, (‖((a : AdeleRing (𝓞 K) K)).1 pl‖ ^ ((pl.mult : ℝ) * w / 2) * (min 1 ‖((a : AdeleRing (𝓞 K) K)).1 pl‖) ^ δ) =
        NumberField.TateGlobal.ideleNorm K a ^ (w / 2) * ∏ pl : InfinitePlace K, (min 1 ‖((a : AdeleRing (𝓞 K) K)).1 pl‖) ^ δ := by
    intro δ a ha
    rw [Finset.prod_mul_distrib, ← hprodN a ha (w / 2)]
    congr 1
    exact Finset.prod_congr rfl fun pl _ => by rw [mul_div_assoc]
  have hminle : ∀ (δ : ℝ), 0 ≤ δ → ∀ a : (AdeleRing (𝓞 K) K)ˣ, ∏ pl : InfinitePlace K, (min 1 ‖((a : AdeleRing (𝓞 K) K)).1 pl‖) ^ δ ≤ 1 :=
    fun δ hδ a => Finset.prod_le_one (fun pl _ => Real.rpow_nonneg (le_min zero_le_one (norm_nonneg _)) _)
      fun pl _ => Real.rpow_le_one (le_min zero_le_one (norm_nonneg _)) (min_le_left _ _) hδ

  have hsmall : ∀ a : (AdeleRing (𝓞 K) K)ˣ, ((a : AdeleRing (𝓞 K) K)).2 = 1 →
      ‖F a‖ ≤ (Cx * Cy) * NumberField.TateGlobal.ideleNorm K a ^ cc *
        ∏ pl : InfinitePlace K, (min 1 ‖((a : AdeleRing (𝓞 K) K)).1 pl‖) ^ (δx + δy) := by
    intro a ha
    rw [hnormF]
    have hx : (Ex a).toReal ≤ Cx * Px a :=
      ENNReal.toReal_le_of_le_ofReal (mul_nonneg hCx0 (hPpos δx a).le) inf_le_left
    have hy : (Ey a).toReal ≤ Cy * Py a := ENNReal.toReal_le_of_le_ofReal (mul_nonneg hCy0 (hPpos δy a).le) le_rfl
    have hNp := hN0 a
    calc F a ≤ NumberField.TateGlobal.ideleNorm K a ^ (cc - w) * (Cx * Px a) * (Cy * Py a) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hx (Real.rpow_nonneg hNp.le _)) hy ENNReal.toReal_nonneg
            (mul_nonneg (Real.rpow_nonneg hNp.le _) (mul_nonneg hCx0 (hPpos δx a).le))
      _ = (Cx * Cy) * NumberField.TateGlobal.ideleNorm K a ^ cc *
            ∏ pl : InfinitePlace K, (min 1 ‖((a : AdeleRing (𝓞 K) K)).1 pl‖) ^ (δx + δy) := by
          rw [hPx, hPy]
          simp only []
          rw [hPsplit δx a ha, hPsplit δy a ha]
          have hmin : ∏ pl : InfinitePlace K, (min 1 ‖((a : AdeleRing (𝓞 K) K)).1 pl‖) ^ (δx + δy) =
              (∏ pl : InfinitePlace K, (min 1 ‖((a : AdeleRing (𝓞 K) K)).1 pl‖) ^ δx) *
                ∏ pl : InfinitePlace K, (min 1 ‖((a : AdeleRing (𝓞 K) K)).1 pl‖) ^ δy := by
            rw [← Finset.prod_mul_distrib]
            refine Finset.prod_congr rfl fun pl _ => ?_
            rw [Real.rpow_add (lt_min one_pos (norm_pos_iff.2 (fst_apply_ne_zero K a pl)))]
          rw [hmin]
          have hNN : NumberField.TateGlobal.ideleNorm K a ^ (cc - w) * NumberField.TateGlobal.ideleNorm K a ^ (w / 2) *
              NumberField.TateGlobal.ideleNorm K a ^ (w / 2) = NumberField.TateGlobal.ideleNorm K a ^ cc := by
            rw [← Real.rpow_add hNp, ← Real.rpow_add hNp]; ring_nf
          calc NumberField.TateGlobal.ideleNorm K a ^ (cc - w) *
                (Cx * (NumberField.TateGlobal.ideleNorm K a ^ (w / 2) * ∏ pl, (min 1 ‖((a : AdeleRing (𝓞 K) K)).1 pl‖) ^ δx)) *
                (Cy * (NumberField.TateGlobal.ideleNorm K a ^ (w / 2) * ∏ pl, (min 1 ‖((a : AdeleRing (𝓞 K) K)).1 pl‖) ^ δy))
              = (Cx * Cy) * (NumberField.TateGlobal.ideleNorm K a ^ (cc - w) * NumberField.TateGlobal.ideleNorm K a ^ (w / 2) *
                  NumberField.TateGlobal.ideleNorm K a ^ (w / 2)) *
                  ((∏ pl, (min 1 ‖((a : AdeleRing (𝓞 K) K)).1 pl‖) ^ δx) * ∏ pl, (min 1 ‖((a : AdeleRing (𝓞 K) K)).1 pl‖) ^ δy) := by
                ring
            _ = _ := by rw [hNN]

  have hlarge : ∀ M : ℕ, ∃ B : ℝ, ∀ a : (AdeleRing (𝓞 K) K)ˣ, ((a : AdeleRing (𝓞 K) K)).2 = 1 →
      ∀ pl : InfinitePlace K,
        ‖F a‖ ≤ B * NumberField.TateGlobal.ideleNorm K a ^ cc * ‖((a : AdeleRing (𝓞 K) K)).1 pl‖ ^ (-(M : ℝ)) := by
    intro M
    refine ⟨CxM M * Cy, fun a ha pl => ?_⟩
    rw [hnormF]
    have hNp := hN0 a
    have hx : (Ex a).toReal ≤ Lx (M, pl) a :=
      ENNReal.toReal_le_of_le_ofReal (hLx0 (M, pl) a ha) (inf_le_right.trans (iInf_le _ (M, pl)))
    have hy : (Ey a).toReal ≤ Cy * NumberField.TateGlobal.ideleNorm K a ^ (w / 2) := by
      refine (ENNReal.toReal_le_of_le_ofReal (mul_nonneg hCy0 (hPpos δy a).le) le_rfl).trans ?_
      show Cy * Py a ≤ _
      rw [hPy]; simp only []
      rw [hPsplit δy a ha]
      calc Cy * (NumberField.TateGlobal.ideleNorm K a ^ (w / 2) * ∏ pl, (min 1 ‖((a : AdeleRing (𝓞 K) K)).1 pl‖) ^ δy)
          ≤ Cy * (NumberField.TateGlobal.ideleNorm K a ^ (w / 2) * 1) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hminle δy hδy.le a) (Real.rpow_nonneg hNp.le _)) hCy0
        _ = Cy * NumberField.TateGlobal.ideleNorm K a ^ (w / 2) := by rw [mul_one]
    have hCxM0 : 0 ≤ CxM M := by
      have h := hCxM M 1 hadm_one.1 hadm_one.2 1 rfl pl
      have : 0 ≤ CxM M * NumberField.TateGlobal.ideleNorm K 1 ^ (w / 2) * ‖(((1 : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).1 pl‖ ^ (-(M : ℝ)) :=
        (norm_nonneg _).trans h
      have hp : 0 < NumberField.TateGlobal.ideleNorm K 1 ^ (w / 2) * ‖(((1 : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).1 pl‖ ^ (-(M : ℝ)) :=
        mul_pos (Real.rpow_pos_of_pos (hN0 1) _) (Real.rpow_pos_of_pos (norm_pos_iff.2 (fst_apply_ne_zero K 1 pl)) _)
      rw [mul_assoc] at this
      exact nonneg_of_mul_nonneg_left this hp
    calc F a ≤ NumberField.TateGlobal.ideleNorm K a ^ (cc - w) * Lx (M, pl) a * (Cy * NumberField.TateGlobal.ideleNorm K a ^ (w / 2)) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hx (Real.rpow_nonneg hNp.le _)) hy ENNReal.toReal_nonneg
            (mul_nonneg (Real.rpow_nonneg hNp.le _) (hLx0 (M, pl) a ha))
      _ = CxM M * Cy * NumberField.TateGlobal.ideleNorm K a ^ cc * ‖((a : AdeleRing (𝓞 K) K)).1 pl‖ ^ (-(M : ℝ)) := by
          rw [hLx]; simp only []
          have hNN : NumberField.TateGlobal.ideleNorm K a ^ (cc - w) * NumberField.TateGlobal.ideleNorm K a ^ (w / 2) *
              NumberField.TateGlobal.ideleNorm K a ^ (w / 2) = NumberField.TateGlobal.ideleNorm K a ^ cc := by
            rw [← Real.rpow_add hNp, ← Real.rpow_add hNp]; ring_nf
          calc NumberField.TateGlobal.ideleNorm K a ^ (cc - w) *
                (CxM M * NumberField.TateGlobal.ideleNorm K a ^ (w / 2) * ‖((a : AdeleRing (𝓞 K) K)).1 pl‖ ^ (-(M : ℝ))) *
                (Cy * NumberField.TateGlobal.ideleNorm K a ^ (w / 2))
              = CxM M * Cy * (NumberField.TateGlobal.ideleNorm K a ^ (cc - w) * NumberField.TateGlobal.ideleNorm K a ^ (w / 2) *
                  NumberField.TateGlobal.ideleNorm K a ^ (w / 2)) * ‖((a : AdeleRing (𝓞 K) K)).1 pl‖ ^ (-(M : ℝ)) := by ring
            _ = _ := by rw [hNN]

  have hδc : 0 < (δx + δy) + cc := by rw [hcc]; linarith
  have hδc₂ : 0 < (δx + δy) + 2 * cc := by rw [hcc]; linarith
  have hint : Integrable F (NumberField.Idele.sPartMeasure K ∅) :=
    NumberField.Idele.integrable_sPartMeasure_empty_of_norm_le_ideleNorm_rpow_mul_prod_min_one_rpow_of_norm_le_rpow_neg K F
      hFm.aestronglyMeasurable (δx + δy) cc (Cx * Cy) hδc hδc₂ hsmall hlarge
  have hFfin : ∫⁻ a, ‖F a‖ₑ ∂(NumberField.Idele.sPartMeasure K ∅) < ⊤ := hasFiniteIntegral_iff_enorm.1 hint.hasFiniteIntegral

  set C₀ : ℝ≥0∞ := ENNReal.ofReal (Bs * NumberField.TateGlobal.ideleNorm K t₀ ^ (cc - w)) with hC₀
  set f : (AdeleRing (𝓞 K) K)ˣ → ℝ≥0∞ := fun a => C₀ * (ENNReal.ofReal (NumberField.TateGlobal.ideleNorm K a ^ (cc - w)) * Ex a * Ey a)
    with hf
  have hfm : Measurable f :=
    measurable_const.mul (((Measurable.ennreal_ofReal (measurable_ideleNorm_rpow K _)).mul hExm).mul hEym)
  have hfF : ∀ a, f a = C₀ * ‖F a‖ₑ := by
    intro a
    rw [hf, hF]; simp only []
    rw [Real.enorm_eq_ofReal (hF0 a), ENNReal.ofReal_mul (mul_nonneg (Real.rpow_nonneg (hN0 a).le _) ENNReal.toReal_nonneg),
      ENNReal.ofReal_mul (Real.rpow_nonneg (hN0 a).le _), ENNReal.ofReal_toReal (hExfin a), ENNReal.ofReal_toReal (hEyfin a)]
  have hffin : ∫⁻ a, f a ∂(NumberField.Idele.sPartMeasure K ∅) < ⊤ := by
    simp_rw [hfF]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hFfin
  set Shell : Set (AdeleRing (𝓞 K) K)ˣ := {t | ∀ v ∈ S, Valued.v (((t : AdeleRing (𝓞 K) K)).2 v) = Valued.v (((t₀ : AdeleRing (𝓞 K) K)).2 v)}
    with hShell
  have hShellm : MeasurableSet Shell := measurableSet_shell K S t₀
  set G : (AdeleRing (𝓞 K) K)ˣ → ℝ≥0∞ := fun t => Shell.indicator (fun t => f (partAt K ∅ t)) t with hG
  have hGm : Measurable G := (hfm.comp (measurable_partAt K ∅)).indicator hShellm

  have hpt : ∀ (a : (AdeleRing (𝓞 K) K)ˣ) (kk : AdelicGL2 (𝓞 K) K), kk ∈ adelicMaximalCompact K →
      ‖whittakerCoefficient K pins ψ x 1 (diagOne (partAt K S a) * kk) *
          (starRingEnd ℂ) (whittakerCoefficient K pins ψ y 1 (diagOne (partAt K S a) * kk)) *
          φ s (diagOne (partAt K S a) * kk)‖ₑ *
        ENNReal.ofReal (NumberField.TateGlobal.ideleNorm K (partAt K S a) ^ (-w - 1)) ≤ G (partAt K S a) := by
    intro a kk hkk
    set t : (AdeleRing (𝓞 K) K)ˣ := partAt K S a with ht
    have htoff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → ((t : AdeleRing (𝓞 K) K)).2 v = 1 :=
      fun v hv => partAt_snd_of_not_mem K S a hv
    obtain ⟨ρ, hρ1, hρS, hρv, hP4⟩ :=
      AutomorphicForm.RankinSelberg.whittakerCoefficient_mul_conj_mul_section_diagOne_mul_eq_of_ball_surgery K hα S D₀ ωx ωy w ν
        hων x₀ nb hnb hx₀cong t₀ ht₀inf ht₀ m ht₀box k₀ hk₀ κ hκ r u cs husupp hWmult hμball hboxvan x hxsum hxG hxZ hxKS n
        hn hxlow y hyG hyZ hyKS hycong hylow finf φ hφ hφKS hφsupp hφval s kk hkk
    have hval := hP4 t htoff
    rw [hval]
    by_cases hsupp : ∀ v ∈ S, Valued.v (((kk : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 0).2 v) ≤
        Valued.v (((kk : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 1).2 v) * e
    · rw [if_pos hsupp]
      by_cases hball : ∀ v ∈ S, Valued.v ((((t * ρ) : AdeleRing (𝓞 K) K)).2 v - ((t₀ : AdeleRing (𝓞 K) K)).2 v) ≤
          Valued.v (((t₀ : AdeleRing (𝓞 K) K)).2 v) * eb
      · rw [if_pos hball]

        have hshell : t ∈ Shell := valued_eq_of_ball K S t₀ ρ t nb hnb hρv hball
        have hNt : NumberField.TateGlobal.ideleNorm K t =
            NumberField.TateGlobal.ideleNorm K (partAt K ∅ t) * NumberField.TateGlobal.ideleNorm K t₀ :=
          ideleNorm_eq_of_shell K S t₀ t ht₀inf ht₀ htoff hshell

        set kinf : AdelicGL2 (𝓞 K) K := adelicArchGLIncl K (glArch (𝓞 K) K kk) with hkinf
        obtain ⟨hkfin, hkarch⟩ := (mem_adelicMaximalCompact_iff (K := K)).1 hkk
        have hkinf1 : glFin (𝓞 K) K kinf = 1 := glFin_adelicArchGLIncl K _
        have hkinf2 : ∀ pl : InfinitePlace K, IsRowIsometry (archComponent K pl (glArch (𝓞 K) K kinf)) := by
          intro pl; rw [hkinf, glArch_adelicArchGLIncl]; exact hkarch pl
        have ha2 : (((partAt K ∅ t) : AdeleRing (𝓞 K) K)).2 = 1 := partAt_empty_snd K t

        have h1 : ‖((NumberField.TateGlobal.ideleNorm K t : ℝ) : ℂ) ^ (s + 1 / 2)‖ₑ =
            ENNReal.ofReal (NumberField.TateGlobal.ideleNorm K t ^ (σ + 1 / 2)) := by
          rw [← ofReal_norm_eq_enorm, Complex.norm_cpow_eq_rpow_re_of_pos (hN0 t)]
          simp [hσ]
        have h2 : ‖finf kinf‖ₑ ≤ ENNReal.ofReal Bs := by
          rw [← ofReal_norm_eq_enorm, hkinf, norm_finf_eq_norm_section K S n ν hν1 finf φ hφval s kk hkk hsupp]
          exact ENNReal.ofReal_le_ofReal (hBs kk hkk)
        have h3 := hExdom kinf hkinf1 hkinf2 (partAt K ∅ t) ha2
        have h4 : ‖(starRingEnd ℂ) (whittakerCoefficient K pins ψ y 1 (diagOne (partAt K ∅ t) * kinf * diagOne t₀))‖ₑ ≤ Ey (partAt K ∅ t) := by
          rw [RCLike.enorm_conj]; exact hEydom kinf hkinf1 hkinf2 (partAt K ∅ t) ha2

        rw [hG]; simp only []
        rw [indicator_of_mem hshell]
        calc ‖((NumberField.TateGlobal.ideleNorm K t : ℝ) : ℂ) ^ (s + 1 / 2) * finf kinf *
              (whittakerCoefficient K pins ψ x₀ 1 (diagOne (partAt K ∅ t) * kinf * (diagOne t₀ * κ)) *
                (starRingEnd ℂ) (whittakerCoefficient K pins ψ y 1 (diagOne (partAt K ∅ t) * kinf * diagOne t₀)))‖ₑ *
              ENNReal.ofReal (NumberField.TateGlobal.ideleNorm K t ^ (-w - 1))
            = ENNReal.ofReal (NumberField.TateGlobal.ideleNorm K t ^ (σ + 1 / 2)) * ‖finf kinf‖ₑ *
                (‖whittakerCoefficient K pins ψ x₀ 1 (diagOne (partAt K ∅ t) * kinf * (diagOne t₀ * κ))‖ₑ *
                  ‖(starRingEnd ℂ) (whittakerCoefficient K pins ψ y 1 (diagOne (partAt K ∅ t) * kinf * diagOne t₀))‖ₑ) *
                ENNReal.ofReal (NumberField.TateGlobal.ideleNorm K t ^ (-w - 1)) := by
              rw [enorm_mul, enorm_mul, enorm_mul, h1]
          _ ≤ ENNReal.ofReal (NumberField.TateGlobal.ideleNorm K t ^ (σ + 1 / 2)) * ENNReal.ofReal Bs *
                (Ex (partAt K ∅ t) * Ey (partAt K ∅ t)) * ENNReal.ofReal (NumberField.TateGlobal.ideleNorm K t ^ (-w - 1)) := by
              gcongr
          _ = f (partAt K ∅ t) := by
              rw [hf]; simp only []
              rw [hC₀]
              have hNp := hN0 t
              have hpow : NumberField.TateGlobal.ideleNorm K t ^ (σ + 1 / 2) * NumberField.TateGlobal.ideleNorm K t ^ (-w - 1) =
                  NumberField.TateGlobal.ideleNorm K (partAt K ∅ t) ^ (cc - w) * NumberField.TateGlobal.ideleNorm K t₀ ^ (cc - w) := by
                rw [← Real.rpow_add hNp, hNt, Real.mul_rpow (hN0 _).le (hN0 _).le, hcc]; ring_nf
              have key : ENNReal.ofReal (NumberField.TateGlobal.ideleNorm K t ^ (σ + 1 / 2)) *
                  ENNReal.ofReal (NumberField.TateGlobal.ideleNorm K t ^ (-w - 1)) =
                  ENNReal.ofReal (NumberField.TateGlobal.ideleNorm K t₀ ^ (cc - w)) *
                    ENNReal.ofReal (NumberField.TateGlobal.ideleNorm K (partAt K ∅ t) ^ (cc - w)) := by
                rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hNp.le _), hpow,
                  ENNReal.ofReal_mul (Real.rpow_nonneg (hN0 _).le _), mul_comm]
              rw [ENNReal.ofReal_mul hBs0]
              calc ENNReal.ofReal (NumberField.TateGlobal.ideleNorm K t ^ (σ + 1 / 2)) * ENNReal.ofReal Bs *
                    (Ex (partAt K ∅ t) * Ey (partAt K ∅ t)) * ENNReal.ofReal (NumberField.TateGlobal.ideleNorm K t ^ (-w - 1))
                  = ENNReal.ofReal Bs * (ENNReal.ofReal (NumberField.TateGlobal.ideleNorm K t ^ (σ + 1 / 2)) *
                      ENNReal.ofReal (NumberField.TateGlobal.ideleNorm K t ^ (-w - 1))) * Ex (partAt K ∅ t) * Ey (partAt K ∅ t) := by
                    ring
                _ = _ := by rw [key]; ring
      · rw [if_neg hball, mul_zero, enorm_zero, zero_mul]
        exact zero_le
    · rw [if_neg hsupp, enorm_zero, zero_mul]
      exact zero_le

  have hinner : ∀ a : (AdeleRing (𝓞 K) K)ˣ,
      (∫⁻ kk, ‖whittakerCoefficient K pins ψ x 1 (diagOne (partAt K S a) * (kk : AdelicGL2 (𝓞 K) K)) *
          (starRingEnd ℂ) (whittakerCoefficient K pins ψ y 1 (diagOne (partAt K S a) * (kk : AdelicGL2 (𝓞 K) K))) *
          φ s (diagOne (partAt K S a) * (kk : AdelicGL2 (𝓞 K) K))‖ₑ *
        ENNReal.ofReal (NumberField.TateGlobal.ideleNorm K (partAt K S a) ^ (-w - 1)) ∂(maximalCompactHaar K)) ≤ G (partAt K S a) := by
    intro a
    refine (lintegral_mono fun kk : adelicMaximalCompact K => hpt a (kk : AdelicGL2 (𝓞 K) K) kk.property).trans ?_
    rw [lintegral_const, measure_univ, mul_one]

  have hshellint : ∫⁻ t, G t ∂(NumberField.Idele.sPartMeasure K S) = ∫⁻ t, f t ∂(NumberField.Idele.sPartMeasure K ∅) := by
    set φo : HeightOneSpectrum (𝓞 K) → ℤ → ℝ≥0∞ := fun v mm => if mm = ord K v t₀ then 1 else 0 with hφo
    have hfm' : Measurable (fun t : (AdeleRing (𝓞 K) K)ˣ => f (partAt K ∅ t)) := hfm.comp (measurable_partAt K ∅)
    have hG1 : ∀ a b : (AdeleRing (𝓞 K) K)ˣ, ((a : AdeleRing (𝓞 K) K)).1 = ((b : AdeleRing (𝓞 K) K)).1 →
        f (partAt K ∅ a) = f (partAt K ∅ b) := fun a b h => by rw [partAt_empty_eq_of_fst_eq K h]
    have hCH := NumberField.Idele.lintegral_mul_prod_ord_sPartMeasure_eq_lintegral_sPartMeasure_empty_mul_prod_tsum K S
      (fun t => f (partAt K ∅ t)) hfm' hG1 φo
    have hprod : ∀ t : (AdeleRing (𝓞 K) K)ˣ, (f (partAt K ∅ t) * ∏ v ∈ S, φo v (ord K v t)) = G t := by
      intro t
      rw [hG]; simp only []
      by_cases htt : t ∈ Shell
      · rw [indicator_of_mem htt, Finset.prod_eq_one (fun v hv => ?_), mul_one]
        rw [hφo]; show (if ord K v t = ord K v t₀ then (1 : ℝ≥0∞) else 0) = 1
        rw [if_pos ((valued_eq_iff_ord_eq K v t t₀).1 (htt v hv))]
      · rw [indicator_of_notMem htt]
        have : ∃ v ∈ S, ¬ Valued.v (((t : AdeleRing (𝓞 K) K)).2 v) = Valued.v (((t₀ : AdeleRing (𝓞 K) K)).2 v) := by
          by_contra h; push Not at h; exact htt h
        obtain ⟨v, hv, hne⟩ := this
        rw [Finset.prod_eq_zero hv, mul_zero]
        show (if ord K v t = ord K v t₀ then (1 : ℝ≥0∞) else 0) = 0
        rw [if_neg (fun h => hne ((valued_eq_iff_ord_eq K v t t₀).2 h))]
    have htsum : ∀ v ∈ S, ∑' mm : ℤ, φo v mm = 1 := fun v _ => by
      rw [hφo]; simpa using tsum_ite_eq (ord K v t₀) (fun _ : ℤ => (1 : ℝ≥0∞))
    simp_rw [hprod] at hCH
    rw [hCH, Finset.prod_eq_one htsum, mul_one]
    rw [NumberField.Idele.sPartMeasure, lintegral_map hfm' (measurable_partAt K ∅), lintegral_map hfm (measurable_partAt K ∅)]
    simp_rw [partAt_empty_partAt_empty]

  calc (∫⁻ t, ∫⁻ kk,
          ‖whittakerCoefficient K pins ψ x 1 (diagOne t * (kk : AdelicGL2 (𝓞 K) K)) *
              (starRingEnd ℂ) (whittakerCoefficient K pins ψ y 1 (diagOne t * (kk : AdelicGL2 (𝓞 K) K))) *
              φ s (diagOne t * (kk : AdelicGL2 (𝓞 K) K))‖ₑ *
            ENNReal.ofReal (NumberField.TateGlobal.ideleNorm K t ^ (-w - 1))
          ∂(maximalCompactHaar K) ∂(NumberField.Idele.sPartMeasure K S))
      ≤ ∫⁻ a, (∫⁻ kk,
          ‖whittakerCoefficient K pins ψ x 1 (diagOne (partAt K S a) * (kk : AdelicGL2 (𝓞 K) K)) *
              (starRingEnd ℂ) (whittakerCoefficient K pins ψ y 1 (diagOne (partAt K S a) * (kk : AdelicGL2 (𝓞 K) K))) *
              φ s (diagOne (partAt K S a) * (kk : AdelicGL2 (𝓞 K) K))‖ₑ *
            ENNReal.ofReal (NumberField.TateGlobal.ideleNorm K (partAt K S a) ^ (-w - 1)) ∂(maximalCompactHaar K))
          ∂((idelicHaar K).restrict (NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K (↑S : Set (HeightOneSpectrum (𝓞 K))))) := by
        rw [NumberField.Idele.sPartMeasure]
        exact lintegral_map_le _ _
    _ ≤ ∫⁻ a, G (partAt K S a)
          ∂((idelicHaar K).restrict (NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K (↑S : Set (HeightOneSpectrum (𝓞 K))))) :=
        lintegral_mono hinner
    _ = ∫⁻ t, G t ∂(NumberField.Idele.sPartMeasure K S) := by
        rw [NumberField.Idele.sPartMeasure, lintegral_map hGm (measurable_partAt K S)]
    _ = ∫⁻ t, f t ∂(NumberField.Idele.sPartMeasure K ∅) := hshellint
    _ < ⊤ := hffin

end
end S_AutomorphicForm_RankinSelberg_lintegral_torus_pair_lt_top_of_ball_surgery
end P2MW
export P2MW.S_AutomorphicForm_RankinSelberg_lintegral_torus_pair_lt_top_of_ball_surgery (solution)
