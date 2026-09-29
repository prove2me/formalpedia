-- Prove2me | solution 1 for AutomorphicForm.exists_pos_eventually_le_sub_one_half_mul_setIntegral_adelicHeight_weyl_unipotent_rpow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/199b1638-412d-5351-983d-62ea159388b3

import Mathlib
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_LanglandsTunnell_TateLocalZeta
import Definitions.Def_NumberField_PrimeNormSums
import Theorems.Thm_AutomorphicForm_LocalIntertwining_integral_adeleRing_pureTensor_prod_mul_finprod_unramifiedWeylIntegrand_mul_tprod
import Theorems.Thm_LanglandsTunnell_TateLocal_modulus_adicCompletion_eq_nnnorm
import Theorems.Thm_FrobeniusDensity_primeSum_toReal_add_log_isBigO
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_pos_eventually_le_sub_one_half_mul_setIntegral_adelicHeight_weyl_unipotent_rpow
p2m_attr_erase "instance" "instCountableOfNumberField_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions"
p2m_attr_erase "simp" "NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq AutomorphicForm.whittakerCoefficient_zero NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicHeight IsDedekindDomain
open AutomorphicForm AutomorphicForm.WindowedSiegel Filter Topology
open scoped Classical

namespace P2mMass

variable (F : Type) [Field F] [NumberField F]

noncomputable def wn (x : AdeleRing (𝓞 F) F) : AdelicGL2 (𝓞 F) F :=
  (adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 x

theorem wn_val (x : AdeleRing (𝓞 F) F) :
    ((wn F x : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) = !![0, 1; 1, x] := by
  rw [wn, adelicWeyl, ← map_inv, gl2Weyl_inv, Units.val_mul, unipotentGL2_coe]
  have : ((globalPoints (𝓞 F) F gl2Weyl : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))
      = !![0, 1; 1, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [globalPoints, gl2Weyl]
  rw [this]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem zero_fst_apply (w : InfinitePlace F) : (0 : AdeleRing (𝓞 F) F).1 w = 0 := rfl
theorem one_fst_apply (w : InfinitePlace F) : (1 : AdeleRing (𝓞 F) F).1 w = 1 := rfl
theorem zero_snd_apply (v : HeightOneSpectrum (𝓞 F)) : (0 : AdeleRing (𝓞 F) F).2 v = 0 := rfl
theorem one_snd_apply (v : HeightOneSpectrum (𝓞 F)) : (1 : AdeleRing (𝓞 F) F).2 v = 1 := rfl

theorem localHeight_wn (x : AdeleRing (𝓞 F) F) (w : InfinitePlace F) :
    localHeight (archComponent F w (glArch (𝓞 F) F (wn F x))) = (1 + ‖x.1 w‖ ^ 2)⁻¹ := by
  have hent : ∀ i j, (archComponent F w (glArch (𝓞 F) F (wn F x)) : Matrix (Fin 2) (Fin 2) w.Completion) i j
      = ((!![0, 1; 1, x] : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).1 w := by
    intro i j
    rw [archComponent_apply, glArch_apply, wn_val]
  unfold localHeight rowNormSq
  rw [Matrix.det_fin_two, hent, hent, hent, hent]
  simp [zero_fst_apply, one_fst_apply]

theorem finLocalHeight_wn (x : AdeleRing (𝓞 F) F) (v : HeightOneSpectrum (𝓞 F)) :
    finLocalHeight (finComponent (𝓞 F) F v (glFin (𝓞 F) F (wn F x))) = (max 1 ‖x.2 v‖ ^ 2)⁻¹ := by
  have hent : ∀ i j, (finComponent (𝓞 F) F v (glFin (𝓞 F) F (wn F x)) :
      Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j
      = ((!![0, 1; 1, x] : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).2 v := by
    intro i j
    rw [finComponent_apply, glFin_apply, wn_val]
  unfold finLocalHeight rowMaxNorm
  rw [Matrix.det_fin_two, hent, hent, hent, hent]
  simp [zero_snd_apply, one_snd_apply]

theorem adelicHeight_wn (x : AdeleRing (𝓞 F) F) :
    adelicHeight F (wn F x) = (∏ w : InfinitePlace F, ((1 + ‖x.1 w‖ ^ 2)⁻¹) ^ w.mult)
      * ∏ᶠ v : HeightOneSpectrum (𝓞 F), (max 1 ‖x.2 v‖ ^ 2)⁻¹ := by
  unfold adelicHeight archHeight finHeight
  simp_rw [localHeight_wn, finLocalHeight_wn]

theorem inv_pow_rpow {a : ℝ} (ha : 0 < a) (m : ℕ) (r : ℝ) :
    ((a⁻¹) ^ m) ^ r = a ^ (-((m : ℝ) * r)) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (inv_nonneg.mpr ha.le), Real.inv_rpow ha.le,
    Real.rpow_neg ha.le]

noncomputable def archF (σ : ℝ) (y : mixedEmbedding.mixedSpace F) : ℝ :=
  (∏ v : {w : InfinitePlace F // w.IsReal}, (1 + ‖y.1 v‖ ^ 2) ^ (-(2 * σ + 1) / 2)) *
    ∏ v : {w : InfinitePlace F // w.IsComplex}, (1 + ‖y.2 v‖ ^ 2) ^ (-(4 * σ + 2) / 2)

noncomputable def finF (σ : ℝ) (v : HeightOneSpectrum (𝓞 F)) (y : v.adicCompletion F) : ℝ :=
  (max 1 ‖y‖) ^ (-(2 * σ + 1))

theorem archF_pos (σ : ℝ) (y : mixedEmbedding.mixedSpace F) : 0 < archF F σ y := by
  unfold archF
  refine mul_pos (Finset.prod_pos fun v _ => ?_) (Finset.prod_pos fun v _ => ?_) <;> positivity

theorem finF_pos (σ : ℝ) (v : HeightOneSpectrum (𝓞 F)) (y : v.adicCompletion F) : 0 < finF F σ v y := by
  unfold finF
  exact Real.rpow_pos_of_pos (by positivity) _

theorem finF_le_one {σ : ℝ} (hσ : 0 ≤ 2 * σ + 1) (v : HeightOneSpectrum (𝓞 F)) (y : v.adicCompletion F) :
    finF F σ v y ≤ 1 := by
  unfold finF
  exact Real.rpow_le_one_of_one_le_of_nonpos (le_max_left _ _) (by linarith)

theorem finF_eq_one_of_norm_le_one (σ : ℝ) (v : HeightOneSpectrum (𝓞 F)) {y : v.adicCompletion F}
    (hy : ‖y‖ ≤ 1) : finF F σ v y = 1 := by
  unfold finF
  rw [max_eq_left hy, Real.one_rpow]

theorem archF_ringEquiv (σ : ℝ) (x : InfiniteAdeleRing F) :
    archF F σ (InfiniteAdeleRing.ringEquiv_mixedSpace F x)
      = (∏ w : InfinitePlace F, ((1 + ‖x w‖ ^ 2)⁻¹) ^ w.mult) ^ (σ + 1 / 2) := by
  rw [← Real.finsetProd_rpow _ _ (fun w _ => by positivity), InfinitePlace.prod_eq_prod_mul_prod, archF,
    InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
  congr 1
  · refine Finset.prod_congr rfl fun v _ => ?_
    rw [InfinitePlace.mult_isReal, inv_pow_rpow (by positivity), Nat.cast_one, one_mul,
      (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal v.2).norm_map_of_map_zero
        (map_zero _)]
    congr 1
    ring
  · refine Finset.prod_congr rfl fun v _ => ?_
    rw [InfinitePlace.mult_isComplex, inv_pow_rpow (by positivity), Nat.cast_ofNat,
      (InfinitePlace.Completion.isometry_extensionEmbedding v.1).norm_map_of_map_zero (map_zero _)]
    congr 1
    ring

theorem finprod_rpow {ι : Type*} {f : ι → ℝ} (hf : ∀ i, 0 < f i) (hfs : Function.HasFiniteMulSupport f)
    (r : ℝ) : (∏ᶠ i, f i) ^ r = ∏ᶠ i, f i ^ r := by
  have hsub : Function.mulSupport (fun i => f i ^ r) ⊆ hfs.toFinset := by
    intro i hi
    simp only [Set.Finite.coe_toFinset, Function.mem_mulSupport]
    intro h1
    exact hi (by simp [h1])
  rw [finprod_eq_prod_of_mulSupport_subset _ hsub,
    finprod_eq_prod_of_mulSupport_subset _ (by simp : Function.mulSupport f ⊆ hfs.toFinset),
    Real.finsetProd_rpow _ _ fun i _ => (hf i).le]

theorem hasFiniteMulSupport_max_inv (x : AdeleRing (𝓞 F) F) :
    Function.HasFiniteMulSupport fun v : HeightOneSpectrum (𝓞 F) => (max 1 ‖x.2 v‖ ^ 2)⁻¹ := by
  have := hasFiniteMulSupport_finLocalHeight (glFin (𝓞 F) F (wn F x))
  simp_rw [finLocalHeight_wn] at this
  exact this

theorem adelicHeight_wn_rpow (σ : ℝ) (x : AdeleRing (𝓞 F) F) :
    adelicHeight F (wn F x) ^ (σ + 1 / 2)
      = archF F σ (InfiniteAdeleRing.ringEquiv_mixedSpace F x.1)
          * ∏ᶠ v : HeightOneSpectrum (𝓞 F), finF F σ v (x.2 v) := by
  rw [adelicHeight_wn, Real.mul_rpow (Finset.prod_nonneg fun w _ => by positivity)
      (finprod_nonneg fun v => by positivity), archF_ringEquiv,
    finprod_rpow (fun v => by positivity) (hasFiniteMulSupport_max_inv F x)]
  congr 1
  refine finprod_congr fun v => ?_
  rw [finF, ← inv_pow, inv_pow_rpow (by positivity)]
  congr 1
  push_cast
  ring

theorem mem_integers_iff_norm_le_one (v : HeightOneSpectrum (𝓞 F)) (y : v.adicCompletion F) :
    y ∈ (v.adicCompletionIntegers F : Set (v.adicCompletion F)) ↔ ‖y‖ ≤ 1 := by
  rw [SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers, Valued.toNormedField.norm_le_one_iff]

theorem unramifiedWeylIntegrand_eq_finF (σ : ℝ) (v : HeightOneSpectrum (𝓞 F)) (y : v.adicCompletion F) :
    (v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator (fun _ => (1 : ℂ)) y
      + (v.adicCompletionIntegers F : Set (v.adicCompletion F))ᶜ.indicator
          (fun y => LanglandsTunnell.TateLocal.charExt (1 : (v.adicCompletion F)ˣ →* ℂˣ)⁻¹ y
            * ((LanglandsTunnell.TateLocal.modulus y : ℝ) : ℂ) ^ (-(2 * (σ : ℂ) + 1))) y
      = ((finF F σ v y : ℝ) : ℂ) := by
  by_cases hy : y ∈ (v.adicCompletionIntegers F : Set (v.adicCompletion F))
  · rw [Set.indicator_of_mem hy, Set.indicator_of_notMem (Set.notMem_compl_iff.mpr hy), add_zero,
      finF_eq_one_of_norm_le_one F σ v ((mem_integers_iff_norm_le_one F v y).mp hy), Complex.ofReal_one]
  · have hy1 : 1 < ‖y‖ := not_le.mp fun h => hy ((mem_integers_iff_norm_le_one F v y).mpr h)
    have hy0 : y ≠ 0 := fun h => by rw [h, norm_zero] at hy1; exact absurd hy1 (by norm_num)
    have h1 : LanglandsTunnell.TateLocal.charExt (1 : (v.adicCompletion F)ˣ →* ℂˣ)⁻¹ y = 1 := by
      rw [LanglandsTunnell.TateLocal.charExt_of_ne_zero _ hy0, MonoidHom.inv_apply, MonoidHom.one_apply,
        inv_one, Units.val_one]
    rw [Set.indicator_of_notMem hy, Set.indicator_of_mem (Set.mem_compl hy), zero_add, h1, one_mul,
      LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm F v y, coe_nnnorm, finF,
      max_eq_right hy1.le, Complex.ofReal_cpow (norm_nonneg _)]
    push_cast
    ring_nf

theorem finprod_eq_prod_mul_finprod_subtype {ι M : Type*} [CommMonoid M] (f : ι → M)
    (hf : Function.HasFiniteMulSupport f) (S : Finset ι) :
    ∏ᶠ i, f i = (∏ i ∈ S, f i) * ∏ᶠ i : {i // i ∉ S}, f i.1 := by
  rw [← finprod_mem_univ, ← Set.union_compl_self (S : Set ι),
    finprod_mem_union' disjoint_compl_right (hf.subset Set.inter_subset_right)
      (hf.subset Set.inter_subset_right),
    finprod_mem_coe_finset, ← finprod_set_coe_eq_finprod_mem]
  rfl

theorem hasFiniteMulSupport_finF (σ : ℝ) (x : FiniteAdeleRing (𝓞 F) F) :
    Function.HasFiniteMulSupport fun v : HeightOneSpectrum (𝓞 F) => finF F σ v (x v) :=
  Filter.eventually_cofinite.mp (x.2.mono fun v hv =>
    finF_eq_one_of_norm_le_one F σ v (norm_le_one_of_mem_adicCompletionIntegers hv))

end P2mMass

namespace P2mMassZeta

open Asymptotics NumberField.PrimeNormSum

variable (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F)))

noncomputable def eulerR (t : ℝ) : ℝ :=
  ∏' v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S}, (1 - pw F t v.1)

noncomputable def logSum (t : ℝ) : ℝ :=
  ∑' v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S}, Real.log (1 - pw F t v.1)

variable {F}

theorem pw_le_half {t : ℝ} (ht : 1 ≤ t) (v : HeightOneSpectrum (𝓞 F)) : pw F t v ≤ 1 / 2 := by
  refine (pw_antitone ht v).trans ?_
  unfold pw
  rw [Real.rpow_neg (by positivity), Real.rpow_one, one_div]
  exact inv_anti₀ (by norm_num) (by exact_mod_cast two_le_absNorm v)

theorem one_sub_pw_pos {t : ℝ} (ht : 1 ≤ t) (v : HeightOneSpectrum (𝓞 F)) : 0 < 1 - pw F t v := by
  linarith [pw_le_half ht v]

theorem pw_sq_le {t : ℝ} (ht : 1 ≤ t) (v : HeightOneSpectrum (𝓞 F)) : pw F t v ^ 2 ≤ pw F 2 v := by
  have h : pw F t v ^ 2 = pw F (2 * t) v := by
    unfold pw
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    congr 1
    push_cast
    ring
  rw [h]
  exact pw_antitone (by linarith) v

theorem log_one_sub_bounds {p : ℝ} (_hp0 : 0 ≤ p) (hp : p ≤ 1 / 2) :
    -p - 2 * p ^ 2 ≤ Real.log (1 - p) ∧ Real.log (1 - p) ≤ -p := by
  have h1 : 0 < 1 - p := by linarith
  constructor
  · have h2 := Real.one_sub_inv_le_log_of_pos h1
    have h3 : -p - 2 * p ^ 2 ≤ 1 - (1 - p)⁻¹ := by
      rw [show 1 - (1 - p)⁻¹ = -p / (1 - p) by field_simp; ring]
      rw [le_div_iff₀ h1]
      nlinarith
    exact h3.trans h2
  · have := Real.log_le_sub_one_of_pos h1
    linarith

theorem abs_log_one_sub_pw_le {t : ℝ} (ht : 1 ≤ t) (v : HeightOneSpectrum (𝓞 F)) :
    |Real.log (1 - pw F t v)| ≤ 2 * pw F t v := by
  have hp0 := pw_nonneg (F := F) t v
  have hp := pw_le_half ht v
  obtain ⟨h1, h2⟩ := log_one_sub_bounds hp0 hp
  rw [abs_le]
  constructor <;> nlinarith

theorem summable_logTerm {t : ℝ} (ht : 1 < t) :
    Summable fun v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S} => Real.log (1 - pw F t v.1) := by
  refine Summable.of_norm_bounded (((summable_pw ht).mul_left 2).subtype _) fun v => ?_
  rw [Real.norm_eq_abs]
  exact abs_log_one_sub_pw_le ht.le v.1

theorem hasProd_eulerR {t : ℝ} (ht : 1 < t) :
    HasProd (fun v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S} => 1 - pw F t v.1)
      (Real.exp (logSum F S t)) :=
  Real.hasProd_of_hasSum_log (fun v => one_sub_pw_pos ht.le v.1) (summable_logTerm S ht).hasSum

theorem eulerR_eq_exp {t : ℝ} (ht : 1 < t) : eulerR F S t = Real.exp (logSum F S t) :=
  (hasProd_eulerR S ht).tprod_eq

theorem eulerR_pos {t : ℝ} (ht : 1 < t) : 0 < eulerR F S t := by
  rw [eulerR_eq_exp S ht]; exact Real.exp_pos _

theorem tprod_complex_eq_eulerR {t : ℝ} (ht : 1 < t) (z : ℂ) (hz : z = -(t : ℂ)) :
    ∏' v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S},
        (1 - ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ z) = (eulerR F S t : ℂ) := by
  have h := (hasProd_eulerR S ht).map Complex.ofRealHom Complex.continuous_ofReal
  rw [← eulerR_eq_exp S ht] at h
  have h' : HasProd (fun v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S} => ((1 - pw F t v.1 : ℝ) : ℂ))
      ((eulerR F S t : ℝ) : ℂ) := h
  rw [← h'.tprod_eq]
  refine tprod_congr fun v => ?_
  simp only [Complex.ofReal_sub, Complex.ofReal_one, pw]
  rw [Complex.ofReal_cpow (Nat.cast_nonneg _), hz]
  push_cast
  rfl

theorem logSum_bounds {t : ℝ} (ht : 1 < t) :
    -(∑' v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S}, pw F t v.1) - 2 * ∑' v, pw F 2 v
        ≤ logSum F S t ∧
      logSum F S t ≤ -(∑' v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S}, pw F t v.1) := by
  have hs1 : Summable fun v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S} => pw F t v.1 :=
    (summable_pw ht).subtype _
  have hs2 : Summable fun v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S} => pw F 2 v.1 :=
    (summable_pw one_lt_two).subtype _
  have hlog := summable_logTerm S ht
  constructor
  · have h3 : ∑' v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S}, pw F 2 v.1 ≤ ∑' v, pw F 2 v :=
      (summable_pw one_lt_two).tsum_subtype_le _ _ (fun v => pw_nonneg 2 v)
    calc -(∑' v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S}, pw F t v.1) - 2 * ∑' v, pw F 2 v
        ≤ -(∑' v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S}, pw F t v.1)
            - 2 * ∑' v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S}, pw F 2 v.1 := by linarith
      _ = ∑' v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S}, (-pw F t v.1 - 2 * pw F 2 v.1) := by
          rw [hs1.neg.tsum_sub (hs2.mul_left 2), tsum_neg, tsum_mul_left]
      _ ≤ logSum F S t := by
          refine Summable.tsum_le_tsum (fun v => ?_) (hs1.neg.sub (hs2.mul_left 2)) hlog
          have := (log_one_sub_bounds (pw_nonneg t v.1) (pw_le_half ht.le v.1)).1
          have := pw_sq_le ht.le v.1
          linarith
  · calc logSum F S t ≤ ∑' v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S}, -pw F t v.1 :=
          Summable.tsum_le_tsum (fun v => (log_one_sub_bounds (pw_nonneg t v.1) (pw_le_half ht.le v.1)).2)
            hlog hs1.neg
      _ = _ := tsum_neg

theorem tsum_subtype_eq {t : ℝ} (ht : 1 < t) :
    ∑' v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S}, pw F t v.1 = (∑' v, pw F t v) - ∑ v ∈ S, pw F t v := by
  rw [← (summable_pw ht).sum_add_tsum_subtype_compl S]
  ring

theorem sum_pw_le_card {t : ℝ} (ht : 0 ≤ t) : ∑ v ∈ S, pw F t v ≤ S.card := by
  have := Finset.sum_le_card_nsmul S (fun v => pw F t v) 1 (fun v _ => pw_le_one ht v)
  simpa using this

theorem sum_pw_nonneg (t : ℝ) : 0 ≤ ∑ v ∈ S, pw F t v :=
  Finset.sum_nonneg fun v _ => pw_nonneg t v

theorem eulerR_bounds_nhds_one : ∃ M : ℝ, ∀ᶠ t in 𝓝[>] (1 : ℝ),
    Real.exp (-M) * (t - 1) ≤ eulerR F S t ∧ eulerR F S t ≤ Real.exp M * (t - 1) := by
  obtain ⟨C, hC⟩ := (FrobeniusDensity.primeSum_toReal_add_log_isBigO F).bound
  set Q : ℝ := ∑' v, pw F 2 v with hQ
  refine ⟨C + S.card + 2 * Q, ?_⟩
  filter_upwards [hC, self_mem_nhdsWithin] with t ht ht1
  have ht1 : 1 < t := ht1
  rw [primeSum_toReal, Real.norm_eq_abs, norm_one, mul_one] at ht
  obtain ⟨hP1, hP2⟩ := abs_le.mp ht
  obtain ⟨hL1, hL2⟩ := logSum_bounds S ht1
  rw [tsum_subtype_eq S ht1] at hL1 hL2
  have hS1 := sum_pw_le_card S (zero_le_one.trans ht1.le)
  have hS0 := sum_pw_nonneg S t
  have ht0 : 0 < t - 1 := by linarith
  rw [eulerR_eq_exp S ht1]
  constructor
  · calc Real.exp (-(C + S.card + 2 * Q)) * (t - 1)
        = Real.exp (-(C + S.card + 2 * Q) + Real.log (t - 1)) := by
          rw [Real.exp_add, Real.exp_log ht0]
      _ ≤ Real.exp (logSum F S t) := Real.exp_le_exp.mpr (by linarith)
  · calc Real.exp (logSum F S t)
        ≤ Real.exp ((C + S.card + 2 * Q) + Real.log (t - 1)) := Real.exp_le_exp.mpr (by linarith)
      _ = Real.exp (C + S.card + 2 * Q) * (t - 1) := by
          rw [Real.exp_add, Real.exp_log ht0]

theorem eulerR_bounds_of_two_le {t : ℝ} (ht : 2 ≤ t) :
    Real.exp (-(3 * ∑' v, pw F 2 v)) ≤ eulerR F S t ∧ eulerR F S t ≤ 1 := by
  have ht1 : 1 < t := by linarith
  obtain ⟨hL1, hL2⟩ := logSum_bounds S ht1
  have h1 : ∑' v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S}, pw F t v.1 ≤ ∑' v, pw F t v :=
    (summable_pw ht1).tsum_subtype_le _ _ (fun v => pw_nonneg t v)
  have h2 : ∑' v, pw F t v ≤ ∑' v, pw F 2 v :=
    Summable.tsum_le_tsum (fun v => pw_antitone ht v) (summable_pw ht1) (summable_pw one_lt_two)
  have h0 : 0 ≤ ∑' v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S}, pw F t v.1 :=
    tsum_nonneg fun v => pw_nonneg t v.1
  rw [eulerR_eq_exp S ht1]
  constructor
  · exact Real.exp_le_exp.mpr (by linarith)
  · rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by linarith)

end P2mMassZeta

namespace P2mMass

open P2mMassZeta NumberField.AdelicBox NumberField.InfinitePlace

variable (F : Type) [Field F] [NumberField F]

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar

@[reducible] noncomputable def kvBorel (v : HeightOneSpectrum (𝓞 F)) :
    MeasurableSpace (v.adicCompletion F) := borel _

theorem borelSpace_kvBorel (v : HeightOneSpectrum (𝓞 F)) :
    @BorelSpace (v.adicCompletion F) _ (kvBorel F v) :=
  @BorelSpace.mk _ _ (kvBorel F v) rfl

attribute [local instance] kvBorel borelSpace_kvBorel

noncomputable def μv (v : HeightOneSpectrum (𝓞 F)) : Measure (v.adicCompletion F) := Measure.addHaar

scoped instance isAddHaarMeasure_μv (v : HeightOneSpectrum (𝓞 F)) : (μv F v).IsAddHaarMeasure :=
  Measure.isAddHaarMeasure_addHaarMeasure _

noncomputable abbrev μA : Measure (AdeleRing (𝓞 F) F) := adelicAddHaar (𝓞 F) F

def cyl (S : Finset (HeightOneSpectrum (𝓞 F))) (V : Set (mixedEmbedding.mixedSpace F))
    (B : ∀ v : HeightOneSpectrum (𝓞 F), Set (v.adicCompletion F)) : Set (AdeleRing (𝓞 F) F) :=
  {x | InfiniteAdeleRing.ringEquiv_mixedSpace F x.1 ∈ V ∧ ∀ v ∈ S, x.2 v ∈ B v}

noncomputable def archConst : ℝ := (2 : ℝ) ^ nrComplexPlaces F / Real.sqrt |(discr F : ℝ)|

theorem archConst_pos : 0 < archConst F := by
  unfold archConst
  refine div_pos (by positivity) (Real.sqrt_pos_of_pos (abs_pos.mpr ?_))
  exact_mod_cast discr_ne_zero F

theorem mass_identity (S : Finset (HeightOneSpectrum (𝓞 F))) (V : Set (mixedEmbedding.mixedSpace F))
    (B : ∀ v : HeightOneSpectrum (𝓞 F), Set (v.adicCompletion F)) (σ : ℝ) (hσ : 1 / 2 < σ) :
    ((μA F) (adelicBox F)).toReal⁻¹
        * (∫ x, (cyl F S V B).indicator (fun x => adelicHeight F (wn F x) ^ (σ + 1 / 2)) x ∂(μA F))
        * eulerR F S (2 * σ)
      = archConst F * (∫ y, V.indicator (archF F σ) y)
        * ((∏ v ∈ S, ((μv F v).real (v.adicCompletionIntegers F : Set (v.adicCompletion F)))⁻¹
              * ∫ y, (B v).indicator (finF F σ v) y ∂(μv F v))
            * eulerR F S (2 * σ + 1)) := by
  have hGK := AutomorphicForm.LocalIntertwining.integral_adeleRing_pureTensor_prod_mul_finprod_unramifiedWeylIntegrand_mul_tprod
    F (μA F) S (μv F) (fun y => ((V.indicator (archF F σ) y : ℝ) : ℂ))
    (fun v y => (((B v).indicator (finF F σ v) y : ℝ) : ℂ)) (fun v => uniformizerUnit F v)
    (fun v _ => by rw [valued_uniformizerUnit]; rfl) (fun _ => 1) (fun v _ u _ => rfl)
    (fun v _ => by simp) (σ : ℂ) (by simpa using hσ)
  simp_rw [unramifiedWeylIntegrand_eq_finF F σ] at hGK
  have hpt : ∀ x : AdeleRing (𝓞 F) F,
      ((V.indicator (archF F σ) (InfiniteAdeleRing.ringEquiv_mixedSpace F x.1) : ℝ) : ℂ)
        * ((∏ v ∈ S, (((B v).indicator (finF F σ v) (x.2 v) : ℝ) : ℂ))
            * ∏ᶠ v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S}, ((finF F σ v.1 (x.2 v.1) : ℝ) : ℂ))
      = (((cyl F S V B).indicator (fun x => adelicHeight F (wn F x) ^ (σ + 1 / 2)) x : ℝ) : ℂ) := by
    intro x
    by_cases hx : x ∈ cyl F S V B
    · have hfin : Function.HasFiniteMulSupport
          fun v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S} => finF F σ v.1 (x.2 v.1) :=
        (hasFiniteMulSupport_finF F σ x.2).fun_comp_of_injective Subtype.val_injective
      have hfp : (∏ᶠ v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S}, ((finF F σ v.1 (x.2 v.1) : ℝ) : ℂ))
          = ((∏ᶠ v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S}, finF F σ v.1 (x.2 v.1) : ℝ) : ℂ) := by
        have := (MonoidHom.map_finprod (Complex.ofRealHom : ℝ →* ℂ) hfin).symm
        first
          | simpa only [Complex.ofRealHom_eq_coe] using this
          | (have h' := this; simp only [Complex.ofRealHom_eq_coe] at h' ⊢; exact h')
          | (have h' := this; simp only [Complex.ofRealHom_eq_coe] at h'; exact h')
          | exact this
          | (simpa only [Complex.ofRealHom_eq_coe, Function.comp_def] using this)
      rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx.1, adelicHeight_wn_rpow,
        finprod_eq_prod_mul_finprod_subtype _ (hasFiniteMulSupport_finF F σ x.2) S,
        Finset.prod_congr rfl fun v hv => by rw [Set.indicator_of_mem (hx.2 v hv)], hfp]
      push_cast
      ring
    · rw [Set.indicator_of_notMem hx]
      simp only [cyl, Set.mem_setOf_eq, not_and_or, not_forall, exists_prop] at hx
      rcases hx with hx | ⟨v, hv, hxv⟩
      · rw [Set.indicator_of_notMem hx]
        push_cast
        ring
      · rw [Finset.prod_eq_zero hv (by rw [Set.indicator_of_notMem hxv]; push_cast; ring)]
        push_cast
        ring
  simp_rw [hpt, integral_complex_ofReal] at hGK
  simp only [MonoidHom.one_apply, Units.val_one, one_mul] at hGK
  have h2σ : (1 : ℝ) < 2 * σ := by linarith
  rw [tprod_complex_eq_eulerR S h2σ (-(2 * (σ : ℂ))) (by push_cast; ring),
    tprod_complex_eq_eulerR S (by linarith : (1 : ℝ) < 2 * σ + 1) (-(2 * (σ : ℂ) + 1))
      (by push_cast; ring)] at hGK
  unfold archConst
  exact_mod_cast hGK

theorem integrable_archF {σ : ℝ} (hσ : 0 < σ) :
    Integrable (archF F σ) (volume : Measure (mixedEmbedding.mixedSpace F)) := by
  have hR : Integrable (fun t : ℝ => (1 + ‖t‖ ^ 2) ^ (-(2 * σ + 1) / 2)) volume :=
    integrable_rpow_neg_one_add_norm_sq (E := ℝ) (μ := volume)
      (by rw [Module.finrank_self]; push_cast; linarith)
  have hC : Integrable (fun t : ℂ => (1 + ‖t‖ ^ 2) ^ (-(4 * σ + 2) / 2)) volume :=
    integrable_rpow_neg_one_add_norm_sq (E := ℂ) (μ := volume)
      (by rw [Complex.finrank_real_complex]; push_cast; linarith)
  have h1 : Integrable (fun x : {w : InfinitePlace F // w.IsReal} → ℝ =>
      ∏ v, (1 + ‖x v‖ ^ 2) ^ (-(2 * σ + 1) / 2)) (Measure.pi fun _ => volume) :=
    Integrable.fintype_prod (f := fun _ t => (1 + ‖t‖ ^ 2) ^ (-(2 * σ + 1) / 2)) fun _ => hR
  have h2 : Integrable (fun x : {w : InfinitePlace F // w.IsComplex} → ℂ =>
      ∏ v, (1 + ‖x v‖ ^ 2) ^ (-(4 * σ + 2) / 2)) (Measure.pi fun _ => volume) :=
    Integrable.fintype_prod (f := fun _ t => (1 + ‖t‖ ^ 2) ^ (-(4 * σ + 2) / 2)) fun _ => hC
  rw [← volume_pi] at h1 h2
  have h := h1.mul_prod h2
  rw [← Measure.volume_eq_prod] at h
  exact h

theorem archF_antitone {σ σ' : ℝ} (h : σ ≤ σ') (y : mixedEmbedding.mixedSpace F) :
    archF F σ' y ≤ archF F σ y := by
  unfold archF
  refine mul_le_mul ?_ ?_ (Finset.prod_nonneg fun v _ => by positivity)
    (Finset.prod_nonneg fun v _ => by positivity)
  · refine Finset.prod_le_prod (fun v _ => by positivity) fun v _ => ?_
    exact Real.rpow_le_rpow_of_exponent_le (by nlinarith [norm_nonneg (y.1 v)]) (by linarith)
  · refine Finset.prod_le_prod (fun v _ => by positivity) fun v _ => ?_
    exact Real.rpow_le_rpow_of_exponent_le (by nlinarith [norm_nonneg (y.2 v)]) (by linarith)

theorem indicator_archF_nonneg (σ : ℝ) (V : Set (mixedEmbedding.mixedSpace F))
    (y : mixedEmbedding.mixedSpace F) : 0 ≤ V.indicator (archF F σ) y :=
  Set.indicator_nonneg (fun y _ => (archF_pos F σ y).le) y

theorem integral_indicator_archF_pos {σ : ℝ} (hσ : 0 < σ) {V : Set (mixedEmbedding.mixedSpace F)}
    (hV : IsOpen V) (hVne : V.Nonempty) : 0 < ∫ y, V.indicator (archF F σ) y := by
  rw [integral_pos_iff_support_of_nonneg (indicator_archF_nonneg F σ V)
    ((integrable_archF F hσ).indicator hV.measurableSet), Set.support_indicator]
  have : V ∩ Function.support (archF F σ) = V := by
    refine Set.inter_eq_left.mpr fun y _ => ?_
    exact (archF_pos F σ y).ne'
  rw [this]
  exact hV.measure_pos _ hVne

theorem integral_indicator_archF_mono {σ σ' : ℝ} (hσ : 0 < σ) (h : σ ≤ σ')
    {V : Set (mixedEmbedding.mixedSpace F)} (hV : MeasurableSet V) :
    ∫ y, V.indicator (archF F σ') y ≤ ∫ y, V.indicator (archF F σ) y :=
  integral_mono ((integrable_archF F (hσ.trans_le h)).indicator hV) ((integrable_archF F hσ).indicator hV)
    fun y => Set.indicator_le_indicator (archF_antitone F h y)

theorem continuous_finF (σ : ℝ) (v : HeightOneSpectrum (𝓞 F)) : Continuous (finF F σ v) := by
  unfold finF
  exact (continuous_const.max continuous_norm).rpow_const fun y => Or.inl (by positivity)

theorem finF_ge_on_ball {σ : ℝ} (hσ : σ ≤ 1) (v : HeightOneSpectrum (𝓞 F))
    (a : v.adicCompletion F) (r : ℝ) {y : v.adicCompletion F} (hy : y ∈ Metric.ball a r) :
    (max 1 (‖a‖ + r)) ^ (-(3 : ℝ)) ≤ finF F σ v y := by
  have hy' : ‖y‖ ≤ ‖a‖ + r := by
    have h1 : ‖y - a‖ < r := by rwa [Metric.mem_ball, dist_eq_norm] at hy
    calc ‖y‖ = ‖a + (y - a)‖ := by rw [add_sub_cancel]
      _ ≤ ‖a‖ + ‖y - a‖ := norm_add_le _ _
      _ ≤ ‖a‖ + r := by linarith
  unfold finF
  calc (max 1 (‖a‖ + r)) ^ (-(3 : ℝ)) ≤ (max 1 ‖y‖) ^ (-(3 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) (max_le_max le_rfl hy') (by norm_num)
    _ ≤ (max 1 ‖y‖) ^ (-(2 * σ + 1)) :=
        Real.rpow_le_rpow_of_exponent_le (le_max_left _ _) (by linarith)

variable {F} in
theorem measureReal_ball_pos (v : HeightOneSpectrum (𝓞 F)) (a : v.adicCompletion F) {r : ℝ} (hr : 0 < r) :
    0 < (μv F v).real (Metric.ball a r) :=
  ENNReal.toReal_pos (Metric.isOpen_ball.measure_pos _ ⟨a, Metric.mem_ball_self hr⟩).ne'
    measure_ball_lt_top.ne

variable {F} in
theorem measureReal_integers_pos (v : HeightOneSpectrum (𝓞 F)) :
    0 < (μv F v).real (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := by
  refine ENNReal.toReal_pos ((Valued.isOpen_valuationSubring _).measure_pos (μv F v)
    ⟨0, zero_mem _⟩).ne' ?_
  exact (isCompact_iff_compactSpace.mpr (NumberField.AdelicHaar.compactSpace_adicCompletionIntegers
    (𝓞 F) F v)).measure_lt_top.ne

theorem local_factor_ge {σ : ℝ} (hσ0 : 1 / 2 < σ) (hσ : σ ≤ 1) (v : HeightOneSpectrum (𝓞 F))
    (a : v.adicCompletion F) (r : ℝ) :
    (μv F v).real (Metric.ball a r) * (max 1 (‖a‖ + r)) ^ (-(3 : ℝ))
      ≤ ∫ y, (Metric.ball a r).indicator (finF F σ v) y ∂(μv F v) := by
  rw [integral_indicator measurableSet_ball]
  have hint : IntegrableOn (finF F σ v) (Metric.ball a r) (μv F v) := by
    refine Measure.integrableOn_of_bounded (M := 1) measure_ball_lt_top.ne
      (continuous_finF F σ v).aestronglyMeasurable (ae_of_all _ fun y => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (finF_pos F σ v y)]
    exact finF_le_one F (by linarith) v y
  have := setIntegral_ge_of_const_le (μ := μv F v) measurableSet_ball measure_ball_lt_top.ne
    (fun y hy => finF_ge_on_ball F hσ v a r hy) hint
  rwa [smul_eq_mul] at this

theorem exists_open_mixedSpace (U₀ : Set (InfiniteAdeleRing F)) (hU₀ : IsOpen U₀ ∧ U₀.Nonempty) :
    ∃ V : Set (mixedEmbedding.mixedSpace F), IsOpen V ∧ V.Nonempty ∧
      InfiniteAdeleRing.ringEquiv_mixedSpace F ⁻¹' V ⊆ U₀ := by
  obtain ⟨a, ha⟩ := hU₀.2
  obtain ⟨I, u, hu, hsub⟩ :=
    (isOpen_pi_iff (s := (U₀ : Set ((w : InfinitePlace F) → w.Completion)))).mp hU₀.1 a ha
  have hballs : ∀ w ∈ I, ∃ ε > 0, Metric.ball (a w) ε ⊆ u w := fun w hw =>
    Metric.isOpen_iff.mp (hu w hw).1 (a w) (hu w hw).2
  choose! ε hε hεsub using hballs
  refine ⟨{y | ∀ w : {w : InfinitePlace F // w.IsReal}, w.1 ∈ I →
        dist (y.1 w) (InfinitePlace.Completion.extensionEmbeddingOfIsReal w.2 (a w.1)) < ε w.1} ∩
      {y | ∀ w : {w : InfinitePlace F // w.IsComplex}, w.1 ∈ I →
        dist (y.2 w) (InfinitePlace.Completion.extensionEmbedding w.1 (a w.1)) < ε w.1},
    ?_, ?_, ?_⟩
  · refine IsOpen.inter ?_ ?_
    · rw [Set.setOf_forall]
      refine isOpen_iInter_of_finite fun w => ?_
      by_cases hw : w.1 ∈ I
      · simp only [hw, forall_const]
        exact isOpen_lt ((continuous_apply w).comp continuous_fst |>.dist continuous_const)
          continuous_const
      · simp [hw]
    · rw [Set.setOf_forall]
      refine isOpen_iInter_of_finite fun w => ?_
      by_cases hw : w.1 ∈ I
      · simp only [hw, forall_const]
        exact isOpen_lt ((continuous_apply w).comp continuous_snd |>.dist continuous_const)
          continuous_const
      · simp [hw]
  · refine ⟨InfiniteAdeleRing.ringEquiv_mixedSpace F a, ?_, ?_⟩
    · intro w hw
      rw [InfiniteAdeleRing.ringEquiv_mixedSpace_apply, dist_self]
      exact hε w.1 hw
    · intro w hw
      rw [InfiniteAdeleRing.ringEquiv_mixedSpace_apply, dist_self]
      exact hε w.1 hw
  · intro x hx
    refine hsub fun w hw => hεsub w hw ?_
    rw [Set.mem_preimage, InfiniteAdeleRing.ringEquiv_mixedSpace_apply] at hx
    obtain ⟨hx1, hx2⟩ := hx
    rw [Metric.mem_ball]
    rcases w.isReal_or_isComplex with hw' | hw'
    · have := hx1 ⟨w, hw'⟩ hw
      rwa [(InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hw').dist_eq] at this
    · have := hx2 ⟨w, hw'⟩ hw
      rwa [(InfinitePlace.Completion.isometry_extensionEmbedding w).dist_eq] at this

theorem lower_aux {K I e R Rlow M σ : ℝ} (hK : 0 < K) (hid : K⁻¹ * I * e = R) (he : 0 < e)
    (heM : e ≤ Real.exp M * (2 * σ - 1)) (hσ : 1 / 2 < σ) (hR : Rlow ≤ R) (hRlow : 0 ≤ Rlow) :
    K * Rlow * Real.exp (-M) / 2 ≤ (σ - 1 / 2) * I := by
  have hK0 : K ≠ 0 := hK.ne'
  have he0 : e ≠ 0 := he.ne'
  have h2 : 2 * σ - 1 ≠ 0 := by linarith
  have hI : I = K * R / e := by
    field_simp at hid ⊢
    linarith
  have hM : 0 < Real.exp M := Real.exp_pos M
  have h1 : K * Rlow * Real.exp (-M) / 2 = (σ - 1 / 2) * ((K * Rlow) / (Real.exp M * (2 * σ - 1))) := by
    rw [Real.exp_neg]
    field_simp
  rw [hI, h1]
  refine mul_le_mul_of_nonneg_left ?_ (by linarith)
  exact div_le_div₀ (mul_nonneg hK.le (hRlow.trans hR)) (by nlinarith) he heM

theorem upper_aux {K I e R Rhigh M σ : ℝ} (hK : 0 < K) (hid : K⁻¹ * I * e = R) (he : 0 < e)
    (heM : Real.exp (-M) * (2 * σ - 1) ≤ e) (hσ : 1 / 2 < σ) (hR : R ≤ Rhigh) (hR0 : 0 ≤ R) :
    (σ - 1 / 2) * I ≤ K * Rhigh * Real.exp M / 2 := by
  have hK0 : K ≠ 0 := hK.ne'
  have he0 : e ≠ 0 := he.ne'
  have h2 : 2 * σ - 1 ≠ 0 := by linarith
  have hI : I = K * R / e := by
    field_simp at hid ⊢
    linarith
  have hM : 0 < Real.exp (-M) := Real.exp_pos _
  have hM' : Real.exp (-M) ≠ 0 := hM.ne'
  have h1 : K * Rhigh * Real.exp M / 2 = (σ - 1 / 2) * ((K * Rhigh) / (Real.exp (-M) * (2 * σ - 1))) := by
    rw [Real.exp_neg] at hM' ⊢
    field_simp
  rw [hI, h1]
  refine mul_le_mul_of_nonneg_left ?_ (by linarith)
  have hRhigh : 0 ≤ Rhigh := hR0.trans hR
  exact div_le_div₀ (by positivity) (by nlinarith) (mul_pos hM (by linarith)) heM

theorem isOpen_cyl (S : Finset (HeightOneSpectrum (𝓞 F))) {V : Set (mixedEmbedding.mixedSpace F)}
    (hV : IsOpen V) {B : ∀ v : HeightOneSpectrum (𝓞 F), Set (v.adicCompletion F)}
    (hB : ∀ v ∈ S, IsOpen (B v)) : IsOpen (cyl F S V B) := by
  have h1 : IsOpen {x : AdeleRing (𝓞 F) F | InfiniteAdeleRing.ringEquiv_mixedSpace F x.1 ∈ V} :=
    hV.preimage ((continuous_ringEquiv_mixedSpace F).comp continuous_fst)
  have h2 : IsOpen {x : AdeleRing (𝓞 F) F | ∀ v ∈ S, x.2 v ∈ B v} := by
    have : {x : AdeleRing (𝓞 F) F | ∀ v ∈ S, x.2 v ∈ B v} = ⋂ v ∈ S, (fun x => x.2 v) ⁻¹' B v := by
      ext x; simp
    rw [this]
    exact isOpen_biInter_finset fun v hv =>
      (hB v hv).preimage ((continuous_finAdeleEval (𝓞 F) F v).comp continuous_snd)
  exact h1.inter h2

theorem cyl_empty_univ (B : ∀ v : HeightOneSpectrum (𝓞 F), Set (v.adicCompletion F)) :
    cyl F ∅ Set.univ B = Set.univ :=
  Set.eq_univ_of_forall fun _ => ⟨Set.mem_univ _, fun v hv => absurd hv (Finset.notMem_empty v)⟩

theorem total_identity (σ : ℝ) (hσ : 1 / 2 < σ) :
    ((μA F) (adelicBox F)).toReal⁻¹ * (∫ x, adelicHeight F (wn F x) ^ (σ + 1 / 2) ∂(μA F))
        * eulerR F ∅ (2 * σ)
      = archConst F * (∫ y, archF F σ y) * eulerR F ∅ (2 * σ + 1) := by
  have h := mass_identity F ∅ Set.univ (fun _ => Set.univ) σ hσ
  rw [cyl_empty_univ, Finset.prod_empty, one_mul] at h
  simp only [Set.indicator_univ] at h
  exact h

theorem integrable_rpow {σ : ℝ} (hσ : 1 / 2 < σ) :
    Integrable (fun x => adelicHeight F (wn F x) ^ (σ + 1 / 2)) (μA F) := by
  by_contra h
  have hid := total_identity F σ hσ
  rw [integral_undef h, mul_zero, zero_mul] at hid
  have : 0 < archConst F * (∫ y, archF F σ y) * eulerR F ∅ (2 * σ + 1) := by
    refine mul_pos (mul_pos (archConst_pos F) ?_) (eulerR_pos ∅ (by linarith))
    have := integral_indicator_archF_pos F (by linarith : 0 < σ) isOpen_univ Set.univ_nonempty
    simpa only [Set.indicator_univ] using this
  linarith

theorem tendsto_two_mul : Tendsto (fun σ : ℝ => 2 * σ) (𝓝[>] (1 / 2 : ℝ)) (𝓝[>] (1 : ℝ)) := by
  refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
  · have : Tendsto (fun σ : ℝ => 2 * σ) (𝓝 (1 / 2 : ℝ)) (𝓝 (2 * (1 / 2))) :=
      (continuous_const.mul continuous_id).tendsto _
    rw [show (2 : ℝ) * (1 / 2) = 1 by norm_num] at this
    exact this.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with σ hσ
    simp only [Set.mem_Ioi] at hσ ⊢
    linarith

theorem main (S₁ : Finset (HeightOneSpectrum (𝓞 F)))
    (U : ∀ v : HeightOneSpectrum (𝓞 F), Set (v.adicCompletion F))
    (hU : ∀ v ∈ S₁, IsOpen (U v) ∧ (U v).Nonempty)
    (U₀ : Set (InfiniteAdeleRing F)) (hU₀ : IsOpen U₀ ∧ U₀.Nonempty) :
    ∃ m₀ m₁ : ℝ, 0 < m₀ ∧
      ∀ᶠ σ : ℝ in 𝓝[>] (1 / 2 : ℝ),
        m₀ ≤ (σ - 1 / 2) *
            ∫ x in {x : AdeleRing (𝓞 F) F | x.1 ∈ U₀ ∧ ∀ v ∈ S₁, x.2 v ∈ U v},
              adelicHeight F (wn F x) ^ (σ + 1 / 2) ∂(μA F) ∧
        (σ - 1 / 2) * ∫ x, adelicHeight F (wn F x) ^ (σ + 1 / 2) ∂(μA F) ≤ m₁ := by

  obtain ⟨V, hVo, hVne, hVsub⟩ := exists_open_mixedSpace F U₀ hU₀
  have hB : ∀ v ∈ S₁, ∃ a : v.adicCompletion F, ∃ r : ℝ, 0 < r ∧ Metric.ball a r ⊆ U v := by
    intro v hv
    obtain ⟨a, ha⟩ := (hU v hv).2
    obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.mp (hU v hv).1 a ha
    exact ⟨a, r, hr, hsub⟩
  choose! a r hr hrsub using hB

  obtain ⟨M₁, hM₁⟩ := eulerR_bounds_nhds_one (F := F) S₁
  obtain ⟨M₀, hM₀⟩ := eulerR_bounds_nhds_one (F := F) ∅
  obtain ⟨Q, hQ⟩ : ∃ Q : ℝ, Q = ∑' v, NumberField.PrimeNormSum.pw F 2 v := ⟨_, rfl⟩
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = ((μA F) (adelicBox F)).toReal := ⟨_, rfl⟩
  have hKpos : 0 < K := by
    rw [hK]
    exact ENNReal.toReal_pos (measure_adelicBox_pos F _).ne' (measure_adelicBox_lt_top F _).ne
  obtain ⟨A₁, hA₁⟩ : ∃ A₁ : ℝ, A₁ = ∫ y, V.indicator (archF F 1) y := ⟨_, rfl⟩
  have hA₁pos : 0 < A₁ := hA₁ ▸ integral_indicator_archF_pos F one_pos hVo hVne
  obtain ⟨Ah, hAh⟩ : ∃ Ah : ℝ, Ah = ∫ y, archF F (1 / 2) y := ⟨_, rfl⟩
  have hAh0 : 0 ≤ Ah := hAh ▸ integral_nonneg fun y => (archF_pos F _ y).le
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : ℝ, ℓ = ∏ v ∈ S₁,
      ((μv F v).real (v.adicCompletionIntegers F : Set (v.adicCompletion F)))⁻¹
        * ((μv F v).real (Metric.ball (a v) (r v)) * (max 1 (‖a v‖ + r v)) ^ (-(3 : ℝ))) := ⟨_, rfl⟩
  have hℓpos : 0 < ℓ := hℓ ▸ Finset.prod_pos fun v hv =>
    mul_pos (inv_pos.mpr (measureReal_integers_pos v))
      (mul_pos (measureReal_ball_pos v (a v) (hr v hv)) (by positivity))
  have hc := archConst_pos F
  refine ⟨K * (archConst F * A₁ * (ℓ * Real.exp (-(3 * Q)))) * Real.exp (-M₁) / 2,
    K * (archConst F * Ah * 1) * Real.exp M₀ / 2,
    div_pos (mul_pos (mul_pos hKpos (mul_pos (mul_pos hc hA₁pos) (mul_pos hℓpos (Real.exp_pos _))))
      (Real.exp_pos _)) two_pos, ?_⟩
  filter_upwards [Ioc_mem_nhdsGT (by norm_num : (1 / 2 : ℝ) < 1), tendsto_two_mul.eventually hM₁,
    tendsto_two_mul.eventually hM₀] with σ hσI hE₁ hE₀
  obtain ⟨hσ, hσ1⟩ := hσI
  have h2σ : (1 : ℝ) < 2 * σ := by linarith
  have hint := integrable_rpow F hσ
  constructor
  ·
    have hid := mass_identity F S₁ V (fun v => Metric.ball (a v) (r v)) σ hσ
    rw [← hK] at hid
    have hcylsub : cyl F S₁ V (fun v => Metric.ball (a v) (r v))
        ⊆ {x : AdeleRing (𝓞 F) F | x.1 ∈ U₀ ∧ ∀ v ∈ S₁, x.2 v ∈ U v} :=
      fun x hx => ⟨hVsub hx.1, fun v hv => hrsub v hv (hx.2 v hv)⟩
    have hmeas : MeasurableSet (cyl F S₁ V fun v => Metric.ball (a v) (r v)) :=
      (isOpen_cyl F S₁ hVo fun v _ => Metric.isOpen_ball).measurableSet
    rw [integral_indicator hmeas] at hid
    have hmono : ∫ x in cyl F S₁ V (fun v => Metric.ball (a v) (r v)),
          adelicHeight F (wn F x) ^ (σ + 1 / 2) ∂(μA F)
        ≤ ∫ x in {x : AdeleRing (𝓞 F) F | x.1 ∈ U₀ ∧ ∀ v ∈ S₁, x.2 v ∈ U v},
            adelicHeight F (wn F x) ^ (σ + 1 / 2) ∂(μA F) :=
      setIntegral_mono_set hint.integrableOn
        (ae_of_all _ fun x => Real.rpow_nonneg (adelicHeight_pos _).le _)
        (ae_of_all _ hcylsub)
    refine le_trans ?_ (mul_le_mul_of_nonneg_left hmono (by linarith))
    refine lower_aux hKpos hid (eulerR_pos S₁ h2σ) hE₁.2 hσ ?_ ?_
    ·
      refine mul_le_mul ?_ ?_ (mul_nonneg hℓpos.le (Real.exp_pos _).le)
        (mul_nonneg hc.le (integral_nonneg (indicator_archF_nonneg F σ V)))
      · refine mul_le_mul_of_nonneg_left ?_ (archConst_pos F).le
        rw [hA₁]
        exact integral_indicator_archF_mono F (by linarith) hσ1 hVo.measurableSet
      · rw [hℓ, hQ]
        refine mul_le_mul ?_ (eulerR_bounds_of_two_le S₁ (by linarith)).1 (by positivity) ?_
        · refine Finset.prod_le_prod (fun v hv => ?_) fun v hv => ?_
          · have := measureReal_integers_pos (F := F) v
            positivity
          · exact mul_le_mul_of_nonneg_left (local_factor_ge F hσ hσ1 v (a v) (r v))
              (inv_pos.mpr (measureReal_integers_pos v)).le
        · refine Finset.prod_nonneg fun v hv => mul_nonneg (inv_pos.mpr (measureReal_integers_pos v)).le
            (integral_nonneg fun y => Set.indicator_nonneg (fun y _ => (finF_pos F σ v y).le) y)
    · have := archConst_pos F
      positivity
  ·
    have hid := total_identity F σ hσ
    rw [← hK] at hid
    refine upper_aux hKpos hid (eulerR_pos ∅ h2σ) hE₀.1 hσ ?_ ?_
    · refine mul_le_mul ?_ (eulerR_bounds_of_two_le ∅ (by linarith)).2 (eulerR_pos ∅ (by linarith)).le
        (by positivity)
      refine mul_le_mul_of_nonneg_left ?_ (archConst_pos F).le
      have := integral_indicator_archF_mono F (by norm_num : (0 : ℝ) < 1 / 2) hσ.le MeasurableSet.univ
      rw [hAh]
      simpa only [Set.indicator_univ] using this
    · have := archConst_pos F
      have := eulerR_pos (F := F) ∅ (by linarith : (1 : ℝ) < 2 * σ + 1)
      have : 0 ≤ ∫ y, archF F σ y := integral_nonneg fun y => (archF_pos F σ y).le
      positivity

end P2mMass
p2m_reactivate "P2MW.S_AutomorphicForm_exists_pos_eventually_le_sub_one_half_mul_setIntegral_adelicHeight_weyl_unipotent_rpow.P2mMass"

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicHeight IsDedekindDomain AutomorphicForm Filter Topology in

theorem solution
    (F : Type) [Field F] [NumberField F]
    (S₁ : Finset (HeightOneSpectrum (𝓞 F)))
    (U : ∀ v : HeightOneSpectrum (𝓞 F), Set (v.adicCompletion F))
    (hU : ∀ v ∈ S₁, IsOpen (U v) ∧ (U v).Nonempty)
    (U₀ : Set (InfiniteAdeleRing F)) (hU₀ : IsOpen U₀ ∧ U₀.Nonempty) :
    letI := adeleBorel (𝓞 F) F
    ∃ m₀ m₁ : ℝ, 0 < m₀ ∧
      ∀ᶠ σ : ℝ in 𝓝[>] (1 / 2 : ℝ),
        m₀ ≤ (σ - 1 / 2) *
            ∫ x in {x : AdeleRing (𝓞 F) F | x.1 ∈ U₀ ∧ ∀ v ∈ S₁, x.2 v ∈ U v},
              adelicHeight F ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 x) ^ (σ + 1 / 2) ∂(adelicAddHaar (𝓞 F) F) ∧
        (σ - 1 / 2) *
            ∫ x, adelicHeight F ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 x) ^ (σ + 1 / 2) ∂(adelicAddHaar (𝓞 F) F) ≤ m₁ :=
  P2mMass.main F S₁ U hU U₀ hU₀

end S_AutomorphicForm_exists_pos_eventually_le_sub_one_half_mul_setIntegral_adelicHeight_weyl_unipotent_rpow
end P2MW
export P2MW.S_AutomorphicForm_exists_pos_eventually_le_sub_one_half_mul_setIntegral_adelicHeight_weyl_unipotent_rpow (solution)
