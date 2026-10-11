-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0260_parallel1
-- name    : PNT_ZeroFree_433_0260_parallel1
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T10:42:51.641975+00:00
-- url     : https://prove2.me/theorems/31c59c15-8260-45cb-af1d-12e9a5d41f1f
-- title:
--   Zero-free region foundations: Eisenstein.SourceMellinInversion [0260_parallel1]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.Eisenstein.SourceMellinInversion
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Eisenstein/SourceMellinInversion.lean#L133-L639

import Definitions.Def_PNT_ZeroFree_433_0004
import Definitions.Def_PNT_ZeroFree_433_0007
import Definitions.Def_PNT_ZeroFree_433_0009
import Definitions.Def_PNT_ZeroFree_433_0031
import Definitions.Def_PNT_ZeroFree_433_0041
import Definitions.Def_PNT_ZeroFree_433_0048
import Definitions.Def_PNT_ZeroFree_433_0049
import Definitions.Def_PNT_ZeroFree_433_0053
import Definitions.Def_PNT_ZeroFree_433_0057
import Definitions.Def_PNT_ZeroFree_433_0079_1
import Definitions.Def_PNT_ZeroFree_433_0167
import Definitions.Def_PNT_ZeroFree_433_0327
import Definitions.Def_PNT_ZeroFree_433_0505

/- Supporting zero-free-region lemmas, grouped by independent dependencies.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Eisenstein/SourceMellinInversion.lean
-/
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

section
namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical


namespace CompletedGauss

section
open Filter MeasureTheory
open scoped Classical BigOperators Topology FourierTransform SchwartzMap ContDiff

lemma compactMellin_vertical_integrable (V : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hsupp : Function.support V⊆Set.Icc a b) (hV : ContDiff ℝ ∞ V) (σ : ℝ) :
    Complex.VerticalIntegrable (mellin V) σ := by
  have hc : HasCompactSupport (CubicReflectionKernel.mellinLogFamily V σ) :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc
      (CubicReflectionKernel.mellinLogFamily_support V a b ha hsupp σ)
  have hd : ContDiff ℝ ∞ (CubicReflectionKernel.mellinLogFamily V σ) :=
    (CubicReflectionKernel.mellinLogFamily_smooth V hV).comp (contDiff_const.prodMk contDiff_id)
  let f : 𝓢(ℝ,ℂ) := hc.toSchwartzMap hd
  have hf : Integrable (fun t : ℝ=>(𝓕 f) (t/(2*Real.pi))) := by
    simpa only [div_eq_mul_inv] using
      (𝓕 f).integrable.comp_mul_right' (inv_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero))
  change Integrable (fun t : ℝ=>mellin V ((σ:ℂ)+t*Complex.I))
  have hfcoe : (f:ℝ→ℂ)=CubicReflectionKernel.mellinLogFamily V σ := rfl
  simpa only [CubicReflectionKernel.mellin_eq_logFamily_fourier,
    SchwartzMap.fourier_coe,hfcoe] using hf

theorem compactMellin_inversion (V : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hsupp : Function.support V⊆Set.Icc a b) (hV : ContDiff ℝ ∞ V)
    (σ x : ℝ) (hx : 0<x) :
    V x=(1/(2*Real.pi):ℂ)*∫t : ℝ,
      (x:ℂ)^(-((σ:ℂ)+t*Complex.I))*mellin V ((σ:ℂ)+t*Complex.I) := by
  have hm := mellinInv_mellin_eq σ V hx
    (CubicReflectionKernel.compact_source_mellin_convergent V a b ha hsupp hV σ)
    (compactMellin_vertical_integrable V a b ha hsupp hV σ) hV.continuous.continuousAt
  simpa only [mellinInv,smul_eq_mul,Complex.real_smul,Complex.ofReal_div,
    Complex.ofReal_one,Complex.ofReal_mul,Complex.ofReal_ofNat] using hm.symm

end

open Filter MeasureTheory
open scoped Classical BigOperators Topology ContDiff

lemma positive_cpow_vertical_norm (r σ t : ℝ) (hr : 0<r) :
    ‖(r:ℂ)^((σ:ℂ)+t*Complex.I)‖=r^σ := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hr]
  simp

lemma positive_cpow_negative_vertical_norm (r σ t : ℝ) (hr : 0<r) :
    ‖(r:ℂ)^(-((σ:ℂ)+t*Complex.I))‖=r^(-σ) := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hr]
  simp

lemma positive_cpow_vertical_continuous (r σ : ℝ) (hr : 0<r) :
    Continuous (fun t : ℝ=>(r:ℂ)^((σ:ℂ)+t*Complex.I)) := by
  let : NeZero (r:ℂ) := ⟨Complex.ofReal_ne_zero.mpr hr.ne'⟩
  exact (_root_.continuous_const_cpow (r:ℂ)).comp (by fun_prop)

lemma positive_cpow_negative_vertical_continuous (r σ : ℝ) (hr : 0<r) :
    Continuous (fun t : ℝ=>(r:ℂ)^(-((σ:ℂ)+t*Complex.I))) := by
  let : NeZero (r:ℂ) := ⟨Complex.ofReal_ne_zero.mpr hr.ne'⟩
  exact (_root_.continuous_const_cpow (r:ℂ)).comp (by fun_prop)

lemma vertical_power_mul_integrable (M : ℝ→ℂ) (hM : Integrable M)
    (r σ : ℝ) (hr : 0<r) :
    Integrable (fun t : ℝ=>(r:ℂ)^((σ:ℂ)+t*Complex.I)*M t) := by
  apply (hM.norm.const_mul (r^σ)).mono'
    ((positive_cpow_vertical_continuous r σ hr).aestronglyMeasurable.mul hM.aestronglyMeasurable)
  exact Filter.Eventually.of_forall (fun t=>by simp only [Pi.mul_apply,norm_mul,positive_cpow_vertical_norm r σ t hr,le_refl])

lemma weighted_vertical_power_integrable (M : ℝ→ℂ) (hM : Integrable M)
    (r σ : ℝ) (hr : 0<r) (c : ℂ) :
    Integrable (fun t : ℝ=>c*(r:ℂ)^(-((σ:ℂ)+t*Complex.I))*M t) := by
  apply (hM.norm.const_mul (‖c‖*r^(-σ))).mono'
    ((continuous_const.mul (positive_cpow_negative_vertical_continuous r σ hr)).aestronglyMeasurable.mul hM.aestronglyMeasurable)
  exact Filter.Eventually.of_forall (fun t=>by
    simp only [Pi.mul_apply,norm_mul,positive_cpow_negative_vertical_norm r σ t hr,le_refl])

lemma weighted_vertical_power_integral_norm (M : ℝ→ℂ) (r σ : ℝ) (hr : 0<r) (c : ℂ) :
    (∫t : ℝ,‖c*(r:ℂ)^(-((σ:ℂ)+t*Complex.I))*M t‖)=
      (‖c‖*r^(-σ))*(∫t : ℝ,‖M t‖) := by
  simp only [norm_mul,positive_cpow_negative_vertical_norm r σ _ hr,integral_const_mul]

theorem weighted_vertical_sum_integral {α : Type*} [Countable α]
    (r : α→ℝ) (hr : ∀i,0<r i) (c : α→ℂ) (σ : ℝ)
    (hc : Summable (fun i=>‖c i‖*(r i)^(-σ)))
    (M : ℝ→ℂ) (hM : Integrable M) :
    (∑' i,∫t : ℝ,c i*(r i:ℂ)^(-((σ:ℂ)+t*Complex.I))*M t)=
      ∫t : ℝ,(∑' i,c i*(r i:ℂ)^(-((σ:ℂ)+t*Complex.I)))*M t := by
  have hi (i : α) := weighted_vertical_power_integrable M hM (r i) σ (hr i) (c i)
  have hs : Summable (fun i=>∫t : ℝ,‖c i*(r i:ℂ)^(-((σ:ℂ)+t*Complex.I))*M t‖) := by
    simp only [weighted_vertical_power_integral_norm M _ σ (hr _) _]
    exact hc.mul_right _
  rw [integral_tsum_of_summable_integral_norm hi hs]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun t=>tsum_mul_right)

lemma positive_quotient_cpow_neg (r X : ℝ) (hr : 0<r) (hX : 0<X) (s : ℂ) :
    ((r/X:ℝ):ℂ)^(-s)=(r:ℂ)^(-s)*(X:ℂ)^s := by
  rw [Complex.ofReal_div,Complex.div_cpow_ofReal_nonneg hr.le hX.le,
    Complex.cpow_neg,Complex.cpow_neg,div_inv_eq_mul]

theorem weightedMellin_inversion {α : Type*} [Countable α]
    (r : α→ℝ) (hr : ∀i,0<r i) (c : α→ℂ) (σ : ℝ)
    (hc : Summable (fun i=>‖c i‖*(r i)^(-σ)))
    (V : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hsupp : Function.support V⊆Set.Icc a b) (hV : ContDiff ℝ ∞ V)
    (X : ℝ) (hX : 0<X) :
    (∑'i,c i*V (r i/X))=(1/(2*Real.pi):ℂ)*∫t : ℝ,
      mellin V ((σ:ℂ)+t*Complex.I)*(X:ℂ)^((σ:ℂ)+t*Complex.I)*
        (∑'i,c i*(r i:ℂ)^(-((σ:ℂ)+t*Complex.I))) := by
  let M : ℝ→ℂ := fun t=>(X:ℂ)^((σ:ℂ)+t*Complex.I)*mellin V ((σ:ℂ)+t*Complex.I)
  have hM : Integrable M := vertical_power_mul_integrable _
    (compactMellin_vertical_integrable V a b ha hsupp hV σ) X σ hX
  have hi (i : α) : c i*V (r i/X)=(1/(2*Real.pi):ℂ)*
      ∫t : ℝ,c i*(r i:ℂ)^(-((σ:ℂ)+t*Complex.I))*M t := by
    rw [compactMellin_inversion V a b ha hsupp hV σ _ (div_pos (hr i) hX)]
    rw [←mul_assoc,mul_comm (c i),mul_assoc,←integral_const_mul]
    congr 1
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun t=>by
      dsimp only
      rw [positive_quotient_cpow_neg _ _ (hr i) hX]
      dsimp only [M]
      ring)
  simp_rw [hi]
  rw [tsum_mul_left,weighted_vertical_sum_integral r hr c σ hc M hM]
  congr 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun t=>by dsimp only [M];ring)

end CompletedGauss

open Filter MeasureTheory
open scoped Classical BigOperators Topology

namespace CompletedGauss

section
open ActualEisensteinCubic ConcreteTraceCRT
local notation "O" => ActualEisensteinCubic.O

lemma angularFactor_norm_le_one (a : ActualEisensteinCubic.O) : ‖FiniteGaussPhase.angularFactor a‖≤1 := by
  by_cases ha : a=0
  · subst a; simp [FiniteGaussPhase.angularFactor]
  · exact (FiniteGaussPhase.norm_angularFactor a ha).le

lemma cubicRow_norm_le_one (I : Ideal ActualEisensteinCubic.O) (hI : primaryGenerator I≠0) (x : ActualEisensteinCubic.O⧸I) :
    ‖cubicRow I hI x‖≤1 := by
  unfold cubicRow
  rw [norm_prod]
  apply Finset.prod_le_one
  · intro i hi; exact norm_nonneg _
  · intro i hi
    exact FiniteRayExpansion.norm_char_le_one _ _

lemma gaussTwo_norm_le_sqrt (I : Ideal ActualEisensteinCubic.O) (hI : primaryGenerator I≠0) :
    ‖gaussTwo I hI‖≤Real.sqrt (Ideal.absNorm I:ℝ) := by
  let n := primaryGenerator I
  let : Finite (ActualEisensteinCubic.O⧸Ideal.span {n}) := finite_quotient_span hI
  let : Fintype (ActualEisensteinCubic.O⧸Ideal.span {n}) := Fintype.ofFinite _
  let e := Ideal.quotEquivOfEq (primaryGenerator_spec I hI).1
  let ψ := eisTraceModChar ShortDraftTrace.breveE ConcreteBreveE.breveE_period_coordinates n hI
  have hN : 0<(Ideal.absNorm I:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (fun h=>primaryGenerator_ne_zero_ideal I hI (Ideal.absNorm_eq_zero_iff.mp h))
  have hn : ‖eisEmbedding n‖=Real.sqrt (Ideal.absNorm I:ℝ) := primaryGenerator_norm I hI
  have hsum : ‖∑x : ActualEisensteinCubic.O⧸Ideal.span {n},cubicRow I hI (e x)*ψ x‖≤(Ideal.absNorm I:ℝ) := by
    calc
      _≤∑x : ActualEisensteinCubic.O⧸Ideal.span {n},‖cubicRow I hI (e x)*ψ x‖ := norm_sum_le _ _
      _≤∑_x : ActualEisensteinCubic.O⧸Ideal.span {n},(1:ℝ) := by
        apply Finset.sum_le_sum
        intro x hx
        rw [norm_mul,AddChar.norm_apply,mul_one]
        exact cubicRow_norm_le_one I hI (e x)
      _=(Ideal.absNorm I:ℝ) := by
        simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one]
        congr 1
        rw [←Nat.card_eq_fintype_card,←Submodule.cardQuot_apply,←Ideal.absNorm_apply,
          (primaryGenerator_spec I hI).1]
  change ‖(∑x : ActualEisensteinCubic.O⧸Ideal.span {n},cubicRow I hI (e x)*ψ x)/(‖eisEmbedding n‖:ℂ)‖≤_
  rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _),hn]
  apply (div_le_iff₀ (Real.sqrt_pos.mpr hN)).mpr
  simpa only [Real.mul_self_sqrt hN.le] using hsum

lemma columnWeight_div_sqrt_norm_le_one (Ψ : ActualEisensteinCubic.O→*ℂ) (hΨ : ∀a,‖Ψ a‖≤1) (I : Ideal ActualEisensteinCubic.O) :
    ‖columnWeight Ψ I/(Real.sqrt (Ideal.absNorm I:ℝ):ℂ)‖≤1 := by
  by_cases hI : Squarefree I ∧ primaryGenerator I≠0
  · have hN : 0<(Ideal.absNorm I:ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (fun h=>primaryGenerator_ne_zero_ideal I hI.2 (Ideal.absNorm_eq_zero_iff.mp h))
    rw [columnWeight_eq Ψ I hI.1 hI.2,norm_div,norm_mul,norm_mul,norm_star,
      FiniteGaussPhase.norm_angularFactor _ hI.2,one_mul,
      Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)]
    apply (div_le_one (Real.sqrt_pos.mpr hN)).mpr
    exact (mul_le_of_le_one_right (norm_nonneg _) (hΨ _)).trans (gaussTwo_norm_le_sqrt I hI.2)
  · simp only [columnWeight,squarefreeGaussCoefficient,dif_neg hI,zero_mul,zero_div,norm_zero,zero_le_one]

lemma cubeWeight_norm_le_one (Ψ : ActualEisensteinCubic.O→*ℂ) (hΨ : ∀a,‖Ψ a‖≤1) (I : Ideal ActualEisensteinCubic.O) :
    ‖cubeWeight Ψ I‖≤1 := by
  by_cases hI : I=0
  · subst I; simp
  have hN : (1:ℝ)≤(Ideal.absNorm I:ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (fun h=>hI (Ideal.absNorm_eq_zero_iff.mp h))
  have hn : 0<(Ideal.absNorm I:ℝ) := lt_of_lt_of_le zero_lt_one hN
  change ‖star (FiniteGaussPhase.angularFactor (primaryGenerator I))^3*
    Ψ (primaryGenerator I)^3/(Ideal.absNorm I:ℂ)‖≤1
  rw [norm_div,norm_mul,norm_pow,norm_star,norm_pow,Complex.norm_natCast]
  apply (div_le_one hn).mpr
  apply le_trans _ hN
  calc
    _≤(1:ℝ)*1 := mul_le_mul
      (pow_le_one₀ (norm_nonneg _) (angularFactor_norm_le_one _))
      (pow_le_one₀ (norm_nonneg _) (hΨ _)) (pow_nonneg (norm_nonneg _) _) zero_le_one
    _=1 := one_mul _

end

open Filter MeasureTheory
open scoped Classical BigOperators Topology ContDiff


section
open ActualEisensteinCubic CubicEisenstein
local notation "O" => ActualEisensteinCubic.O

lemma nat_sqrt_cpow_half (a : ℕ) :
    (Real.sqrt (a:ℝ):ℂ)=(a:ℂ)^(1/2:ℂ) := by
  simpa only [Real.sqrt_eq_rpow,Complex.ofReal_natCast,Complex.ofReal_div,
    Complex.ofReal_one,Complex.ofReal_ofNat] using
    (Complex.ofReal_cpow (Nat.cast_nonneg a) (1/2:ℝ))

lemma nat_half_shift_product (a b : ℕ) (ha : a≠0) (hb : b≠0) (C D s : ℂ) :
    (C/(Real.sqrt (a:ℝ):ℂ)*(D/(b:ℂ)))*((a:ℂ)*(b:ℂ)^3)^(1/2-s)=
      C*D*(b:ℂ)^(1/2-3*s)*(a:ℂ)^(-s) := by
  have ha0 : (a:ℂ)≠0 := Nat.cast_ne_zero.mpr ha
  have hb0 : (b:ℂ)≠0 := Nat.cast_ne_zero.mpr hb
  have hhalf : (a:ℂ)^(1/2:ℂ)≠0 := (Complex.cpow_ne_zero_iff).mpr (Or.inl ha0)
  rw [nat_sqrt_cpow_half]
  have hmul : ((a:ℂ)*(b:ℂ)^3)^(1/2-s)=
      (a:ℂ)^(1/2-s)*(b:ℂ)^(3*(1/2-s)) := by
    rw [←Nat.cast_pow,Complex.natCast_mul_natCast_cpow,Nat.cast_pow,
      ←Complex.natCast_cpow_natCast_mul]
    norm_num
  rw [hmul]
  have hA : (a:ℂ)^(1/2-s)=(a:ℂ)^(1/2:ℂ)*(a:ℂ)^(-s) := by
    rw [sub_eq_add_neg,Complex.cpow_add _ _ ha0]
  have hB : (b:ℂ)^(3*(1/2-s))=(b:ℂ)*(b:ℂ)^(1/2-3*s) := by
    rw [show (3:ℂ)*(1/2-s)=1+(1/2-3*s) by ring,
      Complex.cpow_add _ _ hb0,Complex.cpow_one]
  rw [hA,hB]
  field_simp


end

open ActualEisensteinCubic
local notation "O" => ActualEisensteinCubic.O

lemma weighted_vertical_series_continuous {α : Type*}
    (r : α→ℝ) (hr : ∀i,0<r i) (c : α→ℂ) (σ : ℝ)
    (hc : Summable (fun i=>‖c i‖*(r i)^(-σ))) :
    Continuous (fun t : ℝ=>∑'i,c i*(r i:ℂ)^(-((σ:ℂ)+t*Complex.I))) := by
  apply continuous_tsum
    (fun i=>continuous_const.mul (positive_cpow_negative_vertical_continuous (r i) σ (hr i))) hc
  intro i t
  change ‖c i*(r i:ℂ)^(-((σ:ℂ)+t*Complex.I))‖≤‖c i‖*(r i)^(-σ)
  rw [norm_mul,positive_cpow_negative_vertical_norm _ _ _ (hr i)]

lemma weighted_vertical_series_norm {α : Type*}
    (r : α→ℝ) (hr : ∀i,0<r i) (c : α→ℂ) (σ : ℝ)
    (hc : Summable (fun i=>‖c i‖*(r i)^(-σ))) (t : ℝ) :
    ‖∑'i,c i*(r i:ℂ)^(-((σ:ℂ)+t*Complex.I))‖≤∑'i,‖c i‖*(r i)^(-σ) := by
  have he (i : α) : ‖c i*(r i:ℂ)^(-((σ:ℂ)+t*Complex.I))‖=‖c i‖*(r i)^(-σ) := by
    rw [norm_mul,positive_cpow_negative_vertical_norm _ _ _ (hr i)]
  simpa only [he] using norm_tsum_le_tsum_norm (hc.congr (fun i=>(he i).symm))


end CompletedGauss

open scoped BigOperators Classical
open Finset AddChar MulChar EisensteinEmbedding

namespace CompletedGauss
local notation "Eis" => ActualEisensteinCubic.O

def dualIdealDyad (j : ℕ) : Finset (Ideal Eis) :=
  (ConcretePrimeRowBridge.idealsUpTo (2^j)).filter
    (fun I => Nat.clog 2 (Ideal.absNorm I)=j)

lemma mem_dualIdealDyad (I : Ideal Eis) (j : ℕ) :
    I∈dualIdealDyad j ↔ I≠0 ∧ Nat.clog 2 (Ideal.absNorm I)=j := by
  simp only [dualIdealDyad,Finset.mem_filter,ConcretePrimeRowBridge.mem_idealsUpTo]
  constructor
  · rintro ⟨⟨hI,_⟩,hj⟩
    exact ⟨fun h => by simp [h] at hI, hj⟩
  · rintro ⟨hI,hj⟩
    refine ⟨⟨Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI),?_⟩,hj⟩
    simpa only [hj] using Nat.le_pow_clog (by norm_num : 1<2) (Ideal.absNorm I)


abbrev NonzeroDualIdeal := {I : Ideal Eis // I≠0}

def dualDyadicIndexEquiv :
    (ℕ×NonzeroDualIdeal×NonzeroDualIdeal) ≃
      (Σ i : ℕ×ℕ×ℕ, (dualIdealDyad i.2.2)×(dualIdealDyad i.2.1)) where
  toFun x := ⟨(x.1,Nat.clog 2 (Ideal.absNorm x.2.2.val),Nat.clog 2 (Ideal.absNorm x.2.1.val)),
    ⟨⟨x.2.1.val,(mem_dualIdealDyad _ _).mpr ⟨x.2.1.property,rfl⟩⟩,
      ⟨x.2.2.val,(mem_dualIdealDyad _ _).mpr ⟨x.2.2.property,rfl⟩⟩⟩⟩
  invFun x := ⟨x.1.1,⟨x.2.1.val,((mem_dualIdealDyad _ _).mp x.2.1.property).1⟩,
    ⟨x.2.2.val,((mem_dualIdealDyad _ _).mp x.2.2.property).1⟩⟩
  left_inv x := by cases x; rfl
  right_inv x := by
    rcases x with ⟨⟨m,j,k⟩,⟨⟨I,hI⟩,⟨J,hJ⟩⟩⟩
    have hi:=((mem_dualIdealDyad I k).mp hI).2
    have hj:=((mem_dualIdealDyad J j).mp hJ).2
    dsimp only
    subst k
    subst j
    rfl

theorem tsum_dualIdealDyads
    (f : ℕ×NonzeroDualIdeal×NonzeroDualIdeal → ℂ) (hf : Summable f) :
    (∑'x, f x) = ∑'i : ℕ×ℕ×ℕ,
      ∑n : dualIdealDyad i.2.2, ∑b : dualIdealDyad i.2.1,
        f (i.1,⟨n.val,((mem_dualIdealDyad _ _).mp n.property).1⟩,
          ⟨b.val,((mem_dualIdealDyad _ _).mp b.property).1⟩) := by
  let g := f ∘ dualDyadicIndexEquiv.symm
  have hg : Summable g := dualDyadicIndexEquiv.symm.summable_iff.mpr hf
  calc
    _ = ∑'x,g x := (dualDyadicIndexEquiv.symm.tsum_eq f).symm
    _ = ∑'i,∑'x,g ⟨i,x⟩ := Summable.tsum_sigma' (fun _=>hasSum_fintype _ |>.summable) hg
    _ = _ := by
      apply tsum_congr
      intro i
      rw [tsum_fintype,Fintype.sum_prod_type]
      rfl

end CompletedGauss

end

end OAI

end


