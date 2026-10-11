-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0126_parallel1
-- name    : PNT_ZeroFree_433_0126_parallel1
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T11:13:46.736981+00:00
-- url     : https://prove2.me/theorems/f5125fa2-0e72-4d50-a0f7-e09fec265a4e
-- title:
--   Zero-free region foundations: QuadraticSieve.CuspCoercivity [0126_parallel1]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.QuadraticSieve.CuspCoercivity
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/QuadraticSieve/CuspCoercivity.lean#L166-L558

import Definitions.Def_PNT_ZeroFree_433_0007
import Definitions.Def_PNT_ZeroFree_433_0009
import Definitions.Def_PNT_ZeroFree_433_0048
import Definitions.Def_PNT_ZeroFree_433_0064
import Definitions.Def_PNT_ZeroFree_433_0072
import Definitions.Def_PNT_ZeroFree_433_0089
import Definitions.Def_PNT_ZeroFree_433_0091
import Definitions.Def_PNT_ZeroFree_433_0131_parallel1
import Definitions.Def_PNT_ZeroFree_433_0142_parallel1
import Definitions.Def_PNT_ZeroFree_433_0144_parallel1
import Definitions.Def_PNT_ZeroFree_433_0185_parallel1
import Definitions.Def_PNT_ZeroFree_433_0192_parallel1
import Definitions.Def_PNT_ZeroFree_433_0215_parallel1
import Definitions.Def_PNT_ZeroFree_433_0217_parallel1
import Definitions.Def_PNT_ZeroFree_433_0221_parallel1
import Definitions.Def_PNT_ZeroFree_433_0225_parallel1
import Definitions.Def_PNT_ZeroFree_433_0231_parallel1

/- Supporting zero-free-region lemmas, grouped by independent dependencies.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/QuadraticSieve/CuspCoercivity.lean
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

open scoped BigOperators Classical


open Filter MeasureTheory
open scoped BigOperators Classical Topology InnerProductSpace

namespace CubicEisenstein

section

lemma cusp_hardy_square_identity (u du : ℂ) (v : ℝ) (hv : v≠0) :
    ‖du‖^2/v-‖u‖^2/v^3=
      ‖du-v⁻¹ • u‖^2/v+
        (2*⟪u,du⟫_ℝ/v^2-2*‖u‖^2/v^3) := by
  rw [norm_sub_sq_real,real_inner_smul_right,norm_smul,Real.norm_eq_abs,
    mul_pow,sq_abs,real_inner_comm du u]
  field_simp
  ; ring

lemma cusp_hardy_boundary_hasDerivAt (f : ℝ → ℂ) (v : ℝ)
    (hf : DifferentiableAt ℝ f v) (hv : v≠0) :
    HasDerivAt (fun t => ‖f t‖^2/t^2)
      (2*⟪f v,deriv f v⟫_ℝ/v^2-2*‖f v‖^2/v^3) v := by
  convert! hf.hasDerivAt.norm_sq.div ((hasDerivAt_id v).pow 2) (pow_ne_zero 2 hv) using 1
  all_goals dsimp
  all_goals field_simp
  all_goals ring

theorem cusp_hardy_interval_identity (f : ℝ → ℂ) (a b : ℝ)
    (ha : 0<a) (hab : a≤b)
    (hf : ∀t∈Set.Icc a b,DifferentiableAt ℝ f t)
    (hdf : ContinuousOn (deriv f) (Set.Icc a b)) :
    (∫t in a..b,‖deriv f t‖^2/t)-(∫t in a..b,‖f t‖^2/t^3)=
      (∫t in a..b,‖deriv f t-t⁻¹ • f t‖^2/t)+
        (‖f b‖^2/b^2-‖f a‖^2/a^2) := by
  have hfC : ContinuousOn f (Set.Icc a b) :=
    fun t ht => (hf t ht).continuousAt.continuousWithinAt
  have hn : ∀t∈Set.Icc a b,t≠0 := fun t ht => (ha.trans_le ht.1).ne'
  have hiE : IntervalIntegrable (fun t => ‖deriv f t‖^2/t) volume a b :=
    ((hdf.norm.pow 2).div continuousOn_id hn).intervalIntegrable_of_Icc hab
  have hiM : IntervalIntegrable (fun t => ‖f t‖^2/t^3) volume a b :=
    ((hfC.norm.pow 2).div (continuousOn_id.pow 3) (fun t ht => pow_ne_zero 3 (hn t ht))).intervalIntegrable_of_Icc hab
  have hiS : IntervalIntegrable (fun t => ‖deriv f t-t⁻¹ • f t‖^2/t) volume a b :=
    (((hdf.sub ((continuousOn_id.inv₀ hn).smul hfC)).norm.pow 2).div continuousOn_id hn).intervalIntegrable_of_Icc hab
  have hiB : IntervalIntegrable
      (fun t => 2*⟪f t,deriv f t⟫_ℝ/t^2-2*‖f t‖^2/t^3) volume a b :=
    ((((hfC.inner hdf).const_mul 2).div (continuousOn_id.pow 2)
      (fun t ht => pow_ne_zero 2 (hn t ht))).sub
        (((hfC.norm.pow 2).const_mul 2).div (continuousOn_id.pow 3)
          (fun t ht => pow_ne_zero 3 (hn t ht)))).intervalIntegrable_of_Icc hab
  have hB := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t (ht : t∈Set.uIcc a b) => cusp_hardy_boundary_hasDerivAt f t
      (hf t (by simpa only [Set.uIcc_of_le hab] using ht))
      (hn t (by simpa only [Set.uIcc_of_le hab] using ht))) hiB
  rw [←intervalIntegral.integral_sub hiE hiM]
  calc
    _ = ∫t in a..b, ‖deriv f t-t⁻¹ • f t‖^2/t+
          (2*⟪f t,deriv f t⟫_ℝ/t^2-2*‖f t‖^2/t^3) := by
      apply intervalIntegral.integral_congr
      intro t ht
      exact cusp_hardy_square_identity (f t) (deriv f t) t
        (hn t (by simpa only [Set.uIcc_of_le hab] using ht))
    _ = _ := by rw [intervalIntegral.integral_add hiS hiB,hB]

theorem cusp_hardy_interval (f : ℝ → ℂ) (a b : ℝ)
    (ha : 0<a) (hab : a≤b) (hfa : f a=0)
    (hf : ∀t∈Set.Icc a b,DifferentiableAt ℝ f t)
    (hdf : ContinuousOn (deriv f) (Set.Icc a b)) :
    (∫t in a..b,‖f t‖^2/t^3)≤∫t in a..b,‖deriv f t‖^2/t := by
  have hid := cusp_hardy_interval_identity f a b ha hab hf hdf
  have hsq : 0≤∫t in a..b,‖deriv f t-t⁻¹ • f t‖^2/t := by
    apply intervalIntegral.integral_nonneg hab
    intro t ht
    exact div_nonneg (sq_nonneg _) (ha.trans_le ht.1).le
  have hb : 0≤‖f b‖^2/b^2 := div_nonneg (sq_nonneg _) (sq_nonneg _)
  simp only [hfa,norm_zero,zero_pow (by decide : 2≠0),zero_div,sub_zero] at hid
  linarith

theorem cusp_hardy_halfline (f : ℝ → ℂ) (a : ℝ) (ha : 0<a) (hfa : f a=0)
    (hf : ∀t∈Set.Ici a,DifferentiableAt ℝ f t)
    (hdf : ContinuousOn (deriv f) (Set.Ici a))
    (hM : IntegrableOn (fun t => ‖f t‖^2/t^3) (Set.Ioi a) volume)
    (hE : IntegrableOn (fun t => ‖deriv f t‖^2/t) (Set.Ioi a) volume) :
    (∫t in Set.Ioi a,‖f t‖^2/t^3)≤∫t in Set.Ioi a,‖deriv f t‖^2/t := by
  apply le_of_tendsto_of_tendsto
    (intervalIntegral_tendsto_integral_Ioi a hM tendsto_id)
    (intervalIntegral_tendsto_integral_Ioi a hE tendsto_id)
  filter_upwards [eventually_ge_atTop a] with b hab
  exact cusp_hardy_interval f a b ha hab hfa
    (fun t ht => hf t ht.1) (hdf.mono (fun t ht => ht.1))

theorem cusp_hardy_interval_lintegral (f : ℝ → ℂ) (a b : ℝ)
    (ha : 0<a) (hab : a≤b) (hfa : f a=0)
    (hf : ∀t∈Set.Icc a b,DifferentiableAt ℝ f t)
    (hdf : ContinuousOn (deriv f) (Set.Icc a b)) :
    (∫⁻t in Set.Ioc a b,ENNReal.ofReal (‖f t‖^2/t^3))≤
      ∫⁻t in Set.Ioc a b,ENNReal.ofReal (‖deriv f t‖^2/t) := by
  have hfC : ContinuousOn f (Set.Icc a b) :=
    fun t ht => (hf t ht).continuousAt.continuousWithinAt
  have hn : ∀t∈Set.Icc a b,t≠0 := fun t ht => (ha.trans_le ht.1).ne'
  have hiE : IntervalIntegrable (fun t => ‖deriv f t‖^2/t) volume a b :=
    ((hdf.norm.pow 2).div continuousOn_id hn).intervalIntegrable_of_Icc hab
  have hiM : IntervalIntegrable (fun t => ‖f t‖^2/t^3) volume a b :=
    ((hfC.norm.pow 2).div (continuousOn_id.pow 3)
      (fun t ht => pow_ne_zero 3 (hn t ht))).intervalIntegrable_of_Icc hab
  have hEnn : 0≤ᵐ[volume.restrict (Set.Ioc a b)] (fun t => ‖deriv f t‖^2/t) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact div_nonneg (sq_nonneg _) (ha.trans ht.1).le
  have hMnn : 0≤ᵐ[volume.restrict (Set.Ioc a b)] (fun t => ‖f t‖^2/t^3) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact div_nonneg (sq_nonneg _) (pow_nonneg (ha.trans ht.1).le 3)
  rw [←ofReal_integral_eq_lintegral_ofReal hiM.1 hMnn,
    ←ofReal_integral_eq_lintegral_ofReal hiE.1 hEnn]
  apply ENNReal.ofReal_le_ofReal
  simpa only [intervalIntegral.integral_of_le hab] using
    cusp_hardy_interval f a b ha hab hfa hf hdf

theorem cusp_hardy_halfline_lintegral (f : ℝ → ℂ) (a : ℝ) (ha : 0<a) (hfa : f a=0)
    (hf : ∀t∈Set.Ici a,DifferentiableAt ℝ f t)
    (hdf : ContinuousOn (deriv f) (Set.Ici a)) :
    (∫⁻t in Set.Ioi a,ENNReal.ofReal (‖f t‖^2/t^3))≤
      ∫⁻t in Set.Ioi a,ENNReal.ofReal (‖deriv f t‖^2/t) := by
  have hcover : (⋃n : ℕ,Set.Ioc a (a+n))=Set.Ioi a := by
    ext t
    constructor
    · rintro ⟨_,⟨n,rfl⟩,ht⟩
      exact ht.1
    · intro ht
      obtain ⟨n,hn⟩ := exists_nat_ge (t-a)
      exact Set.mem_iUnion.mpr ⟨n,ht,by linarith⟩
  have hdir : Directed (· ⊆ ·) (fun n : ℕ => Set.Ioc a (a+n)) := by
    intro m n
    refine ⟨max m n,Set.Ioc_subset_Ioc_right ?_,Set.Ioc_subset_Ioc_right ?_⟩
    · change a+(m:ℝ)≤a+((max m n:ℕ):ℝ)
      have hh : (m:ℝ)≤((max m n:ℕ):ℝ) := by exact_mod_cast le_max_left m n
      linarith
    · change a+(n:ℝ)≤a+((max m n:ℕ):ℝ)
      have hh : (n:ℝ)≤((max m n:ℕ):ℝ) := by exact_mod_cast le_max_right m n
      linarith
  calc
    _ = ⨆n : ℕ,∫⁻t in Set.Ioc a (a+n),ENNReal.ofReal (‖f t‖^2/t^3) := by
      rw [←hcover]
      exact setLIntegral_iUnion_of_directed _ hdir
    _ ≤ _ := by
      apply iSup_le
      intro n
      exact (cusp_hardy_interval_lintegral f a (a+n) ha (le_add_of_nonneg_right (Nat.cast_nonneg n)) hfa
        (fun t ht => hf t ht.1) (hdf.mono (fun t ht => ht.1))).trans
          (lintegral_mono_set Set.Ioc_subset_Ioi_self)

open Filter MeasureTheory
open scoped BigOperators Classical Topology InnerProductSpace ENNReal

abbrev CuspChartCoordinates := (ℝ×ℝ)×ℝ


def cuspVerticalDerivative (F : CuspChartCoordinates → ℂ) (q : CuspChartCoordinates) : ℂ :=
  deriv (fun v => F (q.1,v)) q.2

def cuspVerticalVelocity (F : CuspChartCoordinates → ℂ) (q : CuspChartCoordinates) : ℂ :=
  (q.2:ℂ)*cuspVerticalDerivative F q

lemma cusp_weight_mass_identity (u : ℂ) (v : ℝ) (hv : 0<v) :
    ENNReal.ofReal ((v^3)⁻¹) * ENNReal.ofReal (‖u‖^2)=
      ENNReal.ofReal (‖u‖^2/v^3) := by
  rw [←ENNReal.ofReal_mul (by positivity)]
  congr 1
  ring

lemma cusp_weight_velocity_identity (u : ℂ) (v : ℝ) (hv : 0<v) :
    ENNReal.ofReal ((v^3)⁻¹) * ENNReal.ofReal (‖(v:ℂ)*u‖^2)=
      ENNReal.ofReal (‖u‖^2/v) := by
  rw [cusp_weight_mass_identity _ _ hv,norm_mul,mul_pow,Complex.norm_real,
    Real.norm_of_nonneg hv.le]
  congr 1
  field_simp


def cuspCoordinateVelocity (F : CuspChartCoordinates → ℂ)
    (q : CuspChartCoordinates) : Fin 3 → ℂ :=
  ![(q.2:ℂ)*deriv (fun x => F ((x,q.1.2),q.2)) q.1.1,
    (q.2:ℂ)*deriv (fun y => F ((q.1.1,y),q.2)) q.1.2,
    cuspVerticalVelocity F q]


end

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology ENNReal

lemma cusp_height_volume (a : ℝ) (ha : 0<a) :
    (∫⁻v in Set.Ioi a,ENNReal.ofReal ((v^3)⁻¹))=ENNReal.ofReal (1/(2*a^2)) := by
  have hi : IntegrableOn (fun v : ℝ => (v^3)⁻¹) (Set.Ioi a) volume := by
    simpa only [show (-3:ℝ)=-(3:ℕ) by norm_num,Real.rpow_neg_natCast,zpow_neg,
      zpow_natCast] using (integrableOn_Ioi_rpow_of_lt (by norm_num : (-3:ℝ) < -1) ha)
  have hn : 0≤ᵐ[volume.restrict (Set.Ioi a)] (fun v : ℝ => (v^3)⁻¹) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    exact inv_nonneg.mpr (pow_nonneg (ha.trans hv).le 3)
  rw [←ofReal_integral_eq_lintegral_ofReal hi hn]
  congr 1
  have he := integral_Ioi_rpow_of_lt (by norm_num : (-3:ℝ) < -1) ha
  norm_num only at he
  simp only [show (-3:ℝ)=-(3:ℕ) by norm_num,Real.rpow_neg_natCast,zpow_neg,
    zpow_natCast] at he
  rw [he]
  norm_num [show (-3:ℝ)+1=-2 by norm_num]
  ring


end

open Filter MeasureTheory
open scoped BigOperators Classical Topology InnerProductSpace ENNReal ContDiff

def cuspCoordinateVector : Fin 3 → CuspChartCoordinates := ![((1,0),0),((0,1),0),((0,0),1)]

lemma cuspCoordinateVelocity_eq_fderiv (F : CuspChartCoordinates → ℂ)
    (hF : Differentiable ℝ F) (q : CuspChartCoordinates) (j : Fin 3) :
    cuspCoordinateVelocity F q j=(q.2:ℂ)*fderiv ℝ F q (cuspCoordinateVector j) := by
  fin_cases j
  · have hd := (hF q).hasFDerivAt.comp_hasDerivAt q.1.1
      (((hasDerivAt_id q.1.1).prodMk (hasDerivAt_const q.1.1 q.1.2)).prodMk (hasDerivAt_const q.1.1 q.2))
    exact congrArg (fun u : ℂ => (q.2:ℂ)*u) hd.deriv
  · have hd := (hF q).hasFDerivAt.comp_hasDerivAt q.1.2
      (((hasDerivAt_const q.1.2 q.1.1).prodMk (hasDerivAt_id q.1.2)).prodMk (hasDerivAt_const q.1.2 q.2))
    exact congrArg (fun u : ℂ => (q.2:ℂ)*u) hd.deriv
  · have hd := (hF q).hasFDerivAt.comp_hasDerivAt q.2
      ((hasDerivAt_const q.2 q.1).prodMk (hasDerivAt_id q.2))
    exact congrArg (fun u : ℂ => (q.2:ℂ)*u) hd.deriv

lemma cuspCoordinateVelocity_continuous_compact (F : CuspChartCoordinates → ℂ)
    (hF : ContDiff ℝ ∞ F) (hC : HasCompactSupport F) (j : Fin 3) :
    Continuous (fun q => cuspCoordinateVelocity F q j) ∧
      HasCompactSupport (fun q => cuspCoordinateVelocity F q j) := by
  simp_rw [cuspCoordinateVelocity_eq_fderiv F (hF.differentiable (by simp))]
  have hc := hC.fderiv_apply ℝ (cuspCoordinateVector j)
  constructor
  · exact (Complex.continuous_ofReal.comp continuous_snd).mul
      ((hF.continuous_fderiv (by simp)).clm_apply continuous_const)
  · exact HasCompactSupport.mul_left hc


end CubicEisenstein

open scoped BigOperators Classical SchwartzMap
namespace CanonicalQuadraticSieve
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge CompletedGauss
open EisensteinSchwartzPoisson GaussGeneratorTransport UnrestrictedIdealReindex IdealMobiusDivisorSum


theorem primaryProduct_norm (I J : Ideal O) (hI : Admissible I) (hJ : Admissible J) :
    ‖eisEmbedding (primaryGenerator I*primaryGenerator J)‖ =
      Real.sqrt ((Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)) := by
  have hs : ‖eisEmbedding (primaryGenerator I*primaryGenerator J)‖^2 =
      (Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ) := by
    rw [map_mul,norm_mul,mul_pow,
      primaryGenerator_norm_sq I (supported_primaryGenerator_ne_zero I (admissible_supported hI)),
      primaryGenerator_norm_sq J (supported_primaryGenerator_ne_zero J (admissible_supported hJ))]
  rw [← hs,Real.sqrt_sq (norm_nonneg _)]


end CanonicalQuadraticSieve

end

end OAI

end


