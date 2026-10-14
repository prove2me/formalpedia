-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0242_parallel3
-- name    : PNT_ZeroFree_433_0242_parallel3
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T13:48:09.758989+00:00
-- url     : https://prove2.me/theorems/54d76c2a-42fe-4374-8066-a64d37d72be3
-- title:
--   Zero-free region foundations: Reciprocity.PrimaryCongruences [0242_parallel3]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.Reciprocity.PrimaryCongruences
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Reciprocity/PrimaryCongruences.lean#L470-L570

import Definitions.Def_PNT_ZeroFree_433_0004
import Definitions.Def_PNT_ZeroFree_433_0007
import Definitions.Def_PNT_ZeroFree_433_0009
import Definitions.Def_PNT_ZeroFree_433_0019
import Definitions.Def_PNT_ZeroFree_433_0044
import Definitions.Def_PNT_ZeroFree_433_0074
import Definitions.Def_PNT_ZeroFree_433_0075
import Definitions.Def_PNT_ZeroFree_433_0084
import Definitions.Def_PNT_ZeroFree_433_0085
import Definitions.Def_PNT_ZeroFree_433_0106
import Definitions.Def_PNT_ZeroFree_433_0131_parallel1
import Definitions.Def_PNT_ZeroFree_433_0131_parallel2
import Definitions.Def_PNT_ZeroFree_433_0136
import Definitions.Def_PNT_ZeroFree_433_0219_parallel1
import Definitions.Def_PNT_ZeroFree_433_0232_parallel1
import Definitions.Def_PNT_ZeroFree_433_0232_parallel1_1
import Definitions.Def_PNT_ZeroFree_433_0232_parallel2
import Definitions.Def_PNT_ZeroFree_433_0242_parallel1
import Definitions.Def_PNT_ZeroFree_433_0243_parallel3
import Definitions.Def_PNT_ZeroFree_433_0245
import Definitions.Def_PNT_ZeroFree_433_0246_parallel2
import Definitions.Def_PNT_ZeroFree_433_0247_parallel1
import Definitions.Def_PNT_ZeroFree_433_0267_parallel1
import Definitions.Def_PNT_ZeroFree_433_0285_parallel1_1

/- Supporting zero-free-region lemmas, grouped by independent dependencies.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Reciprocity/PrimaryCongruences.lean
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


open scoped BigOperators Classical

namespace CubicEisenstein


section
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups

open ConcreteTraceCRT
local notation "O" => ActualEisensteinCubic.O

lemma integral_upper_triangular_action (T : SL(2,ActualEisensteinCubic.O)) (hc : T 1 0=0)
    (z : ℂ) (v : ℝ) (hv : 0<v) :
    integralComplexMatrix T • upperPoint z v hv=
      upperPoint (eisEmbedding (T 0 0)^2*z+eisEmbedding (T 0 0*T 0 1)) v hv := by
  have hdet : T 0 0*T 1 1=1 := by
    simpa only [Matrix.det_fin_two,hc,mul_zero,sub_zero] using T.property
  let u : ActualEisensteinCubic.Oˣ := ⟨T 1 1,T 0 0,by rw [mul_comm,hdet],hdet⟩
  have hn : ‖eisEmbedding (T 1 1)‖=1 := GaussGeneratorTransport.norm_eisEmbedding_unit u
  have hprod : eisEmbedding (T 1 1)*star (eisEmbedding (T 1 1))=1 := by
    simpa only [Complex.star_def,Complex.normSq_eq_norm_sq,hn,one_pow,Complex.ofReal_one] using
      Complex.mul_conj (eisEmbedding (T 1 1))
  have hstar : star (eisEmbedding (T 1 1))=eisEmbedding (T 0 0) := by
    have hnon : eisEmbedding (T 1 1)≠0 := by
      intro hz
      rw [hz,norm_zero] at hn
      exact zero_ne_one hn
    apply mul_left_cancel₀ hnon
    rw [hprod,←map_mul,mul_comm,hdet,map_one]
  rw [mobius_upperPoint]
  apply upperPoint_congr
  · simp only [integralComplexMatrix_apply,hc,map_zero,zero_mul,zero_add,star_zero,
      mul_zero,add_zero,norm_zero,hn,one_pow,hstar,map_mul]
    norm_num
    ; ring
  · simp only [integralComplexMatrix_apply,hc,map_zero,zero_mul,zero_add,norm_zero,
      hn,one_pow,]
    norm_num

theorem period_integral_upper_triangular
    (F : HyperbolicSpace→ℂ) (v : ℝ) (hv : 0<v)
    (hp : ∀n : ActualEisensteinCubic.O,∀z : ℂ,
      F (upperPoint (3*(z+3*eisEmbedding n)) v hv)=F (upperPoint (3*z) v hv))
    (T : SL(2,ActualEisensteinCubic.O)) (hc : T 1 0=0) :
    (∫z in periodDomain,F (integralComplexMatrix T • upperPoint (3*z) v hv))=
      ∫z in periodDomain,F (upperPoint (3*z) v hv) := by
  have hdet : T 0 0*T 1 1=1 := by
    simpa only [Matrix.det_fin_two,hc,mul_zero,sub_zero] using T.property
  let u : ActualEisensteinCubic.Oˣ := ⟨T 0 0,T 1 1,hdet,by rw [mul_comm,hdet]⟩
  let f : ℂ→ℂ := fun z=>F (upperPoint (3*z) v hv)
  have he (z : ℂ) : F (integralComplexMatrix T • upperPoint (3*z) v hv)=
      f (eisEmbedding (↑(u^2):ActualEisensteinCubic.O)*z+eisEmbedding (T 0 0*T 0 1)/3) := by
    rw [integral_upper_triangular_action T hc]
    dsimp only [f]
    congr 2
    simp only [Units.val_pow_eq_pow_val,map_pow]
    ring
  simp_rw [he]
  exact period_integral_unit_affine f hp (u^2) _

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology ENNReal

local notation "O" => ActualEisensteinCubic.O
namespace SubexponentialBesselCoefficients

lemma series_scaled_three_average_zero (coeff : SubexponentialBesselCoefficients)
    (v : ℝ) (hv : 0<v) : (∫z in periodDomain,coeff.series (v,3*z))=0 := by
  let : Countable ActualEisensteinCubic.O := ActualEisensteinCubic.latticeCoordEquiv.injective.countable
  let : IsFiniteMeasure (volume.restrict periodDomain) := isFiniteMeasure_restrict.mpr (by
    rw [periodDomain_volume]
    exact ENNReal.ofReal_ne_top)
  let f : ActualEisensteinCubic.O→ℂ→ℂ := fun h z => coeff.term h (v,3*z)
  have hc (h : ActualEisensteinCubic.O) : Continuous (f h) := by
    change Continuous (fun z : ℂ => coeff.term h (v,3*z))
    simp_rw [coeff.term_eq_amplitude v hv h]
    change Continuous (fun z : ℂ => coeff.amplitude v h*
      Complex.exp (2*Real.pi*Complex.I*((cuspFrequency h*(3*z))+
        starRingEnd ℂ (cuspFrequency h*(3*z)))))
    fun_prop
  obtain ⟨C,hC,hbound⟩ := coeff.slab_bound v v hv le_rfl
  have hfbound (h : ActualEisensteinCubic.O) (z : ℂ) : ‖f h z‖≤C*Real.exp (-(Real.pi*v)*‖cuspFrequency h‖) :=
    hbound h (v,3*z) ⟨le_rfl,le_rfl⟩
  have hi (h : ActualEisensteinCubic.O) : IntegrableOn (f h) periodDomain volume :=
    (integrable_const (C*Real.exp (-(Real.pi*v)*‖cuspFrequency h‖))).mono'
      (hc h).aestronglyMeasurable (Eventually.of_forall (hfbound h))
  have hnorm (h : ActualEisensteinCubic.O) : (∫z in periodDomain,‖f h z‖)≤
      volume.real periodDomain*(C*Real.exp (-(Real.pi*v)*‖cuspFrequency h‖)) := by
    have hh := integral_mono_ae (hi h).norm (integrable_const (C*Real.exp (-(Real.pi*v)*‖cuspFrequency h‖)))
      (Eventually.of_forall (hfbound h))
    simpa only [setIntegral_const,smul_eq_mul] using hh
  have hs : Summable (fun h : ActualEisensteinCubic.O => ∫z in periodDomain,‖f h z‖) := by
    apply Summable.of_nonneg_of_le (fun h => integral_nonneg (fun z => norm_nonneg _)) hnorm
    exact ((summable_exp_neg_cuspFrequency_norm (Real.pi*v) (mul_pos Real.pi_pos hv)).mul_left C).mul_left
      (volume.real periodDomain)
  have hterm (h : ActualEisensteinCubic.O) : (∫z in periodDomain,f h z)=0 := by
    have he (z : ℂ) : cuspFrequency h*(3*z)= -cuspFrequency (-(3*h))*z := by
      simp only [cuspFrequency,map_neg,map_mul,map_ofNat]
      ring
    change (∫z in periodDomain,coeff.term h (v,3*z))=0
    simp_rw [coeff.term_eq_amplitude v hv h,he]
    rw [integral_const_mul,integral_cusp_character]
    by_cases hh : h=0
    · simp [hh,amplitude]
    · have hk : -(3*h)≠(0:ActualEisensteinCubic.O) := neg_ne_zero.mpr (mul_ne_zero (by norm_num) hh)
      simp [hk]
  change (∫z in periodDomain,∑'h : ActualEisensteinCubic.O,f h z)=0
  rw [←integral_tsum_of_summable_integral_norm hi hs]
  simp_rw [hterm]
  exact tsum_zero


end SubexponentialBesselCoefficients


end CubicEisenstein


end

end OAI

end


