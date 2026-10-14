-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0128_parallel2
-- name    : PNT_ZeroFree_433_0128_parallel2
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T12:46:26.795787+00:00
-- url     : https://prove2.me/theorems/38519042-2ad1-4723-8650-2b7a6ec41ae5
-- title:
--   Zero-free region foundations: CubicSieve.ScaleCaps [0128_parallel2]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.CubicSieve.ScaleCaps
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/CubicSieve/ScaleCaps.lean#L226-L680

import Definitions.Def_PNT_ZeroFree_433_0007
import Definitions.Def_PNT_ZeroFree_433_0009
import Definitions.Def_PNT_ZeroFree_433_0040
import Definitions.Def_PNT_ZeroFree_433_0054
import Definitions.Def_PNT_ZeroFree_433_0054_1
import Definitions.Def_PNT_ZeroFree_433_0055
import Definitions.Def_PNT_ZeroFree_433_0059
import Definitions.Def_PNT_ZeroFree_433_0063
import Definitions.Def_PNT_ZeroFree_433_0070
import Definitions.Def_PNT_ZeroFree_433_0087
import Definitions.Def_PNT_ZeroFree_433_0091
import Definitions.Def_PNT_ZeroFree_433_0102
import Definitions.Def_PNT_ZeroFree_433_0107
import Definitions.Def_PNT_ZeroFree_433_0110
import Definitions.Def_PNT_ZeroFree_433_0118_parallel1
import Definitions.Def_PNT_ZeroFree_433_0119_parallel1
import Definitions.Def_PNT_ZeroFree_433_0122_parallel1
import Definitions.Def_PNT_ZeroFree_433_0124_parallel1
import Definitions.Def_PNT_ZeroFree_433_0127_parallel2
import Definitions.Def_PNT_ZeroFree_433_0128_parallel1
import Definitions.Def_PNT_ZeroFree_433_0129_parallel1
import Definitions.Def_PNT_ZeroFree_433_0135_parallel1
import Definitions.Def_PNT_ZeroFree_433_0137_parallel2
import Definitions.Def_PNT_ZeroFree_433_0181_parallel1
import Definitions.Def_PNT_ZeroFree_433_0208_parallel1
import Definitions.Def_PNT_ZeroFree_433_0264_parallel1

/- Supporting zero-free-region lemmas, grouped by independent dependencies.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/CubicSieve/ScaleCaps.lean
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
namespace SecondPassArithmetic


open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm)
open ConcreteTraceCRT (eisEmbedding)


section
variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]

def globalScaleVector (side : Bool) (x : GlobalSecondData ι) : Fin 10 → ℝ :=
  ![primeProductNorm p (x.cube.sideDivisor side),primeProductNorm p x.common,
    primeProductNorm p x.firstCommon,primeProductNorm p (x.source.sourceCommon\x.source.divisor),
    globalCubeJNorm p x,primeProductNorm p x.firstDivisor,primeProductNorm p x.source.divisor,
    primeProductNorm p x.source.overlap,‖eisEmbedding (SecondPassFiber.newRow (globalSecondTuple p x))‖^2,
    (globalCubeActiveRoot p x)^2]

def globalScaleIndex (side : Bool) (x : GlobalSecondData ι) : GlobalLogIndex :=
  fun i => normLogBin (globalScaleVector p side x i)

include hp in
theorem globalScaleVector_ge_one (side : Bool) (x : GlobalSecondData ι) (hk : x.source.frequency ≠ 0) :
    ∀ i,1 ≤ globalScaleVector p side x i := by
  intro i
  fin_cases i
  · exact primeProductNorm_ge_one p hp (x.cube.sideDivisor side)
  · exact primeProductNorm_ge_one p hp x.common
  · exact primeProductNorm_ge_one p hp x.firstCommon
  · exact primeProductNorm_ge_one p hp (x.source.sourceCommon\x.source.divisor)
  · change 1 ≤ globalCubeJNorm p x
    exact element_norm_ge_one _ (primeProduct_ne_zero p hp x.cube.support _)
  · exact primeProductNorm_ge_one p hp x.firstDivisor
  · exact primeProductNorm_ge_one p hp x.source.divisor
  · exact primeProductNorm_ge_one p hp x.source.overlap
  · change 1 ≤ ‖eisEmbedding (actualSecondRow p x.firstDivisor x.source.divisor x.source.frequency)‖^2
    exact element_norm_ge_one _ (actualSecondRow_ne_zero p _ _ _ hk)
  · change 1 ≤ (globalCubeActiveRoot p x)^2
    exact element_norm_ge_one _ (Finset.prod_ne_zero_iff.mpr (fun i hi => hp i))

include hp in
theorem globalScaleIndex_bounds (side : Bool) (x : GlobalSecondData ι) (hk : x.source.frequency ≠ 0)
    (i : Fin 10) :
    globalLogRep (globalScaleIndex p side x) i ≤ globalScaleVector p side x i ∧
    globalScaleVector p side x i ≤ globalLogRep (globalScaleIndex p side x) i*Real.exp 1 :=
  normLogBin_scale_bounds _ (globalScaleVector_ge_one p hp side x hk i)

include hp in
theorem globalScaleIndex_error (side : Bool) (x : GlobalSecondData ι) (hk : x.source.frequency ≠ 0)
    (i : Fin 10) :
    0 ≤ Real.log (globalScaleVector p side x i/globalLogRep (globalScaleIndex p side x) i) ∧
    Real.log (globalScaleVector p side x i/globalLogRep (globalScaleIndex p side x) i) ≤ 1 :=
  normLogBin_error _ (globalScaleVector_ge_one p hp side x hk i)

def globalLogSector (s : Finset (GlobalSecondData ι)) (side : Bool) (j : GlobalLogIndex) : Finset (GlobalSecondData ι) :=
  s.filter (fun x => globalScaleIndex p side x=j)

end


theorem globalScaleIndex_mem_box {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
    (side : Bool) (x : GlobalSecondData ι) (hk : x.source.frequency ≠ 0) (U : Fin 10 → ℝ)
    (hU : ∀ i,globalScaleVector p side x i ≤ U i) :
    globalScaleIndex p side x∈globalLogBox U := by
  apply Fintype.mem_piFinset.mpr
  intro i
  apply Finset.mem_range.mpr
  exact Nat.lt_succ_of_le (normLogBin_mono (zero_lt_one.trans_le (globalScaleVector_ge_one p hp side x hk i)) (hU i))

theorem sum_globalLogSector {ι M : Type*} [DecidableEq ι] [AddCommMonoid M]
    (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
    (s : Finset (GlobalSecondData ι)) (side : Bool) (U : Fin 10 → ℝ)
    (hk : ∀ x∈s,x.source.frequency ≠ 0)
    (hU : ∀ x∈s,∀ i,globalScaleVector p side x i ≤ U i) (f : GlobalSecondData ι → M) :
    ∑ x∈s,f x=∑ j∈globalLogBox U,∑ x∈globalLogSector p s side j,f x := by
  symm
  exact Finset.sum_fiberwise_of_maps_to (fun x hx => globalScaleIndex_mem_box p hp side x (hk x hx) U (hU x hx)) f


end SecondPassArithmetic

open scoped BigOperators Classical SchwartzMap


open scoped BigOperators Classical
namespace SecondPassArithmetic

section
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm)
open ConcreteTraceCRT (eisEmbedding)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]

def globalActualResidualScale (ell : ℝ) (side : Bool) (x : GlobalSecondData ι) : ℝ :=
  globalFirstColumnScale p ell x side/
    (primeProductNorm p x.firstCommon*primeProductNorm p x.source.divisor*
      primeProductNorm p (x.source.sourceCommon\x.source.divisor))

include hp in
omit [∀ (i : ι), (span {p i}).IsMaximal] in
theorem globalActualResidualScale_pos (ell : ℝ) (hell : 0 < ell) (side : Bool) (x : GlobalSecondData ι) :
    0 < globalActualResidualScale p ell side x := by
  exact div_pos (globalFirstColumnScale_pos p hp ell hell x side)
    (mul_pos (mul_pos (FirstPassCubeLabels.primeProductNorm_pos p hp _) (FirstPassCubeLabels.primeProductNorm_pos p hp _))
      (FirstPassCubeLabels.primeProductNorm_pos p hp _))

include hp in

theorem globalPooled_log_coordinates (ell : ℝ) (hell : 0 < ell) (side : Bool)
    (x : GlobalSecondData ι) (hk : x.source.frequency ≠ 0) :
    let j := globalScaleIndex p side x
    let d := expansionSupportData x.common x.firstDivisor x.source
    |secondSectorZ p (globalActualResidualScale p ell side x) (globalPooledColumnScale ell j) d| ≤ 6 ∧
    |secondSectorUd p (globalLogRep j 5) d| ≤ 6 ∧
    |secondSectorUe p (globalLogRep j 6) d| ≤ 6 ∧
    |secondSectorUv p (globalLogRep j 7) d| ≤ 6 ∧
    |secondSectorKap p (globalLogRep j 8) d| ≤ 6 := by
  let j := globalScaleIndex p side x
  let I : Finset (Fin 10) := {0,1,2,3,6,7}
  have hpos (i : Fin 10) : 0 < globalScaleVector p side x i :=
    zero_lt_one.trans_le (globalScaleVector_ge_one p hp side x hk i)
  have herr (i : Fin 10) := globalScaleIndex_error p hp side x hk i
  have hn (i : Fin 10) : globalScaleVector p side x i/globalLogRep j i ≠ 0 :=
    div_ne_zero (hpos i).ne' (globalLogRep_pos j i).ne'
  have hprod : primeProductNorm p x.source.overlap*globalPooledColumnScale ell j/
      globalActualResidualScale p ell side x =
      ∏ i∈I,globalScaleVector p side x i/globalLogRep j i := by
    have h (i : Fin 10) := (globalLogRep_pos j i).ne'
    have hA := (FirstPassCubeLabels.primeProductNorm_pos p hp (x.cube.sideDivisor side)).ne'
    have hC := (FirstPassCubeLabels.primeProductNorm_pos p hp x.common).ne'
    have ht := (FirstPassCubeLabels.primeProductNorm_pos p hp x.firstCommon).ne'
    have he := (FirstPassCubeLabels.primeProductNorm_pos p hp x.source.divisor).ne'
    have hr := (FirstPassCubeLabels.primeProductNorm_pos p hp (x.source.sourceCommon\x.source.divisor)).ne'
    simp (discharger := decide) only [I, Finset.prod_insert, Finset.prod_singleton]
    norm_num [globalScaleVector,globalPooledColumnScale,globalActualResidualScale,globalFirstColumnScale]
    dsimp [Matrix.vecCons, Fin.cons, Fin.cases]
    field_simp [h]
    all_goals simp only [Fin.induction, Fin.induction.go, eq_mpr_eq_cast, cast_eq]
    all_goals ring

  have hlog : 0 ≤ Real.log (primeProductNorm p x.source.overlap*globalPooledColumnScale ell j/
      globalActualResidualScale p ell side x) ∧
      Real.log (primeProductNorm p x.source.overlap*globalPooledColumnScale ell j/
        globalActualResidualScale p ell side x) ≤ 6 := by
    rw [hprod,Real.log_prod (fun i hi => hn i)]
    constructor
    · exact Finset.sum_nonneg (fun i hi => (herr i).1)
    · calc
        _ ≤ ∑ i∈I,(1 : ℝ) := Finset.sum_le_sum (fun i hi => (herr i).2)
        _ = 6 := by
          norm_num [I] <;> exact_mod_cast (show I.card = 6 from by dsimp [I]; decide)
  have hsmall (i : Fin 10) : |Real.log (globalScaleVector p side x i/globalLogRep j i)| ≤ 6 := by
    rw [abs_of_nonneg (herr i).1]
    exact (herr i).2.trans (by norm_num)
  dsimp only
  refine ⟨?_,?_,?_,?_,?_⟩
  · change |Real.log (primeProductNorm p x.source.overlap*globalPooledColumnScale ell j/
      globalActualResidualScale p ell side x)| ≤ 6
    rw [abs_of_nonneg hlog.1]
    exact hlog.2
  · change |Real.log (‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) x.firstDivisor)‖^2 / globalLogRep j 5)| ≤ 6
    rw [primeSubsetGenerator_norm_eq_productNorm]
    exact hsmall 5
  · change |Real.log (‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) x.source.divisor)‖^2 / globalLogRep j 6)| ≤ 6
    rw [primeSubsetGenerator_norm_eq_productNorm]
    exact hsmall 6
  · exact hsmall 7
  · exact hsmall 8

include hp in

theorem globalPooled_target_bounds (side : Bool) (x : GlobalSecondData ι) (hk : x.source.frequency ≠ 0) :
    let j := globalScaleIndex p side x
    (Ideal.absNorm (SecondPassFiber.newLabel (globalSecondTuple p x)) : ℝ) ≤ globalPooledLabelScale j ∧
    ‖eisEmbedding (SecondPassFiber.newRow (globalSecondTuple p x))‖^2 ≤ globalLogRep j 8*Real.exp 1 := by
  let j := globalScaleIndex p side x
  have hb (i : Fin 10) := (globalScaleIndex_bounds p hp side x hk i).2
  refine ⟨?_,hb 8⟩
  have he : (Ideal.absNorm (SecondPassFiber.newLabel (globalSecondTuple p x)) : ℝ) =
      globalScaleVector p side x 1*globalScaleVector p side x 4*
        globalScaleVector p side x 6*globalScaleVector p side x 7 := by
    rw [show SecondPassFiber.newLabel (globalSecondTuple p x) =
      secondSupportNewLabel p x.cube.support x.cube.leftExponent x.cube.rightExponent x.cube.leftBit x.cube.rightBit
        (expansionSupportData x.common x.firstDivisor x.source) from rfl,
      secondSupportNewLabel_norm,globalBaseLabel_norm]
    rfl
  rw [he]
  calc
    _ ≤ (globalLogRep j 1*Real.exp 1)*(globalLogRep j 4*Real.exp 1)*
        (globalLogRep j 6*Real.exp 1)*(globalLogRep j 7*Real.exp 1) := by
      have hpos (i : Fin 10) := (globalScaleVector_ge_one p hp side x hk i).trans' (by norm_num : (0:ℝ) ≤ 1)
      have hr1 := (globalLogRep_pos j 1).le
      have hr4 := (globalLogRep_pos j 4).le
      have hr6 := (globalLogRep_pos j 6).le
      have hr7 := (globalLogRep_pos j 7).le
      gcongr <;> first | exact hpos _ | exact hb _
    _ = globalPooledLabelScale j := by
      unfold globalPooledLabelScale
      rw [show (4:ℝ)=1+1+1+1 by norm_num,Real.exp_add,Real.exp_add,Real.exp_add]
      ring

end

open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm primeProduct)
open ConcreteTraceCRT (eisEmbedding)


variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]


include hp in
omit [∀ (i : ι), (span {p i}).IsMaximal] in
theorem globalCube_radical_bound (B : ℝ) (hB : 0 ≤ B) (x : GlobalSecondData ι)
    (hb₁ : ‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2 ≤ B)
    (hb₂ : ‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2 ≤ B) :
    primeProductNorm p x.cube.support ≤ B^2 := by
  have hd : (∏ i∈x.cube.support,p i) ∣ primeProduct p x.cube.support x.cube.leftExponent *
      primeProduct p x.cube.support x.cube.rightExponent := by
    rw [← primeProduct_add]
    apply Finset.prod_dvd_prod_of_dvd
    intro i hi
    simpa only [pow_one] using pow_dvd_pow (p i) (x.cube.support_pos i hi)
  have hb0 := mul_ne_zero (primeProduct_ne_zero p hp x.cube.support x.cube.leftExponent)
    (primeProduct_ne_zero p hp x.cube.support x.cube.rightExponent)
  have hn := element_norm_le_of_dvd hb0 hd
  simp only [map_mul,norm_mul,mul_pow] at hn
  exact hn.trans (by simpa only [pow_two] using mul_le_mul hb₁ hb₂ (sq_nonneg _) hB)


end SecondPassArithmetic

end

end OAI

end


