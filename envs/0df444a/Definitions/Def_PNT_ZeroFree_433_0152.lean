-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0152
-- name    : PNT_ZeroFree_433_0152
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T14:07:56.699267+00:00
-- url     : https://prove2.me/theorems/5c39318f-8d0c-4aa2-a840-0d8cdb725419
-- title:
--   Zero-free region foundations: CubicSieve.DivisorTargets [0152]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.CubicSieve.DivisorTargets
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/CubicSieve/DivisorTargets.lean#L82-L657

import Definitions.Def_PNT_ZeroFree_433_0007
import Definitions.Def_PNT_ZeroFree_433_0009
import Definitions.Def_PNT_ZeroFree_433_0048
import Definitions.Def_PNT_ZeroFree_433_0050
import Definitions.Def_PNT_ZeroFree_433_0054
import Definitions.Def_PNT_ZeroFree_433_0055
import Definitions.Def_PNT_ZeroFree_433_0059
import Definitions.Def_PNT_ZeroFree_433_0063
import Definitions.Def_PNT_ZeroFree_433_0070
import Definitions.Def_PNT_ZeroFree_433_0091
import Definitions.Def_PNT_ZeroFree_433_0102
import Definitions.Def_PNT_ZeroFree_433_0110
import Definitions.Def_PNT_ZeroFree_433_0119_parallel1
import Definitions.Def_PNT_ZeroFree_433_0124_parallel1
import Definitions.Def_PNT_ZeroFree_433_0128_parallel1
import Definitions.Def_PNT_ZeroFree_433_0128_parallel2
import Definitions.Def_PNT_ZeroFree_433_0141_parallel1
import Definitions.Def_PNT_ZeroFree_433_0142
import Definitions.Def_PNT_ZeroFree_433_0143
import Definitions.Def_PNT_ZeroFree_433_0152_parallel1
import Definitions.Def_PNT_ZeroFree_433_0247_parallel2
import Definitions.Def_PNT_ZeroFree_433_0249_parallel3

/- Supporting zero-free-region lemmas, grouped by independent dependencies.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/CubicSieve/DivisorTargets.lean
-/
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

section
namespace OAI

noncomputable section

namespace SecondPassArithmetic

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

section

open scoped BigOperators Classical


open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm cubeActiveSupport)
open ConcreteTraceCRT (eisEmbedding)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]

include hp in

theorem globalFirst_diagonal_scalar (K ell B F : ℝ)
    (hK : 0<K) (hell : 0<ell) (hB : 0<B) (hF : 0<F)
    (side : Bool) (b : GlobalFirstData ι) :
    globalFirstCoefficient p K ell B F side b*
        globalFirstPooledRow p K ell B F side b*(primeProductNorm p b.firstCommon)⁻¹ ≤
      (Real.exp 1)^3*ell*B^2*F*(1/primeProductNorm p b.common)*
        (1/primeProductNorm p b.firstCommon)*
        (1/‖eisEmbedding (∏ i∈cubeActiveSupport b.cube.support
          (fun i => b.cube.leftExponent i+b.cube.rightExponent i) b.cube.leftBit b.cube.rightBit,p i)‖) := by
  let x := b.append (⟨∅,∅,∅,1⟩ : SecondExpansionData ι)
  let j := globalScaleIndex p side x
  let A := globalCubeActiveRoot p x
  have hbds := globalScaleIndex_bounds p hp side x (by exact one_ne_zero)
  have hc := (hbds 1).2
  have ha := (hbds 9).2
  change primeProductNorm p b.common≤globalLogRep j 1*Real.exp 1 at hc
  change A^2≤globalLogRep j 9*Real.exp 1 at ha
  have hcp := FirstPassCubeLabels.primeProductNorm_pos p hp b.common
  have htp := FirstPassCubeLabels.primeProductNorm_pos p hp b.firstCommon
  have hA := globalCubeActiveRoot_pos p hp x
  change 0<A at hA
  have h1 := globalLogRep_ge_one j 1
  have h4 := globalLogRep_ge_one j 4
  have h1p := globalLogRep_pos j 1
  have h4p := globalLogRep_pos j 4
  have h5p := globalLogRep_pos j 5
  have h9p := globalLogRep_pos j 9
  have h9s := Real.sqrt_pos.mpr h9p
  have he : 1≤Real.exp 1 := Real.one_le_exp (by norm_num)
  have has : A≤Real.sqrt (globalLogRep j 9)*Real.exp 1 := by
    apply (sq_le_sq₀ hA.le (mul_nonneg h9s.le (Real.exp_pos _).le)).mp
    rw [mul_pow,Real.sq_sqrt h9p.le]
    exact ha.trans (mul_le_mul_of_nonneg_left (by nlinarith : Real.exp 1≤(Real.exp 1)^2) h9p.le)
  have hcA : primeProductNorm p b.common*A ≤
      (Real.exp 1)^2*((globalLogRep j 1)^2*globalLogRep j 4*Real.sqrt (globalLogRep j 9)) := by
    calc
      _ ≤ (globalLogRep j 1*Real.exp 1)*(Real.sqrt (globalLogRep j 9)*Real.exp 1) :=
        mul_le_mul hc has hA.le (by positivity)
      _ = (Real.exp 1)^2*(globalLogRep j 1*1*1*Real.sqrt (globalLogRep j 9)) := by ring
      _ ≤ (Real.exp 1)^2*(globalLogRep j 1*globalLogRep j 1*globalLogRep j 4*Real.sqrt (globalLogRep j 9)) := by gcongr
      _ = _ := by ring
  have hr : 1/((globalLogRep j 1)^2*globalLogRep j 4*Real.sqrt (globalLogRep j 9))≤
      (Real.exp 1)^2/(primeProductNorm p b.common*A) := by
    apply (div_le_div_iff₀ (by positivity) (mul_pos hcp hA)).mpr
    simpa only [one_mul] using hcA
  change (K/(globalLogRep j 5*ell*B^2*F*Real.sqrt (globalLogRep j 9)))*
      (Real.exp 1*ell^2*B^4*F^2*globalLogRep j 5/(K*(globalLogRep j 1)^2*globalLogRep j 4))*
      (primeProductNorm p b.firstCommon)⁻¹≤_
  calc
    _ = (Real.exp 1*ell*B^2*F)*(1/((globalLogRep j 1)^2*globalLogRep j 4*Real.sqrt (globalLogRep j 9)))*
        (primeProductNorm p b.firstCommon)⁻¹ := by field_simp
    _ ≤ (Real.exp 1*ell*B^2*F)*((Real.exp 1)^2/(primeProductNorm p b.common*A))*
        (primeProductNorm p b.firstCommon)⁻¹ := by gcongr
    _ = _ := by change _ = (Real.exp 1)^3*ell*B^2*F*(1/primeProductNorm p b.common)*(1/primeProductNorm p b.firstCommon)*(1/A); ring

end

open scoped BigOperators Classical
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm primeProduct cubeActiveSupport)
open ConcreteTraceCRT (eisEmbedding)
open IdealMobiusDivisorSum (idealDivisors mem_idealDivisors)

section
variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hinj : Function.Injective (fun i => Ideal.span {p i}))

def globalFirstCountKey (b : GlobalFirstData ι) : CubeCoordinates ι × Finset ι × Finset ι :=
  (b.cube,b.common,b.firstCommon)


omit [∀ (i : ι), (span {p i}).IsMaximal] in
theorem globalFirst_divisor_dvd_target (b : GlobalFirstData ι) (hb : GlobalFirstAdmissible b) :
    (∏i∈b.firstDivisor,Ideal.span {p i})∣globalFirstDivisorTarget p (globalFirstCountKey b) := by
  have h := Finset.prod_dvd_prod_of_subset b.firstDivisor (b.common∪b.cube.support)
    (fun i => (Ideal.span {p i} : Ideal O)) hb.2.2
  rw [Finset.prod_union hb.2.1] at h
  exact h

include hinj in
theorem globalFirst_divisor_fiber_card (s : Finset (GlobalFirstData ι))
    (q : CubeCoordinates ι × Finset ι × Finset ι)
    (hs : ∀b∈s,GlobalFirstAdmissible b) (hq : ∀b∈s,globalFirstCountKey b=q) :
    s.card≤(idealDivisors (globalFirstDivisorTarget p q)).card := by
  let D := idealDivisors (globalFirstDivisorTarget p q)
  let encode (b : s) : D := ⟨∏i∈b.val.firstDivisor,Ideal.span {p i},by
    apply (mem_idealDivisors (globalFirstDivisorTarget_ne_zero p q)).mpr
    simpa only [hq b.val b.property] using globalFirst_divisor_dvd_target p b.val (hs b.val b.property)⟩
  have hi : Function.Injective encode := by
    intro b c he
    have hd := FirstCauchyArithmetic.family_product_injective (fun i => Ideal.span {p i}) hinj (congrArg Subtype.val he)
    have hk := (hq b.val b.property).trans (hq c.val c.property).symm
    apply Subtype.ext
    exact GlobalFirstData.ext (congrArg Prod.fst hk) (congrArg (fun q => q.2.2) hk)
      (congrArg (fun q => q.2.1) hk) hd
  simpa only [Fintype.card_coe,D] using Fintype.card_le_of_injective encode hi

include hp in
omit [∀ (i : ι), (span {p i}).IsMaximal] in
theorem globalFirstDivisorTarget_norm_bound (b : GlobalFirstData ι) (B U : ℝ)
    (hB : 0≤B) (hU : 0≤U) (hc : primeProductNorm p b.common≤U)
    (hb1 : ‖eisEmbedding (primeProduct p b.cube.support b.cube.leftExponent)‖^2≤B)
    (hb2 : ‖eisEmbedding (primeProduct p b.cube.support b.cube.rightExponent)‖^2≤B) :
    (Ideal.absNorm (globalFirstDivisorTarget p (globalFirstCountKey b)) : ℝ)≤U*B^2 := by
  have hrad := globalCube_radical_bound p hp B hB (b.append ⟨∅,∅,∅,1⟩) hb1 hb2
  change (Ideal.absNorm ((∏i∈b.common,Ideal.span {p i})*(∏i∈b.cube.support,Ideal.span {p i})) : ℝ)≤_
  rw [map_mul,Nat.cast_mul,←primeProductNorm_eq_ideal_norm,←primeProductNorm_eq_ideal_norm]
  exact mul_le_mul hc hrad (FirstPassCubeLabels.primeProductNorm_pos p hp _).le hU


end

theorem globalFirstData_harmonic_sum (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀{ι : Type*} [DecidableEq ι]
      (p : ι → O) (_hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (_hinj : Function.Injective (fun i => Ideal.span {p i}))
      (s : Finset (GlobalFirstData ι)) (B U : ℝ),
      1≤B → 1≤U → (∀b∈s,GlobalFirstAdmissible b) →
      (∀b∈s,primeProductNorm p b.common≤U) → (∀b∈s,primeProductNorm p b.firstCommon≤U) →
      (∀b∈s,‖eisEmbedding (primeProduct p b.cube.support b.cube.leftExponent)‖^2≤B) →
      (∀b∈s,‖eisEmbedding (primeProduct p b.cube.support b.cube.rightExponent)‖^2≤B) →
      (∑b∈s,(1/primeProductNorm p b.common)*(1/primeProductNorm p b.firstCommon)*
        (1/‖eisEmbedding (∏i∈cubeActiveSupport b.cube.support
          (fun i => b.cube.leftExponent i+b.cube.rightExponent i) b.cube.leftBit b.cube.rightBit,p i)‖))≤
        C*B^(1+ε)*(U*B^2)^ε*(128*Real.exp 1*(normLogBin U+1 : ℝ))^2 := by
  obtain ⟨D,hD,hdiv⟩ := IdealDivisorBound.ideal_divisor_small_power ε hε
  obtain ⟨E,hE,hcube⟩ := cube_coordinates_inverse_active_sum ε hε
  refine ⟨D*E,mul_pos hD hE,?_⟩
  intro ι _ p hp _ hinj s B U hB hU hs hC ht hb1 hb2
  let Q := s.image globalFirstCountKey
  let cubes := s.image GlobalFirstData.cube
  let commons := s.image GlobalFirstData.common
  let firsts := s.image GlobalFirstData.firstCommon
  let weight := fun q : CubeCoordinates ι × Finset ι × Finset ι =>
    (1/primeProductNorm p q.2.1)*(1/primeProductNorm p q.2.2)*
      (1/‖eisEmbedding (∏i∈cubeActiveSupport q.1.support
        (fun i => q.1.leftExponent i+q.1.rightExponent i) q.1.leftBit q.1.rightBit,p i)‖)
  have hw (q : CubeCoordinates ι × Finset ι × Finset ι) : 0≤weight q := by
    have h1 := (FirstPassCubeLabels.primeProductNorm_pos p hp q.2.1).le
    have h2 := (FirstPassCubeLabels.primeProductNorm_pos p hp q.2.2).le
    dsimp [weight]
    positivity
  have hfiber (q : CubeCoordinates ι × Finset ι × Finset ι) (hq : q∈Q) :
      ((s.filter (fun b => globalFirstCountKey b=q)).card : ℝ)≤D*(U*B^2)^ε := by
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hq
    have hc : ((s.filter (fun d => globalFirstCountKey d=globalFirstCountKey b)).card : ℝ)≤
        ((idealDivisors (globalFirstDivisorTarget p (globalFirstCountKey b))).card : ℝ) := by
      exact_mod_cast globalFirst_divisor_fiber_card p hinj (s.filter (fun d => globalFirstCountKey d=globalFirstCountKey b))
        (globalFirstCountKey b) (fun d hd => hs d (Finset.mem_filter.mp hd).1) (fun d hd => (Finset.mem_filter.mp hd).2)
    apply hc.trans ((hdiv _ (globalFirstDivisorTarget_ne_zero p _)).trans _)
    apply mul_le_mul_of_nonneg_left _ hD.le
    exact Real.rpow_le_rpow (Nat.cast_nonneg _)
      (globalFirstDivisorTarget_norm_bound p hp b B U (by linarith) (by linarith) (hC b hb) (hb1 b hb) (hb2 b hb)) hε.le
  have hsub : Q⊆cubes.product (commons.product firsts) := by
    intro q hq
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hq
    exact Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ hb,
      Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ hb,Finset.mem_image_of_mem _ hb⟩⟩
  have he : (∑b∈s,weight (globalFirstCountKey b))=
      ∑q∈Q,((s.filter (fun b => globalFirstCountKey b=q)).card : ℝ)*weight q := by
    calc
      _ = ∑q∈Q,∑b∈s.filter (fun b => globalFirstCountKey b=q),weight (globalFirstCountKey b) :=
        (Finset.sum_fiberwise_of_maps_to (fun b hb => Finset.mem_image_of_mem globalFirstCountKey hb) _).symm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro q hq
        have h := Finset.sum_congr rfl (fun b (hb : b∈s.filter (fun b => globalFirstCountKey b=q)) =>
          show weight (globalFirstCountKey b)=weight q by rw [(Finset.mem_filter.mp hb).2])
        rw [h]
        simp
  have hcube' := hcube p hp hinj cubes B hB (by
      intro x hx; obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hx; exact (hs b hb).1)
    (by intro x hx; obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hx; exact hb1 b hb)
    (by intro x hx; obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hx; exact hb2 b hb)
  have hC' := primeSupport_inverse_sum p hinj commons U (by
    intro C hCmem; obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hCmem; exact hC b hb)
  have ht' := primeSupport_inverse_sum p hinj firsts U (by
    intro T hT; obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hT; exact ht b hb)
  have hC0 : 0≤∑C∈commons,1/primeProductNorm p C :=
    Finset.sum_nonneg (fun C _ => one_div_nonneg.mpr (FirstPassCubeLabels.primeProductNorm_pos p hp C).le)
  have ht0 : 0≤∑T∈firsts,1/primeProductNorm p T :=
    Finset.sum_nonneg (fun T _ => one_div_nonneg.mpr (FirstPassCubeLabels.primeProductNorm_pos p hp T).le)
  change (∑b∈s,weight (globalFirstCountKey b))≤_
  rw [he]
  calc
    _ ≤ ∑q∈Q,(D*(U*B^2)^ε)*weight q := Finset.sum_le_sum (fun q hq => mul_le_mul_of_nonneg_right (hfiber q hq) (hw q))
    _ = (D*(U*B^2)^ε)*∑q∈Q,weight q := (Finset.mul_sum _ _ _).symm
    _ ≤ (D*(U*B^2)^ε)*∑q∈cubes.product (commons.product firsts),weight q :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun q _ _ => hw q)) (by positivity)
    _ = (D*(U*B^2)^ε)*
        ((∑x∈cubes,1/‖eisEmbedding (∏i∈cubeActiveSupport x.support
          (fun i => x.leftExponent i+x.rightExponent i) x.leftBit x.rightBit,p i)‖)*
          (∑C∈commons,1/primeProductNorm p C)*(∑T∈firsts,1/primeProductNorm p T)) := by
      congr 1
      simp only [Finset.product_eq_sprod,Finset.sum_product,weight]
      simp_rw [Finset.sum_mul,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x hx
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro T hT
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro C hCmem
      ring
    _ ≤ (D*(U*B^2)^ε)*((E*B^(1+ε))*(128*Real.exp 1*(normLogBin U+1 : ℝ))*(128*Real.exp 1*(normLogBin U+1 : ℝ))) := by
      gcongr
    _ = _ := by ring

end SecondPassArithmetic

end

end OAI

end


