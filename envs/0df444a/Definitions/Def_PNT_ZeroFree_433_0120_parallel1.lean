-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0120_parallel1
-- name    : PNT_ZeroFree_433_0120_parallel1
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T12:42:55.08219+00:00
-- url     : https://prove2.me/theorems/7ef898cf-b27b-40db-9620-fa14d427ddc3
-- title:
--   Zero-free region foundations: CubicSieve.PrincipalNormalization [0120_parallel1]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.CubicSieve.PrincipalNormalization
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/CubicSieve/PrincipalNormalization.lean#L81-L624

import Definitions.Def_PNT_ZeroFree_433_0007
import Definitions.Def_PNT_ZeroFree_433_0013
import Definitions.Def_PNT_ZeroFree_433_0031
import Definitions.Def_PNT_ZeroFree_433_0037_1
import Definitions.Def_PNT_ZeroFree_433_0040
import Definitions.Def_PNT_ZeroFree_433_0041
import Definitions.Def_PNT_ZeroFree_433_0048
import Definitions.Def_PNT_ZeroFree_433_0051
import Definitions.Def_PNT_ZeroFree_433_0053
import Definitions.Def_PNT_ZeroFree_433_0054
import Definitions.Def_PNT_ZeroFree_433_0054_1
import Definitions.Def_PNT_ZeroFree_433_0055
import Definitions.Def_PNT_ZeroFree_433_0062
import Definitions.Def_PNT_ZeroFree_433_0064
import Definitions.Def_PNT_ZeroFree_433_0070
import Definitions.Def_PNT_ZeroFree_433_0072
import Definitions.Def_PNT_ZeroFree_433_0073
import Definitions.Def_PNT_ZeroFree_433_0087
import Definitions.Def_PNT_ZeroFree_433_0091
import Definitions.Def_PNT_ZeroFree_433_0098
import Definitions.Def_PNT_ZeroFree_433_0103
import Definitions.Def_PNT_ZeroFree_433_0104
import Definitions.Def_PNT_ZeroFree_433_0105
import Definitions.Def_PNT_ZeroFree_433_0106
import Definitions.Def_PNT_ZeroFree_433_0107
import Definitions.Def_PNT_ZeroFree_433_0114
import Definitions.Def_PNT_ZeroFree_433_0119_parallel1
import Definitions.Def_PNT_ZeroFree_433_0127_parallel1
import Definitions.Def_PNT_ZeroFree_433_0168_parallel1
import Definitions.Def_PNT_ZeroFree_433_0195_parallel1
import Definitions.Def_PNT_ZeroFree_433_0264_parallel1_1

/- Supporting zero-free-region lemmas, grouped by independent dependencies.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/CubicSieve/PrincipalNormalization.lean
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

section
open ActualEisensteinCubic
open SecondPassFiber (newLabel newRow)
open ConcretePrimeRowBridge (idealGenerator)
local instance p2mAnonymous_PNT_ZeroFree_433_0120_parallel1_1 : Fintype Oˣ := @Fintype.ofFinite _ PrimaryIdealUnitReindex.finite_units

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i,lambda ∉ Ideal.span {p i})

def globalSecondLabel (x : GlobalSecondData ι) : O :=
  secondSupportLabel p x.cube.support x.cube.leftExponent x.cube.rightExponent
    x.cube.leftBit x.cube.rightBit (expansionSupportData x.common x.firstDivisor x.source)

omit [∀ (i : ι), (span {p i}).IsMaximal] in
theorem globalSecondLabel_span (x : GlobalSecondData ι) :
    Ideal.span {globalSecondLabel p x}=newLabel (globalSecondTuple p x) :=
  actualSecondLabel_span p x.cube.support x.common x.source.divisor x.source.overlap
    x.cube.leftExponent x.cube.rightExponent x.cube.leftBit x.cube.rightBit

def globalSecondLabelUnit (x : GlobalSecondData ι) : Oˣ :=
  Classical.choose (exists_label_unit (globalSecondLabel p x)
    (newLabel (globalSecondTuple p x)) (globalSecondLabel_span p x))

omit [∀ (i : ι), (span {p i}).IsMaximal] in
theorem globalSecondLabelUnit_spec (x : GlobalSecondData ι) :
    globalSecondLabel p x=(globalSecondLabelUnit p x : O)*idealGenerator (newLabel (globalSecondTuple p x)) :=
  Classical.choose_spec (exists_label_unit (globalSecondLabel p x)
    (newLabel (globalSecondTuple p x)) (globalSecondLabel_span p x))

theorem global_second_energy_pushforward
    (hinj : Function.Injective (fun i => Ideal.span {p i})) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ,0 < C ∧ ∀ (s : Finset (GlobalSecondData ι)) (t : Finset (Ideal O × O))
      (q : Ideal O × Ideal O × Ideal O) (w : GlobalSecondData ι → ℂ) (B lengthScale : ℝ)
      (F : Finset ι) (Ψ : O →* ℂ) (m : O) (H : Finset ι → ℂ) (negative : Bool),
      q.1 ≠ ⊥ → 0 ≤ B → 0 ≤ lengthScale →
      (∀ x∈s,GlobalSecondAdmissible x) → (∀ x∈s,globalSecondFixedTriple p x=q) →
      (∀ x∈s,(newLabel (globalSecondTuple p x),newRow (globalSecondTuple p x))∈t) →
      (∀ z∈t,z.1 ≠ ⊥) → (∀ z∈t,(Ideal.absNorm z.1 : ℝ) ≤ lengthScale) →
      (∀ x∈s,‖w x‖ ≤ B) →
      (∑ x∈s,‖w x‖ * ‖fixedChildRow p hp hcop hg F Ψ m H (globalSecondLabel p x)
        (if negative then -newRow (globalSecondTuple p x) else newRow (globalSecondTuple p x))‖^2) ≤
      B*C*(lengthScale*Ideal.absNorm q.1)^ε *
        ∑ u : Oˣ,∑ z∈t,‖idealChildRow p hp hcop hg F Ψ m H negative u z‖^2 := by
  obtain ⟨C,hC,hcard⟩ := globalSecond_fiber_card p hinj ε hε
  refine ⟨C,hC,?_⟩
  intro s t q w B lengthScale F Ψ m H negative hq hB hL hs hfixed hmap ht hnorm hw
  let f : GlobalSecondData ι → Oˣ × (Ideal O × O) := fun x =>
    (globalSecondLabelUnit p x,newLabel (globalSecondTuple p x),newRow (globalSecondTuple p x))
  let P : Oˣ × (Ideal O × O) → ℂ := fun z => idealChildRow p hp hcop hg F Ψ m H negative z.1 z.2
  have hm : ∀ x∈s,f x∈Finset.univ ×ˢ t := by
    intro x hx
    exact Finset.mem_product.mpr ⟨Finset.mem_univ _,hmap x hx⟩
  have hpush := DescentWeightedCauchy.bounded_energy_pushforward s (Finset.univ ×ˢ t) f w P B hm hw
  have he : (∑ x∈s,‖w x‖ * ‖fixedChildRow p hp hcop hg F Ψ m H (globalSecondLabel p x)
      (if negative then -newRow (globalSecondTuple p x) else newRow (globalSecondTuple p x))‖^2) =
      ∑ x∈s,‖w x‖ * ‖P (f x)‖^2 := by
    apply Finset.sum_congr rfl
    intro x hx
    rw [globalSecondLabelUnit_spec p x]
    rfl
  rw [he]
  apply hpush.trans
  calc
    _ ≤ ∑ z∈Finset.univ ×ˢ t,B*C*(lengthScale*Ideal.absNorm q.1)^ε * ‖P z‖^2 := by
      apply Finset.sum_le_sum
      intro z hz
      have hzt := (Finset.mem_product.mp hz).2
      have hc := hcard (s.filter (fun x => f x=z)) q z.2.1 z.2.2
        (fun x hx => hs x (Finset.mem_filter.mp hx).1) (ht z.2 hzt) hq
        (fun x hx => hfixed x (Finset.mem_filter.mp hx).1)
        (fun x hx => congrArg (fun z : Oˣ × (Ideal O × O) => z.2.1) (Finset.mem_filter.mp hx).2)
        (fun x hx => congrArg (fun z : Oˣ × (Ideal O × O) => z.2.2) (Finset.mem_filter.mp hx).2)
      have hn : (Ideal.absNorm z.2.1 : ℝ)*Ideal.absNorm q.1 ≤ lengthScale*Ideal.absNorm q.1 :=
        mul_le_mul_of_nonneg_right (hnorm z.2 hzt) (by positivity)
      have hc' := hc.trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (by positivity) hn hε.le) hC.le)
      have hfinal := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc' hB) (sq_nonneg ‖P z‖)
      simpa only [mul_assoc] using hfinal
    _ = _ := by
      rw [← Finset.mul_sum,Finset.sum_product]

def globalSecondMode (s : Finset (GlobalSecondData ι)) (w : GlobalSecondData ι → ℂ)
    (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m : O) (H₁ H₂ : Finset ι → ℂ) : ℂ :=
  ∑ x∈s,w x * star (fixedChildRow p hp hcop hg F Ψ₁ m H₁
    (globalSecondLabel p x) (newRow (globalSecondTuple p x))) *
    fixedChildRow p hp hcop hg F Ψ₂ m H₂ (globalSecondLabel p x) (-newRow (globalSecondTuple p x))

theorem global_second_mode_transfer
    (hinj : Function.Injective (fun i => Ideal.span {p i})) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ,0 < C ∧ ∀ (s : Finset (GlobalSecondData ι)) (t : Finset (Ideal O × O))
      (q : Ideal O × Ideal O × Ideal O) (w : GlobalSecondData ι → ℂ) (B lengthScale : ℝ)
      (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m : O) (H₁ H₂ : Finset ι → ℂ),
      q.1 ≠ ⊥ → 0 ≤ B → 0 ≤ lengthScale →
      (∀ x∈s,GlobalSecondAdmissible x) → (∀ x∈s,globalSecondFixedTriple p x=q) →
      (∀ x∈s,(newLabel (globalSecondTuple p x),newRow (globalSecondTuple p x))∈t) →
      (∀ z∈t,z.1 ≠ ⊥) → (∀ z∈t,(Ideal.absNorm z.1 : ℝ) ≤ lengthScale) →
      (∀ x∈s,‖w x‖ ≤ B) →
      ‖globalSecondMode p hp hcop hg s w F Ψ₁ Ψ₂ m H₁ H₂‖ ≤
      B*C*(lengthScale*Ideal.absNorm q.1)^ε *
        Real.sqrt (∑ u : Oˣ,∑ z∈t,‖idealChildRow p hp hcop hg F Ψ₁ m H₁ false u z‖^2) *
        Real.sqrt (∑ u : Oˣ,∑ z∈t,‖idealChildRow p hp hcop hg F Ψ₂ m H₂ true u z‖^2) := by
  obtain ⟨C,hC,hpush⟩ := global_second_energy_pushforward p hp hcop hg hinj ε hε
  refine ⟨C,hC,?_⟩
  intro s t q w B lengthScale F Ψ₁ Ψ₂ m H₁ H₂ hq hB hL hs hfixed hmap ht hnorm hw
  let P₁ := fun x => fixedChildRow p hp hcop hg F Ψ₁ m H₁ (globalSecondLabel p x) (newRow (globalSecondTuple p x))
  let P₂ := fun x => fixedChildRow p hp hcop hg F Ψ₂ m H₂ (globalSecondLabel p x) (-newRow (globalSecondTuple p x))
  have h₁ := hpush s t q w B lengthScale F Ψ₁ m H₁ false hq hB hL hs hfixed hmap ht hnorm hw
  have h₂ := hpush s t q w B lengthScale F Ψ₂ m H₂ true hq hB hL hs hfixed hmap ht hnorm hw
  simp only [Bool.false_eq_true,ite_false,ite_true] at h₁ h₂
  let D := B*C*(lengthScale*Ideal.absNorm q.1)^ε
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hCau := DescentWeightedCauchy.weighted_cauchy s w P₂ P₁
  have he : globalSecondMode p hp hcop hg s w F Ψ₁ Ψ₂ m H₁ H₂ =
      ∑ x∈s,w x*P₂ x*star (P₁ x) := by
    unfold globalSecondMode
    apply Finset.sum_congr rfl
    intro x hx
    dsimp [P₁,P₂]
    ring
  rw [he]
  apply hCau.trans
  calc
    _ ≤ Real.sqrt (D*∑ u : Oˣ,∑ z∈t,‖idealChildRow p hp hcop hg F Ψ₂ m H₂ true u z‖^2) *
      Real.sqrt (D*∑ u : Oˣ,∑ z∈t,‖idealChildRow p hp hcop hg F Ψ₁ m H₁ false u z‖^2) := by
        gcongr
    _ = _ := by
      rw [Real.sqrt_mul hD,Real.sqrt_mul hD]
      calc
        _ = (Real.sqrt D)^2 *
          Real.sqrt (∑ u : Oˣ,∑ z∈t,‖idealChildRow p hp hcop hg F Ψ₁ m H₁ false u z‖^2) *
          Real.sqrt (∑ u : Oˣ,∑ z∈t,‖idealChildRow p hp hcop hg F Ψ₂ m H₂ true u z‖^2) := by ring
        _ = _ := by rw [Real.sq_sqrt hD]

end

open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm b0Label jLabel cubeRadical)
open ConcretePrimeRowBridge (idealGenerator span_idealGenerator)
open SecondPassFiber (newLabel newRow)
open ConcreteTraceCRT (eisEmbedding)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i,lambda ∉ Ideal.span {p i})

omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] in
theorem rowCoprimeMask_congr_span (S : Finset ι) {a b : O}
    (h : Ideal.span {a}=Ideal.span {b}) :
    rowCoprimeMask (fun i => Ideal.span {p i}) S a = rowCoprimeMask (fun i => Ideal.span {p i}) S b := by
  have hm (i : ι) : a ∈ Ideal.span {p i} ↔ b ∈ Ideal.span {p i} := by
    rw [← Ideal.span_singleton_le_iff_mem, h, Ideal.span_singleton_le_iff_mem]
  simp only [rowCoprimeMask,hm]

theorem fixedChildRow_congr_mask_span (F : Finset ι) (Ψ : O →* ℂ) {a b : O}
    (h : Ideal.span {a}=Ideal.span {b}) (H : Finset ι → ℂ) (f y : O) :
    fixedChildRow p hp hcop hg F Ψ a H f y = fixedChildRow p hp hcop hg F Ψ b H f y := by
  simp only [fixedChildRow,secondChildColumn,rowCoprimeMask_congr_span p _ h]

theorem secondChildColumn_zero_of_mask_label_mem (Ψ : O →* ℂ) (m f y : O)
    (H : Finset ι → ℂ) (S : Finset ι) (i : ι) (hi : i ∈ S)
    (hmf : m*f ∈ Ideal.span {p i}) :
    secondChildColumn p hp hcop hg Ψ m f y H S = 0 := by
  rcases (inferInstance : (Ideal.span {p i}).IsPrime).mem_or_mem hmf with hm|hf
  · have hz : rowCoprimeMask (fun i => Ideal.span {p i}) S m=0 := by
      simp only [rowCoprimeMask,if_pos (show ∃ i∈S,m ∈ Ideal.span {p i} from ⟨i,hi,hm⟩)]
    simp only [secondChildColumn,hz,mul_zero,zero_mul]
  · have hz : rowCoprimeMask (fun i => Ideal.span {p i}) S f=0 := by
      simp only [rowCoprimeMask,if_pos (show ∃ i∈S,f ∈ Ideal.span {p i} from ⟨i,hi,hf⟩)]
    have hr := FirstPassCubeLabels.row_zero_of_mask_zero (fun i => Ideal.span {p i}) hg S f hz
    simp only [secondChildColumn,hr,zero_pow (by decide : (4 : ℕ) ≠ 0),mul_zero,zero_mul]

theorem fixedChildRow_restore_killed_pool (F B : Finset ι) (Ψ : O →* ℂ)
    (m f y : O) (H : Finset ι → ℂ) (hB : ∀ i∈B,m*f ∈ Ideal.span {p i}) :
    fixedChildRow p hp hcop hg (F\B) Ψ m H f y = fixedChildRow p hp hcop hg F Ψ m H f y := by
  unfold fixedChildRow
  apply Finset.sum_subset (Finset.powerset_mono.mpr Finset.sdiff_subset)
  intro S hS hn
  have hd : ¬ Disjoint B S := by
    intro hd
    apply hn
    apply Finset.mem_powerset.mpr
    intro i hi
    exact Finset.mem_sdiff.mpr ⟨(Finset.mem_powerset.mp hS) hi,
      fun hiB => Finset.disjoint_left.mp hd hiB hi⟩
  obtain ⟨i,hiB,hiS⟩ := Finset.not_disjoint_iff.mp hd
  exact secondChildColumn_zero_of_mask_label_mem p hp hcop hg Ψ m f y H S i hiS (hB i hiB)

def globalSecondMask (m : O) (x : GlobalSecondData ι) : O :=
  (m*b0Label p x.cube.support (fun i => x.cube.leftExponent i+x.cube.rightExponent i)
    x.cube.leftBit x.cube.rightBit *
    primeSubsetGenerator (fun i => Ideal.span {p i}) (x.source.sourceCommon\x.source.divisor)) *
    ∏ i∈x.firstCommon,p i

def fixedTripleMask (m : O) (q : Ideal O × Ideal O × Ideal O) : O :=
  m*idealGenerator q.1*idealGenerator q.2.1*idealGenerator q.2.2

omit [∀ (i : ι), (span {p i}).IsMaximal] in
theorem globalSecondMask_span (m : O) (x : GlobalSecondData ι) :
    Ideal.span {globalSecondMask p m x}=Ideal.span {fixedTripleMask m (globalSecondFixedTriple p x)} := by
  simp only [globalSecondMask,fixedTripleMask,globalSecondFixedTriple,
    ← Ideal.span_singleton_mul_span_singleton,span_idealGenerator,
    primeSubsetGenerator,FiniteGaussPhase.span_finset_prod]
  ring

omit [∀ (i : ι), (span {p i}).IsMaximal] in
theorem globalSecondMask_kills_cube_common (m : O) (x : GlobalSecondData ι) :
    ∀ i∈x.cube.support∪x.common,globalSecondMask p m x*globalSecondLabel p x ∈ Ideal.span {p i} := by
  intro i hi
  let J := jLabel p x.cube.support (fun i => x.cube.leftExponent i+x.cube.rightExponent i)
    x.cube.leftBit x.cube.rightBit
  let b0 := b0Label p x.cube.support (fun i => x.cube.leftExponent i+x.cube.rightExponent i)
    x.cube.leftBit x.cube.rightBit
  rcases Finset.mem_union.mp hi with hi|hi
  · have hd : p i ∣ J*b0 := (Finset.dvd_prod_of_mem p hi).trans
      (cubeRadical_dvd_jLabel_b0 p x.cube.support
        (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit x.cube.support_pos)
    have he : globalSecondMask p m x*globalSecondLabel p x =
        (J*b0)*(m*primeSubsetGenerator (fun i => Ideal.span {p i}) (x.source.sourceCommon\x.source.divisor)*
          (∏ i∈x.firstCommon,p i)*primeSubsetGenerator (fun i => Ideal.span {p i}) x.common*
          primeSubsetGenerator (fun i => Ideal.span {p i}) x.source.divisor*(∏ i∈x.source.overlap,p i)) := by
      simp only [globalSecondMask,globalSecondLabel,secondSupportLabel,expansionSupportData,J,b0]
      ring
    rw [he]
    exact Ideal.mem_span_singleton.mpr (dvd_mul_of_dvd_left hd _)
  · have hC : primeSubsetGenerator (fun i => Ideal.span {p i}) x.common ∈ Ideal.span {p i} := by
      have hs : Ideal.span {primeSubsetGenerator (fun i => Ideal.span {p i}) x.common} ≤ Ideal.span {p i} := by
        rw [primeSubsetGenerator,span_idealGenerator]
        exact Ideal.le_of_dvd (Finset.dvd_prod_of_mem (fun i => Ideal.span {p i}) hi)
      exact hs (Ideal.subset_span (Set.mem_singleton _))
    have hlabel : globalSecondLabel p x ∈ Ideal.span {p i} := by
      apply Ideal.mul_mem_right
      apply Ideal.mul_mem_right
      apply Ideal.mul_mem_right
      exact hC
    exact Ideal.mul_mem_left _ _ hlabel


end SecondPassArithmetic

open scoped BigOperators Classical SchwartzMap
namespace CanonicalQuadraticSieve

section
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge EisensteinSchwartzPoisson
open TruncatedPrincipalPoisson IdealMobiusDivisorSum

variable {m n p : Type} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]

def signedProductDivisorSum (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (P : Ideal O → m → Prop)
    (H : Ideal O → m → n → p → ℂ) : ℂ := by
  classical
  exact ∑ i, ∑ j, ∑ k, originalTerm rows left right a b 1 1 i j k *
    ∑ d ∈ idealDivisors (left j*right k), if P d i then
      (UniqueFactorizationMonoid.moebius d : ℂ)*H d i j k else 0

def correctionRectangleMajorant (S T : Finset (Ideal O))
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (P : Ideal O → m → Prop)
    (H : Ideal O → m → n → p → ℂ) : ℝ := by
  classical
  exact ∑ D ∈ S, ∑ E ∈ T, ∑ i, if P (D*E) i then
    ‖∑ j, ∑ k, originalTerm rows left right a b D E i j k * H (D*E) i j k‖ else 0

omit [DecidableEq m] [DecidableEq n] [DecidableEq p] in
theorem signedProductDivisorSum_le_rectangles (S T : Finset (Ideal O))
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (P : Ideal O → m → Prop)
    (H : Ideal O → m → n → p → ℂ)
    (hleft : ∀ j, left j ≠ 0) (hright : ∀ k, right k ≠ 0)
    (hS : ∀ j D, D ∣ left j → D ∈ S) (hT : ∀ k E, E ∣ right k → E ∈ T) :
    ‖signedProductDivisorSum rows left right a b P H‖ ≤
      correctionRectangleMajorant S T rows left right a b P H := by
  classical
  let pairCols : n × p → Ideal O := fun x => left x.1*right x.2
  let K := columnDivisorPool pairCols
  have hpair : ∀ x, pairCols x ≠ 0 := fun x => mul_ne_zero (hleft x.1) (hright x.2)
  have hK : ∀ j k d, d ∣ left j*right k → d ∈ K :=
    fun j k d hd => mem_columnDivisorPool_of_dvd pairCols hpair (j,k) d hd
  let A : m → n → p → K → ℂ := fun i j k d => if P d.val i then
    if d.val ∣ left j*right k then originalTerm rows left right a b 1 1 i j k * H d.val i j k else 0 else 0
  have he : signedProductDivisorSum rows left right a b P H =
      ∑ i, ∑ j, ∑ k, ∑ d : K, (UniqueFactorizationMonoid.moebius d.val:ℂ)*A i j k d := by
    unfold signedProductDivisorSum
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    rw [← divisorPool_filter K (left j*right k) (mul_ne_zero (hleft j) (hright k)) (hK j k),
      Finset.sum_filter, Finset.mul_sum]
    rw [Finset.sum_coe_sort K (fun d => (UniqueFactorizationMonoid.moebius d:ℂ)*
      (if P d i then if d ∣ left j*right k then originalTerm rows left right a b 1 1 i j k * H d i j k else 0 else 0))]
    apply Finset.sum_congr rfl
    intro d _
    by_cases hd : d ∣ left j*right k <;> by_cases hi : P d i <;>
      simp only [hd, hi, ite_true, ite_false, mul_zero] ; ring
  rw [he]
  apply (finite_principal_triangle (fun d : K => (UniqueFactorizationMonoid.moebius d.val:ℂ))
    (fun d => QuadraticInitialBound.norm_ideal_moebius_le_one d.val) A).trans
  have hp (i : m) := originalColumnSum_divisor_rectangles K S T rows left right a b i
    hleft hright hS hT P H
  have hi (i : m) : (∑ d : K, ‖∑ j, ∑ k, A i j k d‖) =
      ∑ d ∈ K, if P d i then ‖∑ j, ∑ k, if d ∣ left j*right k then
        originalTerm rows left right a b 1 1 i j k * H d i j k else 0‖ else 0 := by
    rw [Finset.sum_coe_sort K (fun d => ‖∑ j, ∑ k, if P d i then if d ∣ left j*right k then
      originalTerm rows left right a b 1 1 i j k * H d i j k else 0 else 0‖)]
    apply Finset.sum_congr rfl
    intro d _
    by_cases hd : P d i <;> simp only [hd, ite_true, ite_false, Finset.sum_const_zero, norm_zero]
  simp_rw [hi]
  apply (Finset.sum_le_sum (fun i _ => hp i)).trans
  unfold correctionRectangleMajorant
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro D _
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro E _
  apply Finset.sum_le_sum
  intro i _
  by_cases hd : D*E ∈ K
  · simp only [hd, ite_true]
    exact le_rfl
  · simp only [hd, ite_false]
    positivity

theorem HasSieveExponent.small_principal_window {α : ℝ} (hexp : HasSieveExponent α)
    (deltaLoss : ℝ) (hδ : 0 < deltaLoss) (ε : ℝ) (hε : 0 < ε) (S T : Finset (Ideal O))
    (D₁ D₂ B N M F U : ℝ) (hD₁ : 1 ≤ D₁) (hD₂ : 1 ≤ D₂) (hB : 1 ≤ B) (hN : 1 ≤ N)
    (hM : 0 < M) (hF : 0 < F) (hU : 0 ≤ U) (hD₁N : D₁ ≤ N) (hD₂N : D₂ ≤ N)
    (hS : ∀ D ∈ S, D₁ ≤ (Ideal.absNorm D:ℝ) ∧ (Ideal.absNorm D:ℝ) ≤ 2*D₁)
    (hT : ∀ E ∈ T, D₂ ≤ (Ideal.absNorm E:ℝ) ∧ (Ideal.absNorm E:ℝ) ≤ 2*D₂)
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (hr : Function.Injective rows) (hl : Function.Injective left) (hri : Function.Injective right)
    (hrows : ∀ i, Admissible (rows i) ∧ B/2 ≤ (Ideal.absNorm (rows i):ℝ) ∧ (Ideal.absNorm (rows i):ℝ) ≤ B)
    (hleft : ∀ j, Admissible (left j) ∧ N/2 ≤ (Ideal.absNorm (left j):ℝ) ∧ (Ideal.absNorm (left j):ℝ) ≤ N)
    (hright : ∀ k, Admissible (right k) ∧ N/2 ≤ (Ideal.absNorm (right k):ℝ) ∧ (Ideal.absNorm (right k):ℝ) ≤ N)
    (a : n → ℂ) (b : p → ℂ) (P : Ideal O → m → Prop)
    (hP : ∀ D ∈ S, ∀ E ∈ T, ∀ i, P (D*E) i → (Ideal.absNorm (D*E):ℝ) ≤
      U*(N*Real.sqrt (F/(M*(Ideal.absNorm (rows i):ℝ))))) :
    correctionRectangleMajorant S T rows left right a b P
      (fun _ _ j k => ((M/(Real.sqrt ((Ideal.absNorm (left j):ℝ)*(Ideal.absNorm (right k):ℝ))*F):ℝ):ℂ)) ≤
      2*divisorEnergyFactor ε hε N a b*(divisorExponentConstant hexp deltaLoss hδ*(B*N)^deltaLoss)*
        (M/F+(2*U)*Real.sqrt (M/F)*B^(α-1/2)) := by
  classical
  by_cases hc : D₁*D₂ ≤ (2*U)*(N*Real.sqrt (F/(M*B)))
  · apply le_trans (b := smallPrincipalCorrection S T rows left right a b M F)
    · unfold correctionRectangleMajorant smallPrincipalCorrection
      apply Finset.sum_le_sum
      intro D _
      apply Finset.sum_le_sum
      intro E _
      apply Finset.sum_le_sum
      intro i _
      split_ifs <;> first | exact le_rfl | positivity
    · exact hexp.small_principal_correction deltaLoss hδ ε hε S T D₁ D₂ B N M F (2*U)
        hD₁ hD₂ hB hN hM hF hD₁N hD₂N hS hT rows left right hr hl hri
        (fun i => ⟨(hrows i).1,(hrows i).2.2⟩) hleft hright a b hc
  · have hz : correctionRectangleMajorant S T rows left right a b P
        (fun _ _ j k => ((M/(Real.sqrt ((Ideal.absNorm (left j):ℝ)*(Ideal.absNorm (right k):ℝ))*F):ℝ):ℂ)) = 0 := by
      unfold correctionRectangleMajorant
      apply Finset.sum_eq_zero
      intro D hD
      apply Finset.sum_eq_zero
      intro E hE
      apply Finset.sum_eq_zero
      intro i _
      have hn : ¬P (D*E) i := by
        intro hp
        apply hc
        apply dual_middle_rectangle_upper M F B (Ideal.absNorm (rows i)) N D₁ D₂
          (Ideal.absNorm D) (Ideal.absNorm E) U hM hF (by linarith) (hrows i).2.1
          (by linarith) hU (by linarith) (by linarith) (hS D hD).1 (hT E hE).1
        simpa only [map_mul,Nat.cast_mul] using hP D hD E hE i hp
      simp only [hn,ite_false]
    rw [hz]
    have he := divisorEnergyFactor_nonneg ε hε N a b
    have hd := (divisorExponentConstant_pos hexp deltaLoss hδ).le
    positivity

theorem HasSieveExponent.small_principal_divisor_sum {α : ℝ} (hexp : HasSieveExponent α)
    (deltaLoss : ℝ) (hδ : 0 < deltaLoss) (ε : ℝ) (hε : 0 < ε)
    (B N M F U : ℝ) (hB : 1 ≤ B) (hN : 1 ≤ N) (hM : 0 < M) (hF : 0 < F) (hU : 0 ≤ U)
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (hr : Function.Injective rows) (hl : Function.Injective left) (hri : Function.Injective right)
    (hrows : ∀ i, Admissible (rows i) ∧ B/2 ≤ (Ideal.absNorm (rows i):ℝ) ∧ (Ideal.absNorm (rows i):ℝ) ≤ B)
    (hleft : ∀ j, Admissible (left j) ∧ N/2 ≤ (Ideal.absNorm (left j):ℝ) ∧ (Ideal.absNorm (left j):ℝ) ≤ N)
    (hright : ∀ k, Admissible (right k) ∧ N/2 ≤ (Ideal.absNorm (right k):ℝ) ∧ (Ideal.absNorm (right k):ℝ) ≤ N)
    (a : n → ℂ) (b : p → ℂ) (P : Ideal O → m → Prop)
    (hP : ∀ d i, P d i → (Ideal.absNorm d:ℝ) ≤ U*(N*Real.sqrt (F/(M*(Ideal.absNorm (rows i):ℝ))))) :
    ‖signedProductDivisorSum rows left right a b P
      (fun _ _ j k => ((M/(Real.sqrt ((Ideal.absNorm (left j):ℝ)*(Ideal.absNorm (right k):ℝ))*F):ℝ):ℂ))‖ ≤
      ((columnDyadicLength N+1:ℕ):ℝ)^2 *
        (2*divisorEnergyFactor ε hε N a b*(divisorExponentConstant hexp deltaLoss hδ*(B*N)^deltaLoss)*
          (M/F+(2*U)*Real.sqrt (M/F)*B^(α-1/2))) := by
  classical
  let S := columnDivisorPool left
  let T := columnDivisorPool right
  have hl0 : ∀ j, left j ≠ 0 := fun j => (hleft j).1.1
  have hr0 : ∀ k, right k ≠ 0 := fun k => (hright k).1.1
  have hS := columnDivisorPool_norm_bounds left hl0 N (fun j => (hleft j).2.2)
  have hT := columnDivisorPool_norm_bounds right hr0 N (fun k => (hright k).2.2)
  apply (signedProductDivisorSum_le_rectangles S T rows left right a b P _ hl0 hr0
    (mem_columnDivisorPool_of_dvd left hl0) (mem_columnDivisorPool_of_dvd right hr0)).trans
  apply divisor_dyadic_sum_le S T N _ _
  · have he := divisorEnergyFactor_nonneg ε hε N a b
    have hd := (divisorExponentConstant_pos hexp deltaLoss hδ).le
    positivity
  · intro j k hj hk
    exact hexp.small_principal_window deltaLoss hδ ε hε (divisorDyadicBin S N j) (divisorDyadicBin T N k)
      (divisorDyadicScale j.val) (divisorDyadicScale k.val) B N M F U
      (divisorDyadicScale_ge_one _) (divisorDyadicScale_ge_one _) hB hN hM hF hU
      (divisorDyadicBin_scale_le S N hS j hj) (divisorDyadicBin_scale_le T N hT k hk)
      (divisorDyadicBin_bounds S N hS j) (divisorDyadicBin_bounds T N hT k)
      rows left right hr hl hri hrows hleft hright a b P (fun D _ E _ i hp => hP (D*E) i hp)

end

open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge EisensteinSchwartzPoisson
open TruncatedPrincipalPoisson IdealMobiusDivisorSum

lemma source_large_cut_lower (M B b N T d : ℝ)
    (hM : 0 < M) (_hB : 0 < B) (hb : 0 < b) (hbB : b ≤ B) (hN : 0 ≤ N) (hT : 0 < T)
    (hd : T*Real.sqrt (M/b) ≤ d) :
    Real.sqrt (M/B)*N ≤ ((4*N/T)/4)*d := by
  have hs : Real.sqrt (M/B) ≤ Real.sqrt (M/b) :=
    Real.sqrt_le_sqrt (div_le_div_of_nonneg_left hM.le hb hbB)
  have hsd : Real.sqrt (M/B) ≤ d/T := (le_div_iff₀ hT).mpr (by nlinarith)
  calc
    _ ≤ (d/T)*N := mul_le_mul_of_nonneg_right hsd hN
    _ = _ := by ring

lemma dual_large_cut_lower (M F B b N T d : ℝ)
    (hM : 0 < M) (hF : 0 < F) (hB : 0 < B) (hb : 0 < b) (hbB : b ≤ B)
    (hN : 0 < N) (hT : 0 < T) (hd : T*(N*Real.sqrt (F/(M*b))) ≤ d) :
    Real.sqrt ((M/F)/B)*N ≤ ((4*M/(F*T))/4)*d := by
  have hs : Real.sqrt (F/(M*B)) ≤ Real.sqrt (F/(M*b)) :=
    Real.sqrt_le_sqrt (div_le_div_of_nonneg_left hF.le (by positivity) (mul_le_mul_of_nonneg_left hbB hM.le))
  have hnd : N*Real.sqrt (F/(M*B)) ≤ d/T := by
    apply (le_div_iff₀ hT).mpr
    calc
      _ = T*(N*Real.sqrt (F/(M*B))) := by ring
      _ ≤ T*(N*Real.sqrt (F/(M*b))) := by gcongr
      _ ≤ d := hd
  rw [dual_middle_scale_identity M F B N hM hF hB hN]
  calc
    _ ≤ ((M/(F*N))*(d/T))*N := by gcongr
    _ = _ := by field_simp

variable {m n p : Type} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]

theorem HasSieveExponent.source_large_principal_sum {α : ℝ} (hexp : HasSieveExponent α)
    (deltaLoss : ℝ) (hδ : 0 < deltaLoss) (ε : ℝ) (hε : 0 < ε)
    (B N M T : ℝ) (hB : 1 ≤ B) (hN : 1 ≤ N) (hM : 0 < M) (hT : 0 < T)
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (hr : Function.Injective rows) (hl : Function.Injective left) (hri : Function.Injective right)
    (hrows : ∀ i, Admissible (rows i) ∧ B/2 ≤ (Ideal.absNorm (rows i):ℝ) ∧ (Ideal.absNorm (rows i):ℝ) ≤ B)
    (hleft : ∀ j, Admissible (left j) ∧ (Ideal.absNorm (left j):ℝ) ≤ N)
    (hright : ∀ k, Admissible (right k) ∧ (Ideal.absNorm (right k):ℝ) ≤ N)
    (a : n → ℂ) (b : p → ℂ) (Z : m → ℝ)
    (hZ : ∀ i, T*Real.sqrt (M/(Ideal.absNorm (rows i):ℝ)) ≤ Z i) :
    ‖principalDivisorCorrection rows left right a b M (fun d i => Z i < (Ideal.absNorm d:ℝ))‖ ≤
      ((columnDyadicLength N+1:ℕ):ℝ)^2 *
        (2*divisorEnergyFactor ε hε N a b*(divisorExponentConstant hexp deltaLoss hδ*(B*N)^deltaLoss)*
          (4*N/T+Real.sqrt M*B^(α-1/2))) := by
  apply hexp.principal_divisor_correction deltaLoss hδ ε hε B N M (4*N/T) hB hN hM (by positivity)
    rows left right hr hl hri hrows hleft hright a b
  intro d i hd
  exact source_large_cut_lower M B (Ideal.absNorm (rows i)) N T (Ideal.absNorm d) hM (by linarith)
    (by linarith [(hrows i).2.1]) (hrows i).2.2 (by linarith) hT ((hZ i).trans hd.le)

theorem HasSieveExponent.dual_large_principal_sum {α : ℝ} (hexp : HasSieveExponent α)
    (deltaLoss : ℝ) (hδ : 0 < deltaLoss) (ε : ℝ) (hε : 0 < ε)
    (B N M F T : ℝ) (hB : 1 ≤ B) (hN : 1 ≤ N) (hM : 0 < M) (hF : 0 < F) (hT : 0 < T)
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (hr : Function.Injective rows) (hl : Function.Injective left) (hri : Function.Injective right)
    (hrows : ∀ i, Admissible (rows i) ∧ B/2 ≤ (Ideal.absNorm (rows i):ℝ) ∧ (Ideal.absNorm (rows i):ℝ) ≤ B)
    (hleft : ∀ j, Admissible (left j) ∧ (Ideal.absNorm (left j):ℝ) ≤ N)
    (hright : ∀ k, Admissible (right k) ∧ (Ideal.absNorm (right k):ℝ) ≤ N)
    (a : n → ℂ) (b : p → ℂ) (Z : m → ℝ)
    (hZ : ∀ i, T*(N*Real.sqrt (F/(M*(Ideal.absNorm (rows i):ℝ)))) ≤ Z i) :
    ‖principalDivisorCorrection rows left right a b (M/F) (fun d i => Z i < (Ideal.absNorm d:ℝ))‖ ≤
      ((columnDyadicLength N+1:ℕ):ℝ)^2 *
        (2*divisorEnergyFactor ε hε N a b*(divisorExponentConstant hexp deltaLoss hδ*(B*N)^deltaLoss)*
          (4*M/(F*T)+Real.sqrt (M/F)*B^(α-1/2))) := by
  apply hexp.principal_divisor_correction deltaLoss hδ ε hε B N (M/F) (4*M/(F*T)) hB hN (by positivity) (by positivity)
    rows left right hr hl hri hrows hleft hright a b
  intro d i hd
  exact dual_large_cut_lower M F B (Ideal.absNorm (rows i)) N T (Ideal.absNorm d) hM hF (by linarith)
    (by linarith [(hrows i).2.1]) (hrows i).2.2 (by linarith) hT ((hZ i).trans hd.le)

omit [DecidableEq m] [DecidableEq n] [DecidableEq p] in
theorem dual_large_principal_normalization
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (M F : ℝ) (P : Ideal O → m → Prop)
    (hM : 0 < M) (hF : 0 < F)
    (hrows : ∀ i, rows i ≠ 0) (hleft : ∀ j, left j ≠ 0) (hright : ∀ k, right k ≠ 0) :
    (∑ i, ∑ j, ∑ k, originalTerm rows left right a b 1 1 i j k *
      (((M/(Real.sqrt ((Ideal.absNorm (left j):ℝ)*(Ideal.absNorm (right k):ℝ))*F):ℝ):ℂ) *
        ((Real.sqrt (F*(Ideal.absNorm (left j):ℝ)*(Ideal.absNorm (right k):ℝ)/
          (M*(Ideal.absNorm (rows i):ℝ))):ℝ):ℂ) *
        ∑ d ∈ idealDivisors (left j*right k), if P d i then
          (UniqueFactorizationMonoid.moebius d:ℂ)/(Ideal.absNorm d:ℂ) else 0)) =
      principalDivisorCorrection rows left right a b (M/F) P := by
  classical
  have hpos (I : Ideal O) (hI : I ≠ 0) : 0 < (Ideal.absNorm I:ℝ) := by
    exact_mod_cast Nat.pos_iff_ne_zero.mpr (fun h => hI (Ideal.absNorm_eq_zero_iff.mp h))
  unfold principalDivisorCorrection
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  rw [←Complex.ofReal_mul, dual_principal_prefactor_identity M F (Ideal.absNorm (rows i))
    (Ideal.absNorm (left j)) (Ideal.absNorm (right k)) hM hF (hpos _ (hrows i))
      (hpos _ (hleft j)) (hpos _ (hright k)), Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro d _
  by_cases hd : P d i
  · simp only [hd,ite_true,Complex.ofReal_div,Complex.ofReal_natCast]
    ring
  · simp only [hd,ite_false,mul_zero]

end CanonicalQuadraticSieve

end

end OAI

end


