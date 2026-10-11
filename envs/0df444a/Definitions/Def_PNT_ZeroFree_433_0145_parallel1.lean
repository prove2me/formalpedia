-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0145_parallel1
-- name    : PNT_ZeroFree_433_0145_parallel1
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T11:31:24.468409+00:00
-- url     : https://prove2.me/theorems/6b9054f8-5f49-479f-95c0-e3c1e7782d12
-- title:
--   Zero-free region foundations: QuadraticSieve.UniformTailBounds [0145_parallel1]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.QuadraticSieve.UniformTailBounds
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/QuadraticSieve/UniformTailBounds.lean#L132-L497

import Definitions.Def_PNT_ZeroFree_433_0007
import Definitions.Def_PNT_ZeroFree_433_0009
import Definitions.Def_PNT_ZeroFree_433_0038_1
import Definitions.Def_PNT_ZeroFree_433_0039
import Definitions.Def_PNT_ZeroFree_433_0041
import Definitions.Def_PNT_ZeroFree_433_0042
import Definitions.Def_PNT_ZeroFree_433_0048
import Definitions.Def_PNT_ZeroFree_433_0051
import Definitions.Def_PNT_ZeroFree_433_0053
import Definitions.Def_PNT_ZeroFree_433_0055
import Definitions.Def_PNT_ZeroFree_433_0070
import Definitions.Def_PNT_ZeroFree_433_0086
import Definitions.Def_PNT_ZeroFree_433_0095
import Definitions.Def_PNT_ZeroFree_433_0142_parallel1
import Definitions.Def_PNT_ZeroFree_433_0187_parallel1
import Definitions.Def_PNT_ZeroFree_433_0216_parallel1
import Definitions.Def_PNT_ZeroFree_433_0219_parallel1
import Definitions.Def_PNT_ZeroFree_433_0222_parallel1
import Definitions.Def_PNT_ZeroFree_433_0225_parallel2
import Definitions.Def_PNT_ZeroFree_433_0229_parallel1
import Definitions.Def_PNT_ZeroFree_433_0238_parallel1
import Definitions.Def_PNT_ZeroFree_433_0243_parallel1
import Definitions.Def_PNT_ZeroFree_433_0506_parallel1

/- Supporting zero-free-region lemmas, grouped by independent dependencies.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/QuadraticSieve/UniformTailBounds.lean
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


open scoped BigOperators Classical SchwartzMap
namespace SecondPassArithmetic
open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding eisEmbedding_ne_zero)
open FirstPassCubeLabels (columnLog normalizedColumn primeProductNorm)
open FirstCauchyArithmetic (supportMobius activeGaussRowFactor)
open JointLogSeparation (frequencyTwist frequencyTwist_apply)

theorem full_uniform_secondPairRadialMode_tail (A : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
    ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
      (hg : ∀ i, lambda ∉ Ideal.span {p i})
      (hinj : Function.Injective (fun i => Ideal.span {p i}))
      (_hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2),
    ∀ (S T : Finset ι) (e : O), e ≠ 0 → ∀ (W : 𝓢(ℝ, ℂ)) (Y H : ℝ),
      0 < Y → 0 ≤ H →
      let n := ∏ i : activeSupport T S, p i.val
      let scale := Y / (‖eisEmbedding e‖^2 * ‖eisEmbedding n‖^2)
      (∑' k : {k : O // H ≤ scale * ‖eisEmbedding k‖^2},
        ‖secondPairRadialMode p hp hg hinj S T e k.val W Y‖) ≤
      (Y / ‖eisEmbedding n‖) *
        ((C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) /
          ((min 1 scale)^2 * (1+H)^A)) := by
  obtain ⟨s,C,hC,hbound⟩ := EisensteinSchwartzPoisson.paperRadialFourier_lattice_tail A
  refine ⟨s,C,hC,?_⟩
  intro ι _ p hp _ hg hinj hc
    S T e he W Y H hY hH
  dsimp only
  let n := ∏ i : activeSupport T S, p i.val
  let scale := Y / (‖eisEmbedding e‖^2 * ‖eisEmbedding n‖^2)
  have hn : n ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i hi => hp i.val)
  have hnorm : 0 < ‖eisEmbedding n‖ := norm_pos_iff.mpr (eisEmbedding_ne_zero hn)
  have hscale : 0 < scale := div_pos hY
    (mul_pos (sq_pos_of_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero he))) (sq_pos_of_pos hnorm))
  let tailSet : Set O := {k | H ≤ scale * ‖eisEmbedding k‖^2}
  let c := Y / ‖eisEmbedding n‖
  have hc0 : 0 ≤ c := (div_pos hY hnorm).le
  have hpnt (k : tailSet) : ‖secondPairRadialMode p hp hg hinj S T e k.val W Y‖ ≤
      c * ‖EisensteinSchwartzPoisson.paperRadialFourier W (scale * ‖eisEmbedding k.val‖^2)‖ := by
    have ha : Y * ‖eisEmbedding k.val‖^2 / (‖eisEmbedding e‖^2 * ‖eisEmbedding n‖^2) =
        scale * ‖eisEmbedding k.val‖^2 := by dsimp [scale]; ring
    simp only [secondPairRadialMode, norm_mul]
    change ‖(Y : ℂ) / (‖eisEmbedding n‖ : ℂ)‖ * _ * _ ≤ _
    rw [ha, norm_div, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hY, abs_of_pos hnorm]
    exact mul_le_of_le_one_right (by positivity)
      (activeGaussRowFactor_norm_le_one p hp hg hinj hc T S e k.val)
  have hmajor : Summable (fun k : tailSet =>
      c * ‖EisensteinSchwartzPoisson.paperRadialFourier W (scale * ‖eisEmbedding k.val‖^2)‖) :=
    ((EisensteinSchwartzPoisson.paperRadialFourier_lattice_summable_norm W scale hscale).subtype tailSet).mul_left c
  have hsmall : Summable (fun k : tailSet => ‖secondPairRadialMode p hp hg hinj S T e k.val W Y‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hpnt hmajor
  calc
    _ ≤ ∑' k : tailSet, c * ‖EisensteinSchwartzPoisson.paperRadialFourier W
          (scale * ‖eisEmbedding k.val‖^2)‖ := hsmall.tsum_le_tsum hpnt hmajor
    _ = c * ∑' k : tailSet, ‖EisensteinSchwartzPoisson.paperRadialFourier W
          (scale * ‖eisEmbedding k.val‖^2)‖ := tsum_mul_left
    _ ≤ _ := mul_le_mul_of_nonneg_left (hbound W scale H hscale hH) hc0

theorem full_uniform_secondPairRadialMode_remainder (A : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
    ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
      (hg : ∀ i, lambda ∉ Ideal.span {p i})
      (hinj : Function.Injective (fun i => Ideal.span {p i}))
      (_hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2),
    ∀ (S T : Finset ι) (e : O), e ≠ 0 → ∀ (W : 𝓢(ℝ, ℂ)) (Y H : ℝ),
      0 < Y → 0 ≤ H → ∀ K : Finset O,
      let n := ∏ i : activeSupport T S, p i.val
      let scale := Y / (‖eisEmbedding e‖^2 * ‖eisEmbedding n‖^2)
      (∀ k : O, k ∉ K → H ≤ scale * ‖eisEmbedding k‖^2) →
      ‖∑' k : {k : O // k ∉ K}, secondPairRadialMode p hp hg hinj S T e k.val W Y‖ ≤
        (Y/‖eisEmbedding n‖) *
          ((C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/((min 1 scale)^2*(1+H)^A)) := by
  obtain ⟨s,C,hC,hb⟩ := full_uniform_secondPairRadialMode_tail A
  refine ⟨s,C,hC,?_⟩
  intro ι _ p hp _ hg hinj hc
  have hb := hb p hp hg hinj hc
  intro S T e he W Y H hY hH K
  dsimp only
  intro hK
  let n := ∏ i : activeSupport T S, p i.val
  let scale := Y / (‖eisEmbedding e‖^2 * ‖eisEmbedding n‖^2)
  let small : Set O := {k | k ∉ K}
  let large : Set O := {k | H ≤ scale * ‖eisEmbedding k‖^2}
  let f : small → large := fun k => ⟨k.val,hK k.val k.property⟩
  have hi : Function.Injective f := by
    intro a b heq
    exact Subtype.ext (congrArg (fun z : large => z.val) heq)
  have hs := secondPairRadialMode_summable_norm p hp hg hinj hc S T e he W Y hY
  calc
    _ ≤ ∑' k : small, ‖secondPairRadialMode p hp hg hinj S T e k.val W Y‖ :=
      norm_tsum_le_tsum_norm (hs.subtype small)
    _ ≤ ∑' k : large, ‖secondPairRadialMode p hp hg hinj S T e k.val W Y‖ :=
      (hs.subtype small).tsum_le_tsum_of_inj f hi (fun _ _ => norm_nonneg _) (fun _ => le_rfl)
        (hs.subtype large)
    _ ≤ _ := hb S T e he W Y H hY hH


end SecondPassArithmetic

open scoped BigOperators Classical
namespace InitialMeanSquare
open IdealMobiusDivisorSum

structure ElementDatum where
  divisor : Ideal O
  shared : O
  frequency : O
  deriving DecidableEq

def elementRow (gen : Ideal O→O) (x : ElementDatum) : O := gen x.divisor*x.frequency
def elementLabel (gen : Ideal O→O) (x : ElementDatum) : O := gen x.divisor*x.shared
def elementObservation (gen : Ideal O→O) (x : ElementDatum) : O×O := (elementRow gen x,elementLabel gen x)

theorem element_divisor_injective_on_fiber (gen : Ideal O→O) (y f : O) (hy : y≠0) :
    Set.InjOn ElementDatum.divisor {x : ElementDatum | elementObservation gen x=(y,f)} := by
  intro x hx z hz hd
  have hxrow : elementRow gen x=y := congrArg Prod.fst hx
  have hzrow : elementRow gen z=y := congrArg Prod.fst hz
  have hxlabel : elementLabel gen x=f := congrArg Prod.snd hx
  have hzlabel : elementLabel gen z=f := congrArg Prod.snd hz
  have hgen : gen x.divisor≠0 := by
    intro he
    apply hy
    rw [←hxrow,elementRow,he,zero_mul]
  have hs : x.shared=z.shared := by
    apply mul_left_cancel₀ hgen
    calc
      gen x.divisor*x.shared = f := hxlabel
      _ = gen z.divisor*z.shared := hzlabel.symm
      _ = gen x.divisor*z.shared := by rw [hd]
  have hh : x.frequency=z.frequency := by
    apply mul_left_cancel₀ hgen
    calc
      gen x.divisor*x.frequency = y := hxrow
      _ = gen z.divisor*z.frequency := hzrow.symm
      _ = gen x.divisor*z.frequency := by rw [hd]
  cases x
  cases z
  simp_all

theorem element_fiber_card_le (gen : Ideal O→O) (hgen : ∀D,Ideal.span {gen D}=D)
    (s : Finset ElementDatum) (y f : O) (hy : y≠0) :
    (s.filter (fun x => elementObservation gen x=(y,f))).card≤(idealDivisors (Ideal.span {y})).card := by
  have hyI : (Ideal.span {y}:Ideal O)≠0 := by intro hz; exact hy (Ideal.span_singleton_eq_bot.mp hz)
  apply Finset.card_le_card_of_injOn ElementDatum.divisor
  · intro x hx
    change x.divisor∈idealDivisors (Ideal.span {y})
    rw [mem_idealDivisors hyI]
    have he : elementRow gen x=y := congrArg Prod.fst (Finset.mem_filter.mp hx).2
    rw [←he,elementRow,←Ideal.span_singleton_mul_span_singleton,hgen]
    exact dvd_mul_right _ _
  · intro x hx z hz he
    exact element_divisor_injective_on_fiber gen y f hy (Finset.mem_filter.mp hx).2 (Finset.mem_filter.mp hz).2 he

theorem element_weighted_energy_pushforward (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ (gen : Ideal O→O), (∀D,Ideal.span {gen D}=D) →
      ∀ (s : Finset ElementDatum) (t : Finset (O×O)) (w : ElementDatum→ℂ)
        (P : O×O→ℂ) (A K : ℝ),
      0≤A → 0≤K → (∀x∈s,elementObservation gen x∈t) →
      (∀y∈t,y.1≠0) → (∀y∈t,(Ideal.absNorm (Ideal.span {y.1}):ℝ)≤K) →
      (∀x∈s,‖w x‖≤A) →
      (∑x∈s,‖w x‖*‖P (elementObservation gen x)‖^2)≤A*C*K^ε*∑y∈t,‖P y‖^2 := by
  obtain ⟨C,hC,hdiv⟩ := IdealDivisorBound.ideal_divisor_small_power ε hε
  refine ⟨C,hC,?_⟩
  intro gen hgen s t w P A K hA hK hmap ht hnorm hw
  apply (DescentWeightedCauchy.bounded_energy_pushforward s t (elementObservation gen) w P A hmap hw).trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro y hy
  have hyI : (Ideal.span {y.1}:Ideal O)≠0 := by intro hz; exact ht y hy (Ideal.span_singleton_eq_bot.mp hz)
  have hcard : ((s.filter (fun x => elementObservation gen x=y)).card:ℝ)≤C*K^ε := by
    calc
      _ ≤ ((idealDivisors (Ideal.span {y.1})).card:ℝ) := by
        exact_mod_cast element_fiber_card_le gen hgen s y.1 y.2 (ht y hy)
      _ ≤ C*(Ideal.absNorm (Ideal.span {y.1}):ℝ)^ε := hdiv _ hyI
      _ ≤ C*K^ε := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (Nat.cast_nonneg _) (hnorm y hy) hε.le) hC.le
  have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcard hA) (sq_nonneg ‖P y‖)
  simpa only [mul_assoc] using hh

end InitialMeanSquare


end

end OAI

end


