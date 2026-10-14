-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0152_parallel1
-- name    : PNT_ZeroFree_433_0152_parallel1
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T12:50:15.559133+00:00
-- url     : https://prove2.me/theorems/79505207-40b8-4922-b70a-c5257e3aef1b
-- title:
--   Zero-free region foundations: CubicSieve.DivisorTargets [0152_parallel1]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.CubicSieve.DivisorTargets
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/CubicSieve/DivisorTargets.lean#L82-L558

import Definitions.Def_PNT_ZeroFree_433_0007
import Definitions.Def_PNT_ZeroFree_433_0009
import Definitions.Def_PNT_ZeroFree_433_0039
import Definitions.Def_PNT_ZeroFree_433_0048
import Definitions.Def_PNT_ZeroFree_433_0050
import Definitions.Def_PNT_ZeroFree_433_0054
import Definitions.Def_PNT_ZeroFree_433_0054_1
import Definitions.Def_PNT_ZeroFree_433_0055
import Definitions.Def_PNT_ZeroFree_433_0058
import Definitions.Def_PNT_ZeroFree_433_0059
import Definitions.Def_PNT_ZeroFree_433_0063
import Definitions.Def_PNT_ZeroFree_433_0070
import Definitions.Def_PNT_ZeroFree_433_0102
import Definitions.Def_PNT_ZeroFree_433_0110
import Definitions.Def_PNT_ZeroFree_433_0118_parallel1
import Definitions.Def_PNT_ZeroFree_433_0119
import Definitions.Def_PNT_ZeroFree_433_0119_parallel1
import Definitions.Def_PNT_ZeroFree_433_0120_parallel1
import Definitions.Def_PNT_ZeroFree_433_0121_parallel1
import Definitions.Def_PNT_ZeroFree_433_0123
import Definitions.Def_PNT_ZeroFree_433_0128_parallel2
import Definitions.Def_PNT_ZeroFree_433_0131_parallel2
import Definitions.Def_PNT_ZeroFree_433_0136_parallel2
import Definitions.Def_PNT_ZeroFree_433_0144_parallel2
import Definitions.Def_PNT_ZeroFree_433_0149_parallel2
import Definitions.Def_PNT_ZeroFree_433_0151_parallel1
import Definitions.Def_PNT_ZeroFree_433_0158_parallel2
import Definitions.Def_PNT_ZeroFree_433_0226_parallel1

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

section
open ActualEisensteinCubic

lemma parity_pair_norm_bounds (s u : Ideal O) (B : ℝ) (hB : 0<B)
    (hs : s≠0) (hu : u≠0)
    (h : (Ideal.absNorm u : ℝ)^2*Ideal.absNorm s≤B^2) :
    (Ideal.absNorm s : ℝ)≤B^2 ∧ (Ideal.absNorm u : ℝ)≤B/Real.sqrt (Ideal.absNorm s) := by
  have hs1 : 1≤(Ideal.absNorm s : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (fun hz => hs (Ideal.absNorm_eq_zero_iff.mp hz))
  have hu1 : 1≤(Ideal.absNorm u : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (fun hz => hu (Ideal.absNorm_eq_zero_iff.mp hz))
  have hs0 : 0<(Ideal.absNorm s : ℝ) := by linarith
  have hsqrt : 0<Real.sqrt (Ideal.absNorm s : ℝ) := Real.sqrt_pos.mpr hs0
  refine ⟨(le_mul_of_one_le_left hs0.le (one_le_pow₀ hu1)).trans h,?_⟩
  apply (le_div_iff₀ hsqrt).mpr
  have hh : ((Ideal.absNorm u : ℝ)*Real.sqrt (Ideal.absNorm s : ℝ))^2≤B^2 := by
    simpa only [mul_pow,Real.sq_sqrt hs0.le] using h
  nlinarith [mul_nonneg (Nat.cast_nonneg (Ideal.absNorm u)) hsqrt.le]

lemma parity_pair_fiber_count (S : Finset (Ideal O × Ideal O)) (B : ℝ) (hB : 0<B)
    (hS : ∀ x∈S,x.1≠0 ∧ x.2≠0 ∧ (Ideal.absNorm x.2 : ℝ)^2*Ideal.absNorm x.1≤B^2)
    (s : Ideal O) (hs : s∈S.image Prod.fst) :
    ((S.filter (fun x => x.1=s)).card : ℝ)≤128*B/Real.sqrt (Ideal.absNorm s) := by
  obtain ⟨x,hx,hxs⟩ := Finset.mem_image.mp hs
  have hnx := parity_pair_norm_bounds x.1 x.2 B hB (hS x hx).1 (hS x hx).2.1 (hS x hx).2.2
  have hu1 : 1≤(Ideal.absNorm x.2 : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (fun hz => (hS x hx).2.1 (Ideal.absNorm_eq_zero_iff.mp hz))
  have hscale : 1≤B/Real.sqrt (Ideal.absNorm s) := by simpa only [hxs] using hu1.trans hnx.2
  let T := S.filter (fun x => x.1=s)
  have hi : Set.InjOn (fun x : Ideal O × Ideal O => x.2) (↑T : Set (Ideal O × Ideal O)) := by
    intro x hx y hy he
    exact Prod.ext ((Finset.mem_filter.mp hx).2.trans (Finset.mem_filter.mp hy).2.symm) he
  have hcount := DescentFiberCost.finite_ideal_count_real (T.image Prod.snd)
    (B/Real.sqrt (Ideal.absNorm s)) hscale (fun u hu => by
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hu
      exact (hS x (Finset.mem_filter.mp hx).1).2.1) (fun u hu => by
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hu
      have hn := parity_pair_norm_bounds x.1 x.2 B hB (hS x (Finset.mem_filter.mp hx).1).1
        (hS x (Finset.mem_filter.mp hx).1).2.1 (hS x (Finset.mem_filter.mp hx).1).2.2
      simpa only [(Finset.mem_filter.mp hx).2] using hn.2)
  rw [Finset.card_image_iff.mpr hi] at hcount
  simpa only [mul_div_assoc] using hcount

theorem parity_ideal_pair_count (S : Finset (Ideal O × Ideal O)) (B H : ℝ)
    (hB : 0<B) (hH : 0≤H)
    (hS : ∀ x∈S,x.1≠0 ∧ x.2≠0 ∧ (Ideal.absNorm x.2 : ℝ)^2*Ideal.absNorm x.1≤B^2)
    (hactive : ∀ x∈S,(Ideal.absNorm x.1 : ℝ)≤H^2) :
    (S.card : ℝ)≤16384*Real.exp 1*B*H*(normLogBin (B^2)+1 : ℝ) := by
  let A := S.image Prod.fst
  have hA (s : Ideal O) (hs : s∈A) : s≠0 ∧ (Ideal.absNorm s : ℝ)≤B^2 ∧ (Ideal.absNorm s : ℝ)≤H^2 := by
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hs
    exact ⟨(hS x hx).1,(parity_pair_norm_bounds x.1 x.2 B hB (hS x hx).1 (hS x hx).2.1 (hS x hx).2.2).1,hactive x hx⟩
  have he : (S.card : ℝ)=∑s∈A,((S.filter (fun x => x.1=s)).card : ℝ) := by
    calc
      _ = ∑_x∈S,(1 : ℝ) := by simp
      _ = ∑s∈A,∑_x∈S.filter (fun x => x.1=s),(1 : ℝ) :=
        (Finset.sum_fiberwise_of_maps_to (fun x hx => Finset.mem_image_of_mem Prod.fst hx) _).symm
      _ = _ := by simp
  rw [he]
  have hpoint (s : Ideal O) (hs : s∈A) :
      1/Real.sqrt (Ideal.absNorm s : ℝ)≤H/(Ideal.absNorm s : ℝ) := by
    have hs0 : 0<(Ideal.absNorm s : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (fun hz => (hA s hs).1 (Ideal.absNorm_eq_zero_iff.mp hz))
    have hroot : 0<Real.sqrt (Ideal.absNorm s : ℝ) := Real.sqrt_pos.mpr hs0
    have hrootle : Real.sqrt (Ideal.absNorm s : ℝ)≤H := by nlinarith [Real.sq_sqrt hs0.le,(hA s hs).2.2]
    apply (div_le_div_iff₀ hroot hs0).mpr
    nlinarith [Real.sq_sqrt hs0.le]
  calc
    _ ≤ ∑s∈A,128*B/Real.sqrt (Ideal.absNorm s) :=
      Finset.sum_le_sum (fun s hs => parity_pair_fiber_count S B hB hS s hs)
    _ ≤ ∑s∈A,(128*B*H)*(1/(Ideal.absNorm s : ℝ)) := by
      apply Finset.sum_le_sum
      intro s hs
      have h := mul_le_mul_of_nonneg_left (hpoint s hs) (by positivity : 0≤128*B)
      convert! h using 1 <;> ring
    _ = (128*B*H)*∑s∈A,1/(Ideal.absNorm s : ℝ) := (Finset.mul_sum _ _ _).symm
    _ ≤ (128*B*H)*(128*Real.exp 1*(normLogBin (B^2)+1 : ℝ)) :=
      mul_le_mul_of_nonneg_left (descent_ideal_inverse_sum A (B^2) (fun s hs => (hA s hs).1)
        (fun s hs => (hA s hs).2.1)) (by positivity)
    _ = _ := by ring

open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm primeProduct aLabel squarefreeLabel cubeActiveSupport)
open ConcreteTraceCRT (eisEmbedding)
open IdealMobiusDivisorSum (idealDivisors)

section
variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]

omit [∀ (i : ι), (span {p i}).IsMaximal] in
theorem cubeParityKey_norm_product (x : CubeCoordinates ι) :
    (Ideal.absNorm (cubeParityKey p x).2 : ℝ)^2*Ideal.absNorm (cubeParityKey p x).1 =
      ‖eisEmbedding (primeProduct p x.support x.leftExponent)‖^2*
        ‖eisEmbedding (primeProduct p x.support x.rightExponent)‖^2 := by
  have h := congrArg (fun I : Ideal O => (Ideal.absNorm I : ℝ)) (cubeParityKey_product p x)
  simpa only [cubeProductIdeal,map_mul,map_pow,Nat.cast_mul,Nat.cast_pow,
    ←eisEmbedding_norm_sq_eq_absNorm_span] using h.symm

include hp in
omit [∀ (i : ι), (span {p i}).IsMaximal] in
theorem cubeParityKey_active_bound (x : CubeCoordinates ι) (H : ℝ)
    (ha : ‖eisEmbedding (∏ i∈cubeActiveSupport x.support
      (fun i => x.leftExponent i+x.rightExponent i) x.leftBit x.rightBit,p i)‖≤H) :
    (Ideal.absNorm (cubeParityKey p x).1 : ℝ)≤H^2 := by
  have h := squarefreeLabel_active_bound p hp x.support
    (fun i => x.leftExponent i+x.rightExponent i) x.leftBit x.rightBit
  change ‖eisEmbedding _‖^2≤‖eisEmbedding _‖^2 at h
  exact (show (Ideal.absNorm (cubeParityKey p x).1 : ℝ)≤‖eisEmbedding
    (∏ i∈cubeActiveSupport x.support (fun i => x.leftExponent i+x.rightExponent i) x.leftBit x.rightBit,p i)‖^2 from
    by simpa only [cubeParityKey,←eisEmbedding_norm_sq_eq_absNorm_span] using h).trans
      (pow_le_pow_left₀ (norm_nonneg _) ha 2)

end

theorem cube_coordinates_parity_count (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → O) (_hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
      (_hinj : Function.Injective (fun i => Ideal.span {p i}))
      (s : Finset (CubeCoordinates ι)) (B H : ℝ),
      1≤B → 0≤H → (∀ x∈s,x.Admissible) →
      (∀ x∈s,‖eisEmbedding (primeProduct p x.support x.leftExponent)‖^2≤B) →
      (∀ x∈s,‖eisEmbedding (primeProduct p x.support x.rightExponent)‖^2≤B) →
      (∀ x∈s,‖eisEmbedding (∏ i∈cubeActiveSupport x.support
        (fun i => x.leftExponent i+x.rightExponent i) x.leftBit x.rightBit,p i)‖≤H) →
      (s.card : ℝ)≤C*B^(1+ε)*H := by
  obtain ⟨D,hD,hdiv⟩ := IdealDivisorBound.ideal_divisor_small_power (ε/12) (by positivity)
  let C := D^3*(16384*Real.exp 1)*(1+1/(ε/4))
  refine ⟨C,by dsimp [C]; positivity,?_⟩
  intro ι _ p hp _ hinj s B H hB hH hs hb1 hb2 ha
  have hB0 : 0<B := by linarith
  have hprod (x : CubeCoordinates ι) (hx : x∈s) :
      (Ideal.absNorm (cubeParityKey p x).2 : ℝ)^2*Ideal.absNorm (cubeParityKey p x).1≤B^2 := by
    rw [cubeParityKey_norm_product]
    simpa only [pow_two] using mul_le_mul (hb1 x hx) (hb2 x hx) (sq_nonneg _) hB0.le
  let Q := s.image (cubeParityKey p)
  have hQ (q : Ideal O × Ideal O) (hq : q∈Q) :
      q.1≠0 ∧ q.2≠0 ∧ (Ideal.absNorm q.2 : ℝ)^2*Ideal.absNorm q.1≤B^2 := by
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hq
    exact ⟨(cubeParityKey_ne_zero p hp x).1,(cubeParityKey_ne_zero p hp x).2,hprod x hx⟩
  have hQactive (q : Ideal O × Ideal O) (hq : q∈Q) : (Ideal.absNorm q.1 : ℝ)≤H^2 := by
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hq
    exact cubeParityKey_active_bound p hp x H (ha x hx)
  have hfiber (q : Ideal O × Ideal O) (hq : q∈Q) :
      ((s.filter (fun x => cubeParityKey p x=q)).card : ℝ)≤D^3*B^(ε/2) := by
    have hq0 := hQ q hq
    have hqprod0 : q.2^2*q.1≠0 := mul_ne_zero (pow_ne_zero _ hq0.2.1) hq0.1
    have hc : ((s.filter (fun x => cubeParityKey p x=q)).card : ℝ)≤
        ((idealDivisors (q.2^2*q.1)).card : ℝ)^3 := by
      exact_mod_cast cubeParityKey_fiber_card p hp hinj (s.filter (fun x => cubeParityKey p x=q)) q
        hq0.1 hq0.2.1 (fun x hx => hs x (Finset.mem_filter.mp hx).1)
        (fun x hx => (Finset.mem_filter.mp hx).2)
    have hn : (Ideal.absNorm (q.2^2*q.1) : ℝ)≤B^2 := by
      simpa only [map_mul,map_pow,Nat.cast_mul,Nat.cast_pow] using hq0.2.2
    calc
      _ ≤ ((idealDivisors (q.2^2*q.1)).card : ℝ)^3 := hc
      _ ≤ (D*(Ideal.absNorm (q.2^2*q.1) : ℝ)^(ε/12))^3 :=
        pow_le_pow_left₀ (Nat.cast_nonneg _) (hdiv _ hqprod0) 3
      _ ≤ (D*(B^2)^(ε/12))^3 := by gcongr
      _ = D^3*B^(ε/2) := by
        rw [mul_pow]
        congr 1
        rw [←Real.rpow_natCast,←Real.rpow_mul (sq_nonneg B),
          ←Real.rpow_natCast,←Real.rpow_mul hB0.le]
        congr 1
        ring
  have hqcard := parity_ideal_pair_count Q B H hB0 hH hQ hQactive
  have hlog := descent_normLogBin_small_power (ε/4) (by positivity) (B^2) (one_le_pow₀ hB)
  have hlog' : (normLogBin (B^2)+1 : ℝ)≤(1+1/(ε/4))*B^(ε/2) := by
    convert! hlog using 1
    rw [←Real.rpow_natCast,←Real.rpow_mul hB0.le]
    congr 2
    ring
  have hsum : (s.card : ℝ)=∑q∈Q,((s.filter (fun x => cubeParityKey p x=q)).card : ℝ) := by
    calc
      _ = ∑_x∈s,(1 : ℝ) := by simp
      _ = ∑q∈Q,∑_x∈s.filter (fun x => cubeParityKey p x=q),(1 : ℝ) :=
        (Finset.sum_fiberwise_of_maps_to (fun x hx => Finset.mem_image_of_mem (cubeParityKey p) hx) _).symm
      _ = _ := by simp
  rw [hsum]
  calc
    _ ≤ ∑_q∈Q,D^3*B^(ε/2) := Finset.sum_le_sum hfiber
    _ = (Q.card : ℝ)*(D^3*B^(ε/2)) := by simp
    _ ≤ (16384*Real.exp 1*B*H*(normLogBin (B^2)+1 : ℝ))*(D^3*B^(ε/2)) := by gcongr
    _ ≤ (16384*Real.exp 1*B*H*((1+1/(ε/4))*B^(ε/2)))*(D^3*B^(ε/2)) := by gcongr
    _ = C*B^(1+ε)*H := by
      rw [Real.rpow_add hB0,Real.rpow_one]
      have he : B^(ε/2)*B^(ε/2)=B^ε := by rw [←Real.rpow_add hB0]; congr 1; ring
      dsimp [C]
      calc
        _ = D^3*(16384*Real.exp 1)*(1+1/(ε/4))*B*(B^(ε/2)*B^(ε/2))*H := by ring
        _ = _ := by rw [he]; ring

end

section
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProduct cubeActiveSupport)
open ConcreteTraceCRT (eisEmbedding)
open IdealMobiusDivisorSum (idealDivisors)

theorem parity_ideal_pair_inverse_sqrt_sum (S : Finset (Ideal O × Ideal O)) (B : ℝ)
    (hB : 0<B)
    (hS : ∀ x∈S,x.1≠0 ∧ x.2≠0 ∧ (Ideal.absNorm x.2 : ℝ)^2*Ideal.absNorm x.1≤B^2) :
    (∑q∈S,1/Real.sqrt (Ideal.absNorm q.1 : ℝ))≤
      16384*Real.exp 1*B*(normLogBin (B^2)+1 : ℝ) := by
  let A := S.image Prod.fst
  have hA (s : Ideal O) (hs : s∈A) : s≠0 ∧ (Ideal.absNorm s : ℝ)≤B^2 := by
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hs
    exact ⟨(hS x hx).1,(parity_pair_norm_bounds x.1 x.2 B hB (hS x hx).1 (hS x hx).2.1 (hS x hx).2.2).1⟩
  have he : (∑q∈S,1/Real.sqrt (Ideal.absNorm q.1 : ℝ))=
      ∑s∈A,((S.filter (fun x => x.1=s)).card : ℝ)/Real.sqrt (Ideal.absNorm s : ℝ) := by
    calc
      _ = ∑s∈A,∑q∈S.filter (fun x => x.1=s),1/Real.sqrt (Ideal.absNorm q.1 : ℝ) :=
        (Finset.sum_fiberwise_of_maps_to (fun x hx => Finset.mem_image_of_mem Prod.fst hx) _).symm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro s hs
        have h : (∑q∈S.filter (fun x => x.1=s),1/Real.sqrt (Ideal.absNorm q.1 : ℝ))=
            ∑_q∈S.filter (fun x => x.1=s),1/Real.sqrt (Ideal.absNorm s : ℝ) :=
          Finset.sum_congr rfl (fun q hq => by rw [(Finset.mem_filter.mp hq).2])
        rw [h]
        simp [div_eq_mul_inv]
  rw [he]
  calc
    _ ≤ ∑s∈A,128*B/(Ideal.absNorm s : ℝ) := by
      apply Finset.sum_le_sum
      intro s hs
      have hpos : 0<(Ideal.absNorm s : ℝ) := by
        exact_mod_cast Nat.pos_of_ne_zero (fun hz => (hA s hs).1 (Ideal.absNorm_eq_zero_iff.mp hz))
      calc
        _ ≤ (128*B/Real.sqrt (Ideal.absNorm s : ℝ))/Real.sqrt (Ideal.absNorm s : ℝ) :=
          div_le_div_of_nonneg_right (parity_pair_fiber_count S B hB hS s hs) (Real.sqrt_nonneg _)
        _ = _ := by rw [div_div,←pow_two,Real.sq_sqrt hpos.le]
    _ = (128*B)*∑s∈A,1/(Ideal.absNorm s : ℝ) := by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro s hs; ring
    _ ≤ (128*B)*(128*Real.exp 1*(normLogBin (B^2)+1 : ℝ)) :=
      mul_le_mul_of_nonneg_left (descent_ideal_inverse_sum A (B^2)
        (fun s hs => (hA s hs).1) (fun s hs => (hA s hs).2)) (by positivity)
    _ = _ := by ring

theorem cube_coordinates_inverse_active_sum (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → O) (_hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
      (_hinj : Function.Injective (fun i => Ideal.span {p i}))
      (s : Finset (CubeCoordinates ι)) (B : ℝ),
      1≤B → (∀ x∈s,x.Admissible) →
      (∀ x∈s,‖eisEmbedding (primeProduct p x.support x.leftExponent)‖^2≤B) →
      (∀ x∈s,‖eisEmbedding (primeProduct p x.support x.rightExponent)‖^2≤B) →
      (∑x∈s,1/‖eisEmbedding (∏ i∈cubeActiveSupport x.support
        (fun i => x.leftExponent i+x.rightExponent i) x.leftBit x.rightBit,p i)‖)≤C*B^(1+ε) := by
  obtain ⟨D,hD,hdiv⟩ := IdealDivisorBound.ideal_divisor_small_power (ε/12) (by positivity)
  let C := D^3*(16384*Real.exp 1)*(1+1/(ε/4))
  refine ⟨C,by dsimp [C]; positivity,?_⟩
  intro ι _ p hp _ hinj s B hB hs hb1 hb2
  have hB0 : 0<B := by linarith
  have hprod (x : CubeCoordinates ι) (hx : x∈s) :
      (Ideal.absNorm (cubeParityKey p x).2 : ℝ)^2*Ideal.absNorm (cubeParityKey p x).1≤B^2 := by
    rw [cubeParityKey_norm_product]
    simpa only [pow_two] using mul_le_mul (hb1 x hx) (hb2 x hx) (sq_nonneg _) hB0.le
  let Q := s.image (cubeParityKey p)
  have hQ (q : Ideal O × Ideal O) (hq : q∈Q) :
      q.1≠0 ∧ q.2≠0 ∧ (Ideal.absNorm q.2 : ℝ)^2*Ideal.absNorm q.1≤B^2 := by
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hq
    exact ⟨(cubeParityKey_ne_zero p hp x).1,(cubeParityKey_ne_zero p hp x).2,hprod x hx⟩
  have hfiber (q : Ideal O × Ideal O) (hq : q∈Q) :
      ((s.filter (fun x => cubeParityKey p x=q)).card : ℝ)≤D^3*B^(ε/2) := by
    have hq0 := hQ q hq
    have hqprod0 : q.2^2*q.1≠0 := mul_ne_zero (pow_ne_zero _ hq0.2.1) hq0.1
    have hc : ((s.filter (fun x => cubeParityKey p x=q)).card : ℝ)≤
        ((idealDivisors (q.2^2*q.1)).card : ℝ)^3 := by
      exact_mod_cast cubeParityKey_fiber_card p hp hinj (s.filter (fun x => cubeParityKey p x=q)) q
        hq0.1 hq0.2.1 (fun x hx => hs x (Finset.mem_filter.mp hx).1)
        (fun x hx => (Finset.mem_filter.mp hx).2)
    have hn : (Ideal.absNorm (q.2^2*q.1) : ℝ)≤B^2 := by
      simpa only [map_mul,map_pow,Nat.cast_mul,Nat.cast_pow] using hq0.2.2
    calc
      _ ≤ ((idealDivisors (q.2^2*q.1)).card : ℝ)^3 := hc
      _ ≤ (D*(Ideal.absNorm (q.2^2*q.1) : ℝ)^(ε/12))^3 :=
        pow_le_pow_left₀ (Nat.cast_nonneg _) (hdiv _ hqprod0) 3
      _ ≤ (D*(B^2)^(ε/12))^3 := by gcongr
      _ = D^3*B^(ε/2) := by
        rw [mul_pow]
        congr 1
        rw [←Real.rpow_natCast,←Real.rpow_mul (sq_nonneg B),
          ←Real.rpow_natCast,←Real.rpow_mul hB0.le]
        congr 1
        ring
  have hlog := descent_normLogBin_small_power (ε/4) (by positivity) (B^2) (one_le_pow₀ hB)
  have hlog' : (normLogBin (B^2)+1 : ℝ)≤(1+1/(ε/4))*B^(ε/2) := by
    convert! hlog using 1
    rw [←Real.rpow_natCast,←Real.rpow_mul hB0.le]
    congr 2
    ring
  have hpoint (x : CubeCoordinates ι) :
      1/‖eisEmbedding (∏ i∈cubeActiveSupport x.support
        (fun i => x.leftExponent i+x.rightExponent i) x.leftBit x.rightBit,p i)‖≤
        1/Real.sqrt (Ideal.absNorm (cubeParityKey p x).1 : ℝ) := by
    have hs0 : 0<(Ideal.absNorm (cubeParityKey p x).1 : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (fun hz => (cubeParityKey_ne_zero p hp x).1 (Ideal.absNorm_eq_zero_iff.mp hz))
    have ha := cubeParityKey_active_bound p hp x _ le_rfl
    have hh : Real.sqrt (Ideal.absNorm (cubeParityKey p x).1 : ℝ)≤
        ‖eisEmbedding (∏ i∈cubeActiveSupport x.support
        (fun i => x.leftExponent i+x.rightExponent i) x.leftBit x.rightBit,p i)‖ := by
      nlinarith [Real.sq_sqrt hs0.le,norm_nonneg (eisEmbedding (∏ i∈cubeActiveSupport x.support
        (fun i => x.leftExponent i+x.rightExponent i) x.leftBit x.rightBit,p i))]
    exact one_div_le_one_div_of_le (Real.sqrt_pos.mpr hs0) hh
  have he : (∑x∈s,1/Real.sqrt (Ideal.absNorm (cubeParityKey p x).1 : ℝ))=
      ∑q∈Q,((s.filter (fun x => cubeParityKey p x=q)).card : ℝ)*(1/Real.sqrt (Ideal.absNorm q.1 : ℝ)) := by
    calc
      _ = ∑q∈Q,∑x∈s.filter (fun x => cubeParityKey p x=q),1/Real.sqrt (Ideal.absNorm (cubeParityKey p x).1 : ℝ) :=
        (Finset.sum_fiberwise_of_maps_to (fun x hx => Finset.mem_image_of_mem (cubeParityKey p) hx) _).symm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro q hq
        have h := Finset.sum_congr rfl (fun x (hx : x∈s.filter (fun x => cubeParityKey p x=q)) =>
          show 1/Real.sqrt (Ideal.absNorm (cubeParityKey p x).1 : ℝ)=1/Real.sqrt (Ideal.absNorm q.1 : ℝ) by
            rw [(Finset.mem_filter.mp hx).2])
        rw [h]
        simp
  calc
    _ ≤ ∑x∈s,1/Real.sqrt (Ideal.absNorm (cubeParityKey p x).1 : ℝ) := Finset.sum_le_sum (fun x _ => hpoint x)
    _ = _ := he
    _ ≤ ∑q∈Q,(D^3*B^(ε/2))*(1/Real.sqrt (Ideal.absNorm q.1 : ℝ)) := by
      exact Finset.sum_le_sum (fun q hq => mul_le_mul_of_nonneg_right (hfiber q hq) (by positivity))
    _ = (D^3*B^(ε/2))*(∑q∈Q,1/Real.sqrt (Ideal.absNorm q.1 : ℝ)) := (Finset.mul_sum _ _ _).symm
    _ ≤ (D^3*B^(ε/2))*(16384*Real.exp 1*B*(normLogBin (B^2)+1 : ℝ)) :=
      mul_le_mul_of_nonneg_left (parity_ideal_pair_inverse_sqrt_sum Q B hB0 hQ) (by positivity)
    _ ≤ (D^3*B^(ε/2))*(16384*Real.exp 1*B*((1+1/(ε/4))*B^(ε/2))) := by gcongr
    _ = C*B^(1+ε) := by
      rw [Real.rpow_add hB0,Real.rpow_one]
      have he : B^(ε/2)*B^(ε/2)=B^ε := by rw [←Real.rpow_add hB0]; congr 1; ring
      dsimp [C]
      calc
        _ = D^3*(16384*Real.exp 1)*(1+1/(ε/4))*B*(B^(ε/2)*B^(ε/2)) := by ring
        _ = _ := by rw [he]; ring

end

open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm cubeActiveSupport)
open ConcreteTraceCRT (eisEmbedding)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]


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


def globalFirstDivisorTarget (q : CubeCoordinates ι × Finset ι × Finset ι) : Ideal O :=
  (∏i∈q.2.1,Ideal.span {p i})*(∏i∈q.1.support,Ideal.span {p i})

theorem globalFirstDivisorTarget_ne_zero (q : CubeCoordinates ι × Finset ι × Finset ι) :
    globalFirstDivisorTarget p q≠0 := by
  apply mul_ne_zero <;> exact Finset.prod_ne_zero_iff.mpr (fun i hi => NeZero.ne (Ideal.span {p i}))


include hinj in
theorem primeSupport_inverse_sum (s : Finset (Finset ι)) (U : ℝ)
    (hs : ∀S∈s,primeProductNorm p S≤U) :
    (∑S∈s,1/primeProductNorm p S)≤128*Real.exp 1*(normLogBin U+1 : ℝ) := by
  let f := fun S : Finset ι => ∏i∈S,(Ideal.span {p i} : Ideal O)
  have hi : Function.Injective f := FirstCauchyArithmetic.family_product_injective _ hinj
  have he : (∑S∈s,1/primeProductNorm p S)=∑I∈s.image f,1/(Ideal.absNorm I : ℝ) := by
    rw [Finset.sum_image (fun S _ T _ h => hi h)]
    exact Finset.sum_congr rfl (fun S hS => by rw [primeProductNorm_eq_ideal_norm])
  rw [he]
  apply descent_ideal_inverse_sum
  · intro I hI
    obtain ⟨S,hS,rfl⟩ := Finset.mem_image.mp hI
    exact Finset.prod_ne_zero_iff.mpr (fun i hi => NeZero.ne (Ideal.span {p i}))
  · intro I hI
    obtain ⟨S,hS,rfl⟩ := Finset.mem_image.mp hI
    simpa only [f,←primeProductNorm_eq_ideal_norm] using hs S hS

end


end SecondPassArithmetic

end

end OAI

end


