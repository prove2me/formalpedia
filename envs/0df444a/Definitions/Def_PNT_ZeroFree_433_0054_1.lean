-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0054_1
-- name    : PNT_ZeroFree_433_0054_1
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-10T15:31:57.224458+00:00
-- url     : https://prove2.me/theorems/eb2f0581-4205-406a-ba5e-4b332eede37e
-- title:
--   Zero-free region foundations: Arithmetic.SquarefreeDivisors [0054_1]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.Arithmetic.SquarefreeDivisors
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Arithmetic/SquarefreeDivisors.lean#L76-L372

import Definitions.Def_PNT_ZeroFree_433_0053

/- Supporting zero-free-region estimates, split at Lean command boundaries.
Uniquely named private helpers in the first part are promoted
so the remaining estimates can use them across the module boundary.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Arithmetic/SquarefreeDivisors.lean
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

namespace SquarefreeDivisorBound
open scoped BigOperators Classical
open Filter IdealMobiusDivisorSum

abbrev O := ActualEisensteinCubic.O

theorem squarefree_divisor_card_le (I : Ideal O) (hI : I ≠ ⊥) :
    ((idealDivisors I).filter Squarefree).card ≤ 2 ^ (primeSupport I).card := by
  rw [squarefree_divisors_eq_image I hI]
  exact Finset.card_image_le.trans_eq (Finset.card_powerset _)

theorem prime_support_subsets_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ I : Ideal O, I ≠ ⊥ →
      (2 : ℝ) ^ (primeSupport I).card ≤ C * (Ideal.absNorm I : ℝ) ^ ε := by
  have ht : Tendsto (fun n : ℕ => (n : ℝ) ^ ε) atTop atTop :=
    (tendsto_rpow_atTop hε).comp tendsto_natCast_atTop_atTop
  obtain ⟨N, hN⟩ := eventually_atTop.mp (ht.eventually (eventually_ge_atTop (2 : ℝ)))
  let small : Finset (Ideal O) :=
    (Ideal.finite_setOfPred_absNorm_le (S := O) N).toFinset
  refine ⟨(2 : ℝ) ^ small.card, by positivity, ?_⟩
  intro I hI
  let S := primeSupport I
  let A := S ∩ small
  let B := S \ small
  have hBS : B ⊆ primeSupport I := Finset.sdiff_subset
  have hlarge (P : Ideal O) (hP : P ∈ B) : (2 : ℝ) ≤ (Ideal.absNorm P : ℝ) ^ ε := by
    apply hN
    have hn : P ∉ small := (Finset.mem_sdiff.mp hP).2
    have hgt : N < Ideal.absNorm P := by
      apply Nat.lt_of_not_ge
      intro hp
      exact hn (by simpa [small] using hp)
    exact hgt.le
  have hpowB : (2 : ℝ) ^ B.card ≤ (Ideal.absNorm (∏ P ∈ B, P) : ℝ) ^ ε := by
    calc
      _ = ∏ P ∈ B, (2 : ℝ) := by simp
      _ ≤ ∏ P ∈ B, (Ideal.absNorm P : ℝ) ^ ε :=
        Finset.prod_le_prod (fun _ _ => by positivity) hlarge
      _ = (∏ P ∈ B, (Ideal.absNorm P : ℝ)) ^ ε :=
        (Real.finsetProd_rpow B (fun P => (Ideal.absNorm P : ℝ))
          (fun _ _ => by positivity) ε)
      _ = _ := by simp only [map_prod, Nat.cast_prod]
  have hNI : 0 < Ideal.absNorm I := Nat.pos_iff_ne_zero.mpr
    (fun h => hI (Ideal.absNorm_eq_zero_iff.mp h))
  have hnorm : Ideal.absNorm (∏ P ∈ B, P) ≤ Ideal.absNorm I :=
    Nat.le_of_dvd hNI (map_dvd Ideal.absNorm (support_product_dvd hI hBS))
  have hpowBI : (2 : ℝ) ^ B.card ≤ (Ideal.absNorm I : ℝ) ^ ε :=
    hpowB.trans (Real.rpow_le_rpow (by positivity) (by exact_mod_cast hnorm) hε.le)
  have hAc : A.card ≤ small.card := Finset.card_le_card Finset.inter_subset_right
  have hcard : S.card = A.card + B.card := by
    simp [A, B]
  change (2 : ℝ) ^ S.card ≤ _
  rw [hcard, pow_add]
  exact mul_le_mul (pow_le_pow_right₀ (by norm_num) hAc) hpowBI
    (by positivity) (by positivity)

theorem squarefree_divisor_small_power (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ I : Ideal O, I ≠ ⊥ →
      (((idealDivisors I).filter Squarefree).card : ℝ) ≤ C * (Ideal.absNorm I : ℝ) ^ ε := by
  obtain ⟨C, hC, h⟩ := prime_support_subsets_bound ε hε
  refine ⟨C, hC, fun I hI => ?_⟩
  have hc : (((idealDivisors I).filter Squarefree).card : ℝ) ≤
      (2 : ℝ) ^ (primeSupport I).card := by
    exact_mod_cast squarefree_divisor_card_le I hI
  exact hc.trans (h I hI)

open DescentWeightedCauchy

theorem first_element_squarefree_fiber
    (s : Finset (Ideal O × O)) (hs : ∀ x ∈ s, Squarefree x.1)
    (e y : O) (hy : y ≠ 0) :
    (s.filter (fun x => firstElementRowMap e x = y)).card ≤
      ((idealDivisors (Ideal.span {y})).filter Squarefree).card := by
  have hyI : (Ideal.span {y} : Ideal O) ≠ ⊥ := by
    intro h
    have hm : y ∈ (Ideal.span {y} : Ideal O) := Ideal.subset_span (by simp)
    rw [h] at hm
    exact hy hm
  apply Finset.card_le_card_of_injOn Prod.fst
  · intro x hx
    change x.1 ∈ (idealDivisors (Ideal.span {y})).filter Squarefree
    have hx' := Finset.mem_filter.mp hx
    apply Finset.mem_filter.mpr
    refine ⟨?_, hs x hx'.1⟩
    rw [mem_idealDivisors hyI, ← hx'.2]
    exact firstElementRowMap_label_dvd e x
  · intro x hx z hz hfst
    have hx' := (Finset.mem_filter.mp hx).2
    have hz' := (Finset.mem_filter.mp hz).2
    have hfac : ConcretePrimeRowBridge.idealGenerator x.1 ^ 2 * e ≠ 0 := by
      intro he
      apply hy
      rw [← hx']
      simp [firstElementRowMap, mul_assoc, he]
    apply Prod.ext hfst
    apply mul_right_cancel₀ hfac
    calc
      x.2 * (ConcretePrimeRowBridge.idealGenerator x.1 ^ 2 * e) = y := by
        simpa [firstElementRowMap, mul_assoc] using hx'
      _ = z.2 * (ConcretePrimeRowBridge.idealGenerator x.1 ^ 2 * e) := by
        simpa [firstElementRowMap, mul_assoc, hfst] using hz'.symm

theorem first_element_fiber_small_power (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (s : Finset (Ideal O × O)),
      (∀ x ∈ s, Squarefree x.1) → ∀ e y : O, y ≠ 0 →
      ((s.filter (fun x => firstElementRowMap e x = y)).card : ℝ) ≤
        C * (Ideal.absNorm (Ideal.span {y}) : ℝ) ^ ε := by
  obtain ⟨C, hC, h⟩ := squarefree_divisor_small_power ε hε
  refine ⟨C, hC, ?_⟩
  intro s hs e y hy
  have hyI : (Ideal.span {y} : Ideal O) ≠ ⊥ := by
    intro he
    have hm : y ∈ (Ideal.span {y} : Ideal O) := Ideal.subset_span (by simp)
    rw [he] at hm
    exact hy hm
  have hc : ((s.filter (fun x => firstElementRowMap e x = y)).card : ℝ) ≤
      (((idealDivisors (Ideal.span {y})).filter Squarefree).card : ℝ) := by
    exact_mod_cast first_element_squarefree_fiber s hs e y hy
  exact hc.trans (h _ hyI)

theorem first_element_energy_small_power (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (s : Finset (Ideal O × O)) (t : Finset O)
      (e : O) (w : Ideal O × O → ℂ) (P : O → ℂ) (B Y : ℝ),
      0 ≤ B → 0 ≤ Y → (∀ x ∈ s, Squarefree x.1) →
      (∀ x ∈ s, firstElementRowMap e x ∈ t) → (∀ y ∈ t, y ≠ 0) →
      (∀ y ∈ t, (Ideal.absNorm (Ideal.span {y}) : ℝ) ≤ Y) →
      (∀ x ∈ s, ‖w x‖ ≤ B) →
      (∑ x ∈ s, ‖w x‖ * ‖P (firstElementRowMap e x)‖ ^ 2) ≤
        B * C * Y ^ ε * ∑ y ∈ t, ‖P y‖ ^ 2 := by
  obtain ⟨C, hC, hc⟩ := first_element_fiber_small_power ε hε
  refine ⟨C, hC, ?_⟩
  intro s t e w P B Y hB hY hs hmap ht hnorm hw
  have hpush := bounded_energy_pushforward s t (firstElementRowMap e) w P B hmap hw
  apply hpush.trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro y hy
  have hcard := (hc s hs e y (ht y hy)).trans
    (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (by positivity) (hnorm y hy) hε.le) hC.le)
  have hterm := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hcard hB) (sq_nonneg ‖P y‖)
  simpa only [mul_assoc] using hterm

end SquarefreeDivisorBound

namespace VerticalContourShift
open MeasureTheory Filter Set
open scoped Topology

theorem horizontal_integral_tendsto_zero
    (f : ℂ → ℂ) (a b C : ℝ) (hab : a ≤ b)
    (hbound : ∀ σ ∈ Icc a b, ∀ t : ℝ,
      ‖f ((σ : ℂ) + t * Complex.I)‖ ≤ C / (1 + t ^ 2)) :
    Tendsto (fun t : ℝ => ∫ σ : ℝ in a..b, f ((σ : ℂ) + t * Complex.I))
      atTop (𝓝 0) := by
  have ht : Tendsto (fun t : ℝ => 1 + t ^ 2) atTop atTop :=
    tendsto_atTop_add_const_left atTop 1 (tendsto_pow_atTop (by decide : (2 : ℕ) ≠ 0))
  have hz : Tendsto (fun t : ℝ => C / (1 + t ^ 2) * |b - a|) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.div_atTop ht).mul_const |b - a|
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _) _ hz
  intro t
  apply intervalIntegral.norm_integral_le_of_norm_le_const
  intro σ hσ
  exact hbound σ (Ioc_subset_Icc_self (by simpa [uIoc_of_le hab] using hσ)) t

theorem integral_eq_of_strip_decay
    (f : ℂ → ℂ) (a b C : ℝ) (hab : a ≤ b)
    (hdiff : ∀ z : ℂ, a ≤ z.re → z.re ≤ b → DifferentiableAt ℂ f z)
    (ha : Integrable (fun t : ℝ => f ((a : ℂ) + t * Complex.I)))
    (hb : Integrable (fun t : ℝ => f ((b : ℂ) + t * Complex.I)))
    (hbound : ∀ σ ∈ Icc a b, ∀ t : ℝ,
      ‖f ((σ : ℂ) + t * Complex.I)‖ ≤ C / (1 + t ^ 2)) :
    (∫ t : ℝ, f ((a : ℂ) + t * Complex.I)) =
      ∫ t : ℝ, f ((b : ℂ) + t * Complex.I) := by
  let H (t : ℝ) : ℂ := ∫ σ : ℝ in a..b, f ((σ : ℂ) + t * Complex.I)
  let V (σ t : ℝ) : ℂ := ∫ u : ℝ in -t..t, f ((σ : ℂ) + u * Complex.I)
  have htop : Tendsto H atTop (𝓝 0) := horizontal_integral_tendsto_zero f a b C hab hbound
  have hbottom : Tendsto (fun t : ℝ => H (-t)) atTop (𝓝 0) := by
    let g (z : ℂ) := f (star z)
    have hg : ∀ σ ∈ Icc a b, ∀ t : ℝ,
        ‖g ((σ : ℂ) + t * Complex.I)‖ ≤ C / (1 + t ^ 2) := by
      intro σ hσ t
      simpa [g] using hbound σ hσ (-t)
    convert! horizontal_integral_tendsto_zero g a b C hab hg using 1 ;
      simp [g, H]
  have hVa : Tendsto (V a) atTop
      (𝓝 (∫ t : ℝ, f ((a : ℂ) + t * Complex.I))) :=
    intervalIntegral_tendsto_integral ha tendsto_neg_atTop_atBot tendsto_id
  have hVb : Tendsto (V b) atTop
      (𝓝 (∫ t : ℝ, f ((b : ℂ) + t * Complex.I))) :=
    intervalIntegral_tendsto_integral hb tendsto_neg_atTop_atBot tendsto_id
  have hrect (t : ℝ) : H (-t) - H t + Complex.I * V b t - Complex.I * V a t = 0 := by
    have hd : DifferentiableOn ℂ f
        (uIcc (((a : ℂ) - t * Complex.I).re) (((b : ℂ) + t * Complex.I).re) ×ℂ
         uIcc (((a : ℂ) - t * Complex.I).im) (((b : ℂ) + t * Complex.I).im)) := by
      intro z hz
      apply (hdiff z ?_ ?_).differentiableWithinAt
      · have hz' : z.re ∈ Icc a b := by
          simpa [uIcc_of_le hab] using hz.1
        exact hz'.1
      · have hz' : z.re ∈ Icc a b := by
          simpa [uIcc_of_le hab] using hz.1
        exact hz'.2
    have hr := Complex.integral_boundary_rect_eq_zero_of_differentiableOn f
      ((a : ℂ) - t * Complex.I) ((b : ℂ) + t * Complex.I) hd
    simpa [H, V, smul_eq_mul] using hr
  have hlim : Tendsto
      (fun t : ℝ => H (-t) - H t + Complex.I * V b t - Complex.I * V a t)
      atTop (𝓝 (0 - 0 + Complex.I * (∫ t : ℝ, f ((b : ℂ) + t * Complex.I)) -
        Complex.I * (∫ t : ℝ, f ((a : ℂ) + t * Complex.I)))) :=
    ((hbottom.sub htop).add (tendsto_const_nhds.mul hVb)).sub
      (tendsto_const_nhds.mul hVa)
  have heq : Complex.I * (∫ t : ℝ, f ((b : ℂ) + t * Complex.I)) -
      Complex.I * (∫ t : ℝ, f ((a : ℂ) + t * Complex.I)) = 0 := by
    have hzero : Tendsto (fun t : ℝ => H (-t) - H t + Complex.I * V b t - Complex.I * V a t)
        atTop (𝓝 0) := by
      simpa only [hrect] using (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℂ)) atTop (𝓝 0))
    simpa using tendsto_nhds_unique hlim hzero
  exact (mul_left_cancel₀ Complex.I_ne_zero (sub_eq_zero.mp heq)).symm

end VerticalContourShift

open scoped BigOperators Classical
namespace FirstPassCubeLabels
abbrev O := ActualEisensteinCubic.O
open ActualEisensteinCubic

def bit (b : Bool) : ℕ := if b then 1 else 0

def conductorExponent (parityBit ε₁ ε₂ : Bool) : ZMod 6 :=
  (bit ε₁ : ZMod 6) - (bit ε₂ : ZMod 6) + 3 * (bit parityBit : ZMod 6)

def crtExponent (side parityBit ε₁ ε₂ : Bool) : ℕ :=
  if conductorExponent parityBit ε₁ ε₂ = 0 then 0 else
    ((1 : ZMod 6) + if side then -conductorExponent parityBit ε₁ ε₂
      else conductorExponent parityBit ε₁ ε₂).val

def dilationExponent (parityBit ε₁ ε₂ : Bool) : ℕ :=
  if parityBit then bit ε₁ + bit ε₂ else 0

def retained (parityBit ε₁ ε₂ : Bool) : Bool := parityBit || (ε₁ && ε₂)

theorem exponent_table (side parityBit ε₁ ε₂ : Bool) :
    (4 * bit (if side then ε₂ else ε₁) + crtExponent side parityBit ε₁ ε₂ +
      dilationExponent parityBit ε₁ ε₂) % 6 = if retained parityBit ε₁ ε₂ then 4 else 0 := by
  cases side <;> cases parityBit <;> cases ε₁ <;> cases ε₂ <;> decide

section Rows
variable {ι : Type*} (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
  (hg : ∀ i, lambda ∉ P i) (S : Finset ι)

theorem row_pow (a : O) (m : ℕ) :
    finiteSquarefreeRow P hg S (a ^ m) = finiteSquarefreeRow P hg S a ^ m := by
  simp only [finiteSquarefreeRow, map_pow, Finset.prod_pow]

theorem row_prod {κ : Type*} (B : Finset κ) (a : κ → O) :
    finiteSquarefreeRow P hg S (∏ j ∈ B, a j) =
      ∏ j ∈ B, finiteSquarefreeRow P hg S (a j) := by
  classical
  induction B using Finset.induction_on with
  | empty => simp [finiteSquarefreeRow]
  | @insert j B hj ih =>
    simp only [Finset.prod_insert hj, finiteSquarefreeRow_mul, ih]

theorem row_sixth (a : O) :
    finiteSquarefreeRow P hg S a ^ 6 = rowCoprimeMask P S a := by
  rw [← row_pow, finiteSquarefreeRow_sixth_power]
  rfl

include hg

theorem mask_mul (a b : O) :
    rowCoprimeMask P S (a * b) = rowCoprimeMask P S a * rowCoprimeMask P S b := by
  simp only [← row_sixth P hg S, finiteSquarefreeRow_mul, mul_pow]

theorem mask_pow (a : O) (m : ℕ) :
    rowCoprimeMask P S (a ^ m) = rowCoprimeMask P S a ^ m := by
  rw [← row_sixth P hg S, row_pow, ← row_sixth P hg S]
  simp only [← pow_mul, Nat.mul_comm]

theorem mask_prod {κ : Type*} (B : Finset κ) (a : κ → O) :
    rowCoprimeMask P S (∏ j ∈ B, a j) = ∏ j ∈ B, rowCoprimeMask P S (a j) := by
  rw [← row_sixth P hg S, row_prod, ← Finset.prod_pow]
  simp only [row_sixth]

theorem row_zero_of_mask_zero (a : O) (h : rowCoprimeMask P S a = 0) :
    finiteSquarefreeRow P hg S a = 0 := by
  have hq := row_sixth P hg S a
  rw [h] at hq
  exact (pow_eq_zero_iff (by decide : (6 : ℕ) ≠ 0)).mp hq

theorem row_power_mul_mask_power (a : O) (k m : ℕ) (hk : 0 < k) :
    finiteSquarefreeRow P hg S a ^ k * rowCoprimeMask P S a ^ m =
      finiteSquarefreeRow P hg S a ^ k := by
  by_cases h : ∃ i ∈ S, a ∈ P i
  · have hm : rowCoprimeMask P S a = 0 := by simp [rowCoprimeMask, h]
    rw [row_zero_of_mask_zero P hg S a hm]
    simp [Nat.ne_of_gt hk]
  · simp [rowCoprimeMask, h]


end Rows


section Reassembly
variable {ι κ : Type*} (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
  (hg : ∀ i, lambda ∉ P i) (S : Finset ι)


end Reassembly


end FirstPassCubeLabels

open scoped BigOperators Classical SchwartzMap
namespace QuadraticInitialBound
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson
open FiniteGaussPhase MixedCrossSeparation ActualEisensteinCoordinates QuadraticGaussRay
open RayFourExpansion


end QuadraticInitialBound

end

end OAI

end


