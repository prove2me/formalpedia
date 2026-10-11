-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0037_1
-- name    : PNT_ZeroFree_433_0037_1
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-10T13:57:19.224988+00:00
-- url     : https://prove2.me/theorems/6eaa1206-a374-466e-91d0-218d6c25a18f
-- title:
--   Zero-free region foundations: GaussSum.SecondPoissonScale [0037_1]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.GaussSum.SecondPoissonScale
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/GaussSum/SecondPoissonScale.lean#L54-L483

import Definitions.Def_PNT_ZeroFree_433_0031

/- Supporting zero-free-region estimates, split at Lean command boundaries.
Uniquely named private helpers in the first part are promoted
so the remaining estimates can use them across the module boundary.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/GaussSum/SecondPoissonScale.lean
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

theorem second_prefactor_identity
    (Y qe qg qx₁ qx₂ Li : ℝ)
    (hqe : 0 < qe) (hqg : 0 < qg) (hqx₁ : 0 < qx₁)
    (hqx₂ : 0 < qx₂) (hLi : 0 < Li) :
    Y / (qe * Real.sqrt ((qx₁ / qg) * (qx₂ / qg))) =
      (Y * qg / (qe * Li)) * Real.sqrt (Li / qx₁) * Real.sqrt (Li / qx₂) := by
  have hs1 : Real.sqrt (qx₁ / qg) ≠ 0 := by
    exact ne_of_gt (Real.sqrt_pos.2 (div_pos hqx₁ hqg))
  have hs2 : Real.sqrt (qx₂ / qg) ≠ 0 := by
    exact ne_of_gt (Real.sqrt_pos.2 (div_pos hqx₂ hqg))
  have ht1 : Real.sqrt (Li / qx₁) ≠ 0 := by
    exact ne_of_gt (Real.sqrt_pos.2 (div_pos hLi hqx₁))
  have ht2 : Real.sqrt (Li / qx₂) ≠ 0 := by
    exact ne_of_gt (Real.sqrt_pos.2 (div_pos hLi hqx₂))
  have hqg0 : qg ≠ 0 := ne_of_gt hqg
  have hqe0 : qe ≠ 0 := ne_of_gt hqe
  have hLi0 : Li ≠ 0 := ne_of_gt hLi
  have hqx10 : qx₁ ≠ 0 := ne_of_gt hqx₁
  have hqx20 : qx₂ ≠ 0 := ne_of_gt hqx₂
  rw [Real.sqrt_mul (le_of_lt (div_pos hqx₁ hqg))]
  have ha : Real.sqrt (qx₁ / qg) * Real.sqrt (Li / qx₁) = Real.sqrt (Li / qg) := by
    rw [← Real.sqrt_mul (le_of_lt (div_pos hqx₁ hqg))]
    congr 1
    field_simp
  have hb : Real.sqrt (qx₂ / qg) * Real.sqrt (Li / qx₂) = Real.sqrt (Li / qg) := by
    rw [← Real.sqrt_mul (le_of_lt (div_pos hqx₂ hqg))]
    congr 1
    field_simp
  have hc : Real.sqrt (Li / qg) * Real.sqrt (Li / qg) = Li / qg := by
    simpa [pow_two] using Real.sq_sqrt (le_of_lt (div_pos hLi hqg))
  have hmain :
      Real.sqrt (Li / qx₁) * Real.sqrt (Li / qx₂) *
        (Real.sqrt (qx₁ / qg) * Real.sqrt (qx₂ / qg)) = Li / qg := by
    calc
      _ = (Real.sqrt (qx₁ / qg) * Real.sqrt (Li / qx₁)) *
          (Real.sqrt (qx₂ / qg) * Real.sqrt (Li / qx₂)) := by ring
      _ = Li / qg := by rw [ha, hb, hc]
  apply (div_eq_iff (mul_ne_zero hqe0 (mul_ne_zero hs1 hs2))).2
  calc
    Y = (Y * qg / (qe * Li)) * ((Li / qg) * qe) := by field_simp
    _ = ((Y * qg / (qe * Li)) * Real.sqrt (Li / qx₁) * Real.sqrt (Li / qx₂)) *
          (qe * (Real.sqrt (qx₁ / qg) * Real.sqrt (qx₂ / qg))) := by
       rw [← hmain]
       ring

namespace ActualEisensteinCubic

section

open scoped ComplexConjugate

theorem canonicalSextic_conj_as_row_label
    (P : Ideal O) [P.IsMaximal] (hgood : lambda ∉ P) (e : O) :
    star (canonicalSextic P hgood (Ideal.Quotient.mk P e)) =
      canonicalSextic P hgood (Ideal.Quotient.mk P e) *
        (canonicalSextic P hgood (Ideal.Quotient.mk P e)) ^ 4 := by
  let χ := canonicalSextic P hgood
  let x : O ⧸ P := Ideal.Quotient.mk P e
  have hconj : star (χ x) = (χ x)⁻¹ := by
    by_cases hx : IsUnit x
    · let u : (O ⧸ P)ˣ := hx.unit
      have hu : (u : O ⧸ P) = x := hx.unit_spec
      rw [← hu]
      exact (canonicalSextic_inverse_eq_conj_on_units P hgood u).symm
    · have hzero : χ x = 0 := MulChar.map_nonunit χ hx
      simp [hzero]
  rw [hconj]
  by_cases hx : IsUnit x
  · have h6 : (χ x) ^ 6 = 1 := by
      rw [← MulChar.pow_apply' χ (by decide : 6 ≠ 0),
        canonicalSextic_pow_six P hgood]
      exact MulChar.one_apply hx
    apply inv_eq_of_mul_eq_one_right
    calc
      χ x * (χ x * (χ x) ^ 4) = (χ x) ^ 6 := by ring
      _ = 1 := h6
  · have hzero : χ x = 0 := MulChar.map_nonunit χ hx
    change (χ x)⁻¹ = χ x * (χ x) ^ 4
    simp [hzero]

theorem canonicalSextic_second_child
    (P : Ideal O) [P.IsMaximal] (hgood : lambda ∉ P)
    (d e k J C v : O) :
    star (canonicalSextic P hgood (Ideal.Quotient.mk P e)) *
      canonicalSextic P hgood (Ideal.Quotient.mk P d) *
      canonicalSextic P hgood (Ideal.Quotient.mk P k) *
      (canonicalSextic P hgood (Ideal.Quotient.mk P (J * C))) ^ 4 *
      (canonicalSextic P hgood (Ideal.Quotient.mk P v)) ^ 4 =
    canonicalSextic P hgood (Ideal.Quotient.mk P (d * e * k)) *
      (canonicalSextic P hgood (Ideal.Quotient.mk P (J * C * e * v))) ^ 4 := by
  rw [canonicalSextic_conj_as_row_label P hgood e]
  simp only [map_mul]
  ring

theorem finiteSquarefreeRow_mul
    {ι : Type*} (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hgood : ∀ i, lambda ∉ P i) (S : Finset ι) (a b : O) :
    finiteSquarefreeRow P hgood S (a * b) =
      finiteSquarefreeRow P hgood S a * finiteSquarefreeRow P hgood S b := by
  classical
  simp only [finiteSquarefreeRow, map_mul, Finset.prod_mul_distrib]

theorem finiteSquarefreeRow_conj_as_row_label
    {ι : Type*} (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hgood : ∀ i, lambda ∉ P i) (S : Finset ι) (e : O) :
    star (finiteSquarefreeRow P hgood S e) =
      finiteSquarefreeRow P hgood S e *
        (finiteSquarefreeRow P hgood S e) ^ 4 := by
  classical
  simp only [finiteSquarefreeRow, star_prod]
  rw [← Finset.prod_pow, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  exact canonicalSextic_conj_as_row_label (P i) (hgood i) e

theorem finiteSquarefreeRow_second_child
    {ι : Type*} (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hgood : ∀ i, lambda ∉ P i) (S : Finset ι)
    (d e k J C v : O) :
    star (finiteSquarefreeRow P hgood S e) *
      finiteSquarefreeRow P hgood S d *
      finiteSquarefreeRow P hgood S k *
      (finiteSquarefreeRow P hgood S (J * C)) ^ 4 *
      (finiteSquarefreeRow P hgood S v) ^ 4 =
    finiteSquarefreeRow P hgood S (d * e * k) *
      (finiteSquarefreeRow P hgood S (J * C * e * v)) ^ 4 := by
  rw [finiteSquarefreeRow_conj_as_row_label P hgood S e]
  simp only [finiteSquarefreeRow_mul]
  ring

end

noncomputable def rowCoprimeMask
    {ι : Type*} (P : ι → Ideal O) (S : Finset ι) (u : O) : ℂ := by
  classical
  exact if ∃ i ∈ S, u ∈ P i then 0 else 1

theorem finiteSquarefreeRow_self_pair
    {ι : Type*} (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hgood : ∀ i, (IsCyclotomicExtension.zeta_spec 3 ℚ K).toInteger - 1 ∉ P i)
    (S : Finset ι) (u : O) :
    star (finiteSquarefreeRow P hgood S u) * finiteSquarefreeRow P hgood S u =
      rowCoprimeMask P S u := by
  classical
  unfold finiteSquarefreeRow rowCoprimeMask
  rw [star_prod, ← Finset.prod_mul_distrib]
  by_cases h : ∃ i ∈ S, u ∈ P i
  · rw [if_pos h]
    obtain ⟨i, hi, hui⟩ := h
    apply Finset.prod_eq_zero hi
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hui, MulChar.map_zero]
    simp
  · rw [if_neg h]
    apply Finset.prod_eq_one
    intro i hi
    rw [MulChar.star_apply', ← MulChar.mul_apply, inv_mul_cancel]
    apply MulChar.one_apply
    let : Field (O ⧸ P i) := Ideal.Quotient.field (P i)
    exact isUnit_iff_ne_zero.mpr fun hui => h ⟨i, hi, Ideal.Quotient.eq_zero_iff_mem.mp hui⟩

theorem finiteSquarefreeRow_pair_kernel
    {ι : Type*} [DecidableEq ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hgood : ∀ i, (IsCyclotomicExtension.zeta_spec 3 ℚ K).toInteger - 1 ∉ P i)
    (S T : Finset ι) (u : O) :
    star (finiteSquarefreeRow P hgood S u) * finiteSquarefreeRow P hgood T u =
      rowCoprimeMask P (S ∩ T) u *
        star (finiteSquarefreeRow P hgood (S \ T) u) *
        finiteSquarefreeRow P hgood (T \ S) u := by
  have hsplit (A B : Finset ι) :
      finiteSquarefreeRow P hgood A u =
        finiteSquarefreeRow P hgood (A ∩ B) u *
        finiteSquarefreeRow P hgood (A \ B) u := by
    exact (Finset.prod_inter_mul_prod_sdiff A B _).symm
  rw [hsplit S T, hsplit T S, Finset.inter_comm T S, star_mul]
  calc
    _ = (star (finiteSquarefreeRow P hgood (S ∩ T) u) *
          finiteSquarefreeRow P hgood (S ∩ T) u) *
        star (finiteSquarefreeRow P hgood (S \ T) u) *
        finiteSquarefreeRow P hgood (T \ S) u := by ring
    _ = _ := by rw [finiteSquarefreeRow_self_pair]

 theorem mask_powerset {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (p : ι → Prop) [DecidablePred p] :
    (if ∃ i ∈ S, p i then (0 : ℂ) else 1) =
      ∑ E ∈ S.powerset, (-1 : ℂ) ^ E.card *
        if ∀ i ∈ E, p i then 1 else 0 := by
  have hprod : (if ∃ i ∈ S, p i then (0 : ℂ) else 1) =
      ∏ i ∈ S, (1 - if p i then (1 : ℂ) else 0) := by
    by_cases h : ∃ i ∈ S, p i
    · rw [if_pos h]
      obtain ⟨i, hi, hp⟩ := h
      symm
      apply Finset.prod_eq_zero hi
      simp [hp]
    · rw [if_neg h]
      symm
      apply Finset.prod_eq_one
      intro i hi
      simp [show ¬p i from fun hp => h ⟨i, hi, hp⟩]
  rw [hprod, Finset.prod_sub]
  apply Finset.sum_congr rfl
  intro E hE
  simp only [Finset.prod_const_one, mul_one]
  congr 1
  by_cases h : ∀ i ∈ E, p i
  · rw [if_pos h]
    apply Finset.prod_eq_one
    intro i hi
    simp [h i hi]
  · rw [if_neg h]
    push Not at h
    obtain ⟨i, hi, hp⟩ := h
    apply Finset.prod_eq_zero hi
    simp [hp]

theorem rowCoprimeMask_subsets
    {ι : Type*} [DecidableEq ι] (P : ι → Ideal O) (S : Finset ι) (u : O) :
    rowCoprimeMask P S u =
      ∑ E ∈ S.powerset, (-1 : ℂ) ^ E.card *
        if ∀ i ∈ E, u ∈ P i then 1 else 0 := by
  classical
  exact mask_powerset S (fun i => u ∈ P i)

theorem finiteSquarefreeRow_pair_sum_mobius
    {ι : Type*} [DecidableEq ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hgood : ∀ i, (IsCyclotomicExtension.zeta_spec 3 ℚ K).toInteger - 1 ∉ P i)
    (S T : Finset ι) (R : Finset O) (V : O → ℂ) :
    (∑ u ∈ R, V u * star (finiteSquarefreeRow P hgood S u) *
      finiteSquarefreeRow P hgood T u) =
      ∑ E ∈ (S ∩ T).powerset, (-1 : ℂ) ^ E.card *
        ∑ u ∈ R.filter (fun u => ∀ i ∈ E, u ∈ P i),
          V u * star (finiteSquarefreeRow P hgood (S \ T) u) *
            finiteSquarefreeRow P hgood (T \ S) u := by
  classical
  have hterm (u : O) :
      V u * star (finiteSquarefreeRow P hgood S u) *
          finiteSquarefreeRow P hgood T u =
        ∑ E ∈ (S ∩ T).powerset, (-1 : ℂ) ^ E.card *
          if ∀ i ∈ E, u ∈ P i then
            V u * star (finiteSquarefreeRow P hgood (S \ T) u) *
              finiteSquarefreeRow P hgood (T \ S) u else 0 := by
    rw [mul_assoc, finiteSquarefreeRow_pair_kernel, rowCoprimeMask_subsets]
    simp only [Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro E hE
    by_cases h : ∀ i ∈ E, u ∈ P i
    · simp only [if_pos h, mul_one]
      ring
    · simp only [if_neg h, mul_zero, zero_mul]
  simp_rw [hterm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro E hE
  rw [Finset.mul_sum, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro u hu
  by_cases h : ∀ i ∈ E, u ∈ P i <;> simp [h]

 theorem finite_energy_expand {α β : Type*}
    (R : Finset α) (C : Finset β) (V : α → ℂ) (a : β → ℂ)
    (r : β → α → ℂ) :
    (∑ u ∈ R, V u * (↑(‖∑ n ∈ C, a n * r n u‖ ^ 2) : ℂ)) =
      ∑ n ∈ C, ∑ m ∈ C, star (a n) * a m *
        ∑ u ∈ R, V u * star (r n u) * r m u := by
  have hnorm (u : α) :
      (↑(‖∑ n ∈ C, a n * r n u‖ ^ 2) : ℂ) =
        (∑ n ∈ C, star (a n) * star (r n u)) *
          (∑ m ∈ C, a m * r m u) := by
    rw [Complex.sq_norm, Complex.normSq_eq_conj_mul_self]
    simp only [map_sum, map_mul, starRingEnd_apply]
  simp_rw [hnorm]
  calc
    _ = ∑ u ∈ R, ∑ n ∈ C, ∑ m ∈ C,
        (star (a n) * a m) * (V u * star (r n u) * r m u) := by
      apply Finset.sum_congr rfl
      intro u hu
      simp only [Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro n hn
      apply Finset.sum_congr rfl
      intro m hm
      ring
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro n hn
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro m hm
      rw [Finset.mul_sum]

theorem finiteSquarefreeRow_mean_square_mobius
    {ι β : Type*} [DecidableEq ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hgood : ∀ i, (IsCyclotomicExtension.zeta_spec 3 ℚ K).toInteger - 1 ∉ P i)
    (C : Finset β) (support : β → Finset ι) (a : β → ℂ)
    (R : Finset O) (V : O → ℂ) :
    (∑ u ∈ R, V u * (↑(‖∑ n ∈ C,
      a n * finiteSquarefreeRow P hgood (support n) u‖ ^ 2) : ℂ)) =
      ∑ n ∈ C, ∑ m ∈ C, star (a n) * a m *
        ∑ E ∈ (support n ∩ support m).powerset, (-1 : ℂ) ^ E.card *
          ∑ u ∈ R.filter (fun u => ∀ i ∈ E, u ∈ P i),
            V u * star (finiteSquarefreeRow P hgood (support n \ support m) u) *
              finiteSquarefreeRow P hgood (support m \ support n) u := by
  rw [finite_energy_expand]
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.sum_congr rfl
  intro m hm
  congr 1
  exact finiteSquarefreeRow_pair_sum_mobius P hgood (support n) (support m) R V

theorem prime_product_moebius
    {ι : Type*} [DecidableEq ι] (P : ι → Ideal O)
    [∀ i, (P i).IsMaximal] (hprime : ∀ i, Prime (P i))
    (hinj : Function.Injective P) (S : Finset ι) :
    (UniqueFactorizationMonoid.moebius (∏ i ∈ S, P i) : ℂ) =
      (-1 : ℂ) ^ S.card := by
  induction S using Finset.induction_on with
  | empty => simp only [Finset.prod_empty, UniqueFactorizationMonoid.moebius_one, Int.cast_one, Finset.card_empty, pow_zero]
  | @insert i S hi ih =>
    have hcop : IsCoprime (P i) (∏ j ∈ S, P j) := by
      apply IsCoprime.prod_right
      intro j hj
      apply Ideal.isCoprime_of_isMaximal
      exact hinj.ne (by intro h; subst j; exact hi hj)
    rw [Finset.prod_insert hi, hcop.isRelPrime.moebius_mul,
      (hprime i).irreducible.moebius_eq, Int.cast_mul, Int.cast_neg,
      Int.cast_one, ih, Finset.card_insert_of_notMem hi, pow_succ]
    ring

theorem mem_prime_product_iff
    {ι : Type*} [DecidableEq ι] (P : ι → Ideal O)
    [∀ i, (P i).IsMaximal] (hinj : Function.Injective P)
    (S : Finset ι) (u : O) :
    u ∈ (∏ i ∈ S, P i) ↔ ∀ i ∈ S, u ∈ P i := by
  rw [Ideal.prod_eq_iInf_of_pairwise_isCoprime]
  · simp
  · intro i hi j hj hij
    exact Ideal.isCoprime_of_isMaximal (hinj.ne hij)

end ActualEisensteinCubic

namespace ConcretePrimeRowBridge

section

open ActualEisensteinCubic ShortDraftHeckeBridge
open scoped BigOperators Classical

noncomputable def primeSubsetProduct (F : Finset (Ideal O))
    (E : Finset (primePool F)) : Ideal O := ∏ i ∈ E, i.1

noncomputable def residualSexticRow
    (F : Finset (Ideal O)) (hFpos : ∀ I ∈ F, I ≠ ⊥)
    (hFgood : ∀ I ∈ F,
      ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I,
        goodLambda ∉ P)
    (I J : Ideal O) (u : O) : ℂ := by
  letI : ∀ i : primePool F, (i.1).IsMaximal := primePool_maximal F hFpos
  exact finiteSquarefreeRow (fun i : primePool F => i.1)
    (primePool_good F hFgood) (idealSupport F I \ idealSupport F J) u

theorem idealRowSum_mean_square_mobius
    (F : Finset (Ideal O)) (hFpos : ∀ I ∈ F, I ≠ ⊥)
    (hFgood : ∀ I ∈ F,
      ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I,
        goodLambda ∉ P)
    {q : ℕ} (χ : DirichletCharacter ℂ q) (W : ℕ → ℂ)
    (R : Finset O) (V : O → ℂ) :
    (∑ u ∈ R, V u * (↑(‖idealRowSum F hFpos hFgood χ W u‖ ^ 2) : ℂ)) =
      ∑ I ∈ F, ∑ J ∈ F,
        star (baseChangeWeight χ I * W (Ideal.absNorm I)) *
          (baseChangeWeight χ J * W (Ideal.absNorm J)) *
        ∑ E ∈ (idealSupport F I ∩ idealSupport F J).powerset,
          (UniqueFactorizationMonoid.moebius (primeSubsetProduct F E) : ℂ) *
          ∑ u ∈ R.filter (fun u => u ∈ primeSubsetProduct F E),
            V u * star (residualSexticRow F hFpos hFgood I J u) *
              residualSexticRow F hFpos hFgood J I u := by
  classical
  let : ∀ i : primePool F, (i.1).IsMaximal := primePool_maximal F hFpos
  have hprime (i : primePool F) : Prime i.1 := by
    obtain ⟨I, hIF, hi⟩ := mem_primePool_iff.mp i.property
    exact UniqueFactorizationMonoid.prime_of_normalized_factor i.1 hi
  change (∑ u ∈ R, V u * (↑(‖∑ I ∈ F,
    (baseChangeWeight χ I * W (Ideal.absNorm I)) *
      finiteSquarefreeRow (fun i : primePool F => i.1)
        (primePool_good F hFgood) (idealSupport F I) u‖ ^ 2) : ℂ)) = _
  erw [finiteSquarefreeRow_mean_square_mobius]
  apply Finset.sum_congr rfl
  intro I hI
  apply Finset.sum_congr rfl
  intro J hJ
  congr 1
  apply Finset.sum_congr rfl
  intro E hE
  rw [show (UniqueFactorizationMonoid.moebius (primeSubsetProduct F E) : ℂ) =
    (-1 : ℂ) ^ E.card from
      prime_product_moebius (fun i : primePool F => i.1)
        hprime Subtype.val_injective E]
  congr 1
  apply Finset.sum_congr
  · ext u
    simp only [Finset.mem_filter]
    exact and_congr_right fun hu =>
      (mem_prime_product_iff (fun i : primePool F => i.1)
        Subtype.val_injective E u).symm
  · intro u hu
    rfl

end

open ActualEisensteinCubic

theorem idealSupport_product_dvd
    (F : Finset (Ideal O)) (hFpos : ∀ I ∈ F, I ≠ ⊥)
    (I : Ideal O) (E : Finset (primePool F))
    (hE : E ⊆ idealSupport F I) :
    (∏ i ∈ E, i.1) ∣ I := by
  let : ∀ i : primePool F, (i.1).IsMaximal := primePool_maximal F hFpos
  apply Finset.prod_dvd_of_coprime
  · intro i hi j hj hij
    apply Ideal.isCoprime_of_isMaximal
    exact Subtype.val_injective.ne hij
  · intro i hi
    exact UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors
      ((mem_idealSupport_iff F I i).mp (hE hi))


end ConcretePrimeRowBridge

namespace EisensteinSchwartzPoisson
open MeasureTheory Filter LineDeriv
open scoped FourierTransform SchwartzMap Real RealInnerProductSpace


end EisensteinSchwartzPoisson

end

end OAI

end


