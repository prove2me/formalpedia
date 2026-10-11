-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0049
-- name    : PNT_ZeroFree_433_0049
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-10T15:06:35.1164+00:00
-- url     : https://prove2.me/theorems/7e65c372-dd78-432b-9c0f-c932e5db2de4
-- title:
--   Zero-free region foundations: GaussSum.CompletedExpansion [0049]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.GaussSum.CompletedExpansion
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/GaussSum/CompletedExpansion.lean#L78-L676

import Definitions.Def_PNT_ZeroFree_433_0048

/- Supporting source modules for the zero-free-region proof.
Ported and checked against Lean 4.33.1 / Mathlib 0df444a.
Original source attribution:
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/GaussSum/CompletedExpansion.lean#L78-L676
-/

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

-- Source module: OAI.NumberTheory.DirichletL.GaussSum.CompletedExpansion
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

open scoped BigOperators Classical

namespace CompletedGauss

open ActualEisensteinCubic

def expandedTerm (Ψ : O →* ℂ) (W : ℝ → ℂ) (X : ℝ) (I H J : Ideal O) : ℂ :=
  (UniqueFactorizationMonoid.moebius H : ℂ) * cubeWeight Ψ (H * J) *
    (columnWeight Ψ I / (Real.sqrt (Ideal.absNorm I : ℝ) : ℂ) *
      Vstar W ((Ideal.absNorm I : ℝ) * (Ideal.absNorm H : ℝ) ^ 3 *
        (Ideal.absNorm J : ℝ) ^ 3 / X))

theorem finite_support_expandedTerm (Ψ : O →* ℂ) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (X : ℝ) (hX : 0 < X) :
    (Function.support (fun p : Ideal O × Ideal O × Ideal O =>
      expandedTerm Ψ W X p.1 p.2.1 p.2.2)).Finite := by
  apply finite_support_norm_triple W hW X hX
  · intro I H J hz
    rcases hz with rfl | rfl | rfl <;> simp [expandedTerm]
  · intro I H J hw
    simp [expandedTerm, Vstar, hw]

theorem expandedTerm_scale (Ψ : O →* ℂ) (W : ℝ → ℂ) (X : ℝ) (I H J : Ideal O) :
    (UniqueFactorizationMonoid.moebius H : ℂ) * cubeWeight Ψ H *
      summand Ψ W (X / (Ideal.absNorm H : ℝ) ^ 3) I J = expandedTerm Ψ W X I H J := by
  have harg : (Ideal.absNorm I : ℝ) * (Ideal.absNorm J : ℝ) ^ 3 /
      (X / (Ideal.absNorm H : ℝ) ^ 3) =
      (Ideal.absNorm I : ℝ) * (Ideal.absNorm H : ℝ) ^ 3 *
        (Ideal.absNorm J : ℝ) ^ 3 / X := by
    rw [div_div_eq_mul_div]
    ring
  simp only [summand, expandedTerm, harg, map_mul]
  ring

theorem expandedTerm_one (Ψ : O →* ℂ) (W : ℝ → ℂ) (X : ℝ) (I J : Ideal O) :
    expandedTerm Ψ W X I 1 J = summand Ψ W X I J := by
  simp only [expandedTerm, summand, UniqueFactorizationMonoid.moebius_one, Int.cast_one,
    one_mul, map_one, Nat.cast_one, one_pow, mul_one]
  ring

theorem completedT_finite_support (Ψ : O →* ℂ) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (X : ℝ) (hX : 0 < X) :
    (Function.support (fun p : Ideal O × Ideal O => summand Ψ W X p.1 p.2)).Finite := by
  have hf := finite_support_expandedTerm Ψ W hW X hX
  have hinj : Function.Injective (fun p : Ideal O × Ideal O => (p.1, (1 : Ideal O), p.2)) := by
    intro a b hab
    exact Prod.ext (Prod.mk.inj hab).1 (Prod.mk.inj (Prod.mk.inj hab).2).2
  have hp := Set.Finite.preimage hinj.injOn hf
  change (Function.support (fun p : Ideal O × Ideal O => expandedTerm Ψ W X p.1 1 p.2)).Finite at hp
  simpa only [expandedTerm_one] using hp

theorem completedT_summable (Ψ : O →* ℂ) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (X : ℝ) (hX : 0 < X) :
    Summable (fun p : Ideal O × Ideal O => summand Ψ W X p.1 p.2) :=
  summable_of_hasFiniteSupport (completedT_finite_support Ψ W hW X hX)

theorem weighted_completedT_reopen (Ψ : O →* ℂ) (W : ℝ → ℂ) (X : ℝ) (H : Ideal O) :
    (UniqueFactorizationMonoid.moebius H : ℂ) * cubeWeight Ψ H *
      completedT Ψ W (X / (Ideal.absNorm H : ℝ) ^ 3) =
      ∑' I : Ideal O, ∑' J : Ideal O, expandedTerm Ψ W X I H J := by
  simp only [completedT, ← tsum_mul_left, expandedTerm_scale]

theorem cube_inverse_finite_support (Ψ : O →* ℂ) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (X : ℝ) (hX : 0 < X) :
    (Function.support (fun H : Ideal O =>
      (UniqueFactorizationMonoid.moebius H : ℂ) * cubeWeight Ψ H *
        completedT Ψ W (X / (Ideal.absNorm H : ℝ) ^ 3))).Finite := by
  have hf := finite_support_expandedTerm Ψ W hW X hX
  apply (hf.image (fun p => p.2.1)).subset
  intro H hH
  by_contra hn
  have hzero : ∀ I J, expandedTerm Ψ W X I H J = 0 := by
    intro I J
    by_contra hz
    exact hn ⟨(I, H, J), hz, rfl⟩
  apply hH
  dsimp only
  rw [weighted_completedT_reopen]
  simp only [hzero, tsum_zero]

theorem cube_inner_inverse (Ψ : O →* ℂ) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (X : ℝ) (hX : 0 < X) (I : Ideal O) :
    (∑' H : Ideal O, ∑' J : Ideal O, expandedTerm Ψ W X I H J) =
      columnWeight Ψ I / (Real.sqrt (Ideal.absNorm I : ℝ) : ℂ) *
        Vstar W ((Ideal.absNorm I : ℝ) / X) := by
  let f : Ideal O → ℂ := fun B =>
    columnWeight Ψ I / (Real.sqrt (Ideal.absNorm I : ℝ) : ℂ) *
      Vstar W ((Ideal.absNorm I : ℝ) * (Ideal.absNorm B : ℝ) ^ 3 / X)
  have heq (H J : Ideal O) :
      (UniqueFactorizationMonoid.moebius H : ℂ) * cubeWeight Ψ (H * J) * f (H * J) =
        expandedTerm Ψ W X I H J := by
    simp only [f, expandedTerm, map_mul, Nat.cast_mul, mul_pow, mul_assoc]
  have hf := finite_support_expandedTerm Ψ W hW X hX
  have hp : (Function.support (fun p : Ideal O × Ideal O => expandedTerm Ψ W X I p.1 p.2)).Finite := by
    change ((fun p : Ideal O × Ideal O => (I, p)) ⁻¹'
      Function.support (fun p : Ideal O × Ideal O × Ideal O =>
        expandedTerm Ψ W X p.1 p.2.1 p.2.2)).Finite
    exact Set.Finite.preimage (fun a _ b _ hab => (Prod.mk.inj hab).2) hf
  have hgeneric := ideal_cube_convolution (cubeWeight Ψ) (cubeWeight_zero Ψ) f
    (by simpa only [heq] using hp)
  simpa only [heq, f, map_one, Nat.cast_one, one_pow, mul_one] using hgeneric

theorem completed_cube_inverse_vstar (Ψ : O →* ℂ) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (X : ℝ) (hX : 0 < X) :
    (∑' H : Ideal O, (UniqueFactorizationMonoid.moebius H : ℂ) * cubeWeight Ψ H *
      completedT Ψ W (X / (Ideal.absNorm H : ℝ) ^ 3)) =
    ∑' I : Ideal O, columnWeight Ψ I / (Real.sqrt (Ideal.absNorm I : ℝ) : ℂ) *
      Vstar W ((Ideal.absNorm I : ℝ) / X) := by
  let F : Ideal O × Ideal O × Ideal O → ℂ := fun p => expandedTerm Ψ W X p.1 p.2.1 p.2.2
  have hF : Summable F := summable_of_hasFiniteSupport (finite_support_expandedTerm Ψ W hW X hX)
  let e : (Ideal O × Ideal O × Ideal O) ≃ (Ideal O × Ideal O × Ideal O) := {
    toFun := fun p => (p.2.1, p.1, p.2.2)
    invFun := fun p => (p.2.1, p.1, p.2.2)
    left_inv := by rintro ⟨I, H, J⟩; rfl
    right_inv := by rintro ⟨I, H, J⟩; rfl }
  have hswap : Summable (fun p => F (e p)) := e.summable_iff.mpr hF
  calc
    _ = ∑' H : Ideal O, ∑' I : Ideal O, ∑' J : Ideal O, expandedTerm Ψ W X I H J := by
      simp only [completedT, ← tsum_mul_left, expandedTerm_scale]
    _ = ∑' p : Ideal O × Ideal O × Ideal O, F (e p) := by
      rw [hswap.tsum_prod]
      apply tsum_congr
      intro H
      exact (hswap.prod_factor H).tsum_prod.symm
    _ = ∑' p : Ideal O × Ideal O × Ideal O, F p := e.tsum_eq F
    _ = ∑' I : Ideal O, ∑' H : Ideal O, ∑' J : Ideal O, expandedTerm Ψ W X I H J := by
      rw [hF.tsum_prod]
      apply tsum_congr
      intro I
      exact (hF.prod_factor I).tsum_prod
    _ = _ := tsum_congr (cube_inner_inverse Ψ W hW X hX)

theorem vstar_source_normalization (Ψ : O →* ℂ) (W : ℝ → ℂ)
    (X : ℝ) (hX : 0 < X) (I : Ideal O) :
    columnWeight Ψ I / (Real.sqrt (Ideal.absNorm I : ℝ) : ℂ) *
      Vstar W ((Ideal.absNorm I : ℝ) / X) =
      (Real.sqrt X : ℂ)⁻¹ * columnWeight Ψ I * W ((Ideal.absNorm I : ℝ) / X) := by
  by_cases hI : I = 0
  · subst I; simp
  have hN : (0 : ℝ) < Ideal.absNorm I := lt_of_lt_of_le zero_lt_one (norm_at_least_one I hI)
  have hsN : (Real.sqrt (Ideal.absNorm I : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 hN).ne'
  have hsX : (Real.sqrt X : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.2 hX).ne'
  rw [Vstar, Real.sqrt_div hN.le, Complex.ofReal_div]
  field_simp

theorem completed_cube_inverse (Ψ : O →* ℂ) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (X : ℝ) (hX : 0 < X) :
    (Real.sqrt X : ℂ)⁻¹ *
      (∑' I : Ideal O, columnWeight Ψ I * W ((Ideal.absNorm I : ℝ) / X)) =
    ∑' H : Ideal O, (UniqueFactorizationMonoid.moebius H : ℂ) * cubeWeight Ψ H *
      completedT Ψ W (X / (Ideal.absNorm H : ℝ) ^ 3) := by
  rw [completed_cube_inverse_vstar Ψ W hW X hX, ← tsum_mul_left]
  apply tsum_congr
  intro I
  simpa only [mul_assoc] using (vstar_source_normalization Ψ W X hX I).symm

open ActualEisensteinCubic ConcreteTraceCRT

theorem normalizedFactors_product {ι : Type*} [Fintype ι]
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal] :
    UniqueFactorizationMonoid.normalizedFactors (Ideal.span {∏ i, p i}) =
      Finset.univ.val.map (fun i => Ideal.span {p i}) := by
  have hp (i : ι) : Prime (Ideal.span {p i}) :=
    Ideal.prime_of_isPrime (NeZero.ne _) inferInstance
  have h := UniqueFactorizationMonoid.normalizedFactors_prod_of_prime
    (m := Finset.univ.val.map (fun i => Ideal.span {p i})) (by
      intro P hP
      obtain ⟨i, _, rfl⟩ := Multiset.mem_map.mp hP
      exact hp i)
  rw [FiniteGaussPhase.span_finset_prod]
  exact h

theorem product_primary {ι : Type*} [Fintype ι] (p : ι → O)
    (hp : ∀ i, lambda ^ 2 ∣ p i - 1) : lambda ^ 2 ∣ (∏ i, p i) - 1 := by
  apply primary_multiset_prod (Finset.univ.val.map p)
  intro r hr
  obtain ⟨i, _, rfl⟩ := Multiset.mem_map.mp hr
  exact hp i

def productPrimeIndexEquiv {ι : Type*} [Fintype ι]
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i}))) :
    ι ≃ PrimeIndex (Ideal.span {∏ i, p i}) := by
  have hinj : Function.Injective (fun i => (Ideal.span {p i} : Ideal O)) := by
    intro i j hij
    by_contra hne
    have ht := (hcop hne).sup_eq
    rw [hij, sup_idem] at ht
    exact (inferInstance : (Ideal.span {p j}).IsMaximal).ne_top ht
  have hmem (i : ι) : (Ideal.span {p i} : Ideal O) ∈ primeSupport (Ideal.span {∏ i, p i}) := by
    rw [primeSupport, normalizedFactors_product]
    exact Multiset.mem_toFinset.mpr (Multiset.mem_map.mpr ⟨i, Finset.mem_univ _, rfl⟩)
  let f : ι → PrimeIndex (Ideal.span {∏ i, p i}) := fun i => ⟨Ideal.span {p i}, hmem i⟩
  apply Equiv.ofBijective f
  constructor
  · intro i j hij
    exact hinj (congrArg Subtype.val hij)
  · intro P
    have hm := Multiset.mem_toFinset.mp P.property
    rw [normalizedFactors_product] at hm
    obtain ⟨i, _, hi⟩ := Multiset.mem_map.mp hm
    exact ⟨i, Subtype.ext hi⟩

theorem cubicRow_product_mk {ι : Type*} [Fintype ι]
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hgood : ∀ i, lambda ∉ Ideal.span {p i})
    (hI : primaryGenerator (Ideal.span {∏ i, p i}) ≠ 0) (a : O) :
    cubicRow (Ideal.span {∏ i, p i}) hI (Ideal.Quotient.mk (Ideal.span {∏ i, p i}) a) =
      ∏ i, (canonicalSextic (Ideal.span {p i}) (hgood i) ^ 2)
        (Ideal.Quotient.mk (Ideal.span {p i}) a) := by
  rw [cubicRow_mk]
  symm
  exact (productPrimeIndexEquiv p hcop).prod_comp (fun P =>
    (canonicalSextic P.val (primeIndex_good _ hI P) ^ 2) (Ideal.Quotient.mk P.val a))

theorem gaussTwo_eq_canonicalProductGauss {ι : Type*} [Fintype ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hgood : ∀ i, lambda ∉ Ideal.span {p i})
    (hprimary : ∀ i, lambda ^ 2 ∣ p i - 1)
    (hI : primaryGenerator (Ideal.span {∏ i, p i}) ≠ 0) :
    gaussTwo (Ideal.span {∏ i, p i}) hI =
      FiniteGaussPhase.canonicalProductGauss p hp hcop hgood (fun _ => 2) := by
  have hpall : (∏ i, p i) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hp i)
  have hgen := primaryGenerator_span (∏ i, p i) hpall (product_primary p hprimary)
  let : Finite (O ⧸ Ideal.span {∏ i, p i}) := finite_quotient_span hpall
  let : Fintype (O ⧸ Ideal.span {∏ i, p i}) := Fintype.ofFinite _
  let : Finite (O ⧸ Ideal.span {primaryGenerator (Ideal.span {∏ i, p i})}) := finite_quotient_span hI
  let : Fintype (O ⧸ Ideal.span {primaryGenerator (Ideal.span {∏ i, p i})}) := Fintype.ofFinite _
  let e := Ideal.quotEquivOfEq (primaryGenerator_spec (Ideal.span {∏ i, p i}) hI).1
  have hsum :
      (∑ x : O ⧸ Ideal.span {primaryGenerator (Ideal.span {∏ i, p i})},
        cubicRow (Ideal.span {∏ i, p i}) hI (e x) *
          eisTraceModChar ShortDraftTrace.breveE ConcreteBreveE.breveE_period_coordinates
            (primaryGenerator (Ideal.span {∏ i, p i})) hI x) =
      (∑ x : O ⧸ Ideal.span {∏ i, p i},
        (∏ i, (canonicalSextic (Ideal.span {p i}) (hgood i) ^ 2)
          (FiniteGaussPhase.productElementCRT p hcop x i)) *
          eisTraceModChar ShortDraftTrace.breveE ConcreteBreveE.breveE_period_coordinates
            (∏ i, p i) hpall x) := by
    apply Fintype.sum_equiv e.toEquiv
    intro x
    change cubicRow (Ideal.span {∏ i, p i}) hI (e x) *
        eisTraceModChar ShortDraftTrace.breveE ConcreteBreveE.breveE_period_coordinates
          (primaryGenerator (Ideal.span {∏ i, p i})) hI x =
      (∏ i, (canonicalSextic (Ideal.span {p i}) (hgood i) ^ 2)
        (FiniteGaussPhase.productElementCRT p hcop (e x) i)) *
        eisTraceModChar ShortDraftTrace.breveE ConcreteBreveE.breveE_period_coordinates
          (∏ i, p i) hpall (e x)
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    simp only [e, Ideal.quotEquivOfEq_mk, cubicRow_product_mk p hcop hgood hI,
      FiniteGaussPhase.productElementCRT_mk, eisTraceModChar, IdealGaussCRT.traceModChar_mk, hgen]
  change _ / _ = _ / _
  rw [hsum, hgen]

theorem squarefreeGaussCoefficient_eq_canonicalProductCoefficient {ι : Type*} [Fintype ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hgood : ∀ i, lambda ∉ Ideal.span {p i})
    (hprimary : ∀ i, lambda ^ 2 ∣ p i - 1) :
    squarefreeGaussCoefficient (Ideal.span {∏ i, p i}) =
      FiniteGaussPhase.canonicalProductCoefficient p hp hcop hgood := by
  have hpall : (∏ i, p i) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hp i)
  have hgen := primaryGenerator_span (∏ i, p i) hpall (product_primary p hprimary)
  have hI : primaryGenerator (Ideal.span {∏ i, p i}) ≠ 0 := by rwa [hgen]
  have hsq : Squarefree (Ideal.span {∏ i, p i}) := by
    apply (UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors
      (Ideal.span_singleton_eq_bot.not.mpr hpall)).mpr
    rw [normalizedFactors_product]
    apply Multiset.Nodup.map
    · intro i j hij
      by_contra hne
      have ht := (hcop hne).sup_eq
      rw [hij, sup_idem] at ht
      exact (inferInstance : (Ideal.span {p j}).IsMaximal).ne_top ht
    · exact Finset.univ.nodup
  rw [squarefreeGaussCoefficient_eq _ hsq hI,
    gaussTwo_eq_canonicalProductGauss p hp hcop hgood hprimary hI, hgen]
  rfl

end CompletedGauss

namespace FiniteRayExpansion

variable {R : Type*} [CommRing R] [Fintype R]
noncomputable local instance : Fintype (MulChar R ℂ) := Fintype.ofFinite _

def unitFourierCoeff (f : Rˣ → ℂ) (χ : MulChar R ℂ) : ℂ :=
  (∑ u : Rˣ, f u * star (χ (u : R))) / (Fintype.card Rˣ : ℂ)

theorem unit_fourier_inversion (f : Rˣ → ℂ) (v : Rˣ) :
    (∑ χ : MulChar R ℂ, unitFourierCoeff f χ * χ (v : R)) = f v := by
  have hN : (Fintype.card Rˣ : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp_rw [unitFourierCoeff, div_mul_eq_mul_div, Finset.sum_mul, mul_assoc]
  rw [← Finset.sum_div, Finset.sum_comm]
  simp_rw [← Finset.mul_sum, FiniteRingSieve.unit_char_orthogonal]
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  exact mul_div_cancel_right₀ (f v) hN

theorem norm_char_unit (χ : MulChar R ℂ) (u : Rˣ) : ‖χ (u : R)‖ = 1 := by
  simpa only [MulChar.coe_equivToUnitHom] using
    Complex.norm_eq_one_of_mem_rootsOfUnity (χ.apply_mem_rootsOfUnity u)

theorem norm_char_le_one (χ : MulChar R ℂ) (r : R) : ‖χ r‖ ≤ 1 := by
  by_cases hr : IsUnit r
  · obtain ⟨u, rfl⟩ := hr
    exact (norm_char_unit χ u).le
  · rw [MulChar.map_nonunit χ hr, norm_zero]
    norm_num

theorem unitFourierCoeff_norm_le_average (f : Rˣ → ℂ) (χ : MulChar R ℂ) :
    ‖unitFourierCoeff f χ‖ ≤ (∑ u : Rˣ, ‖f u‖) / (Fintype.card Rˣ : ℝ) := by
  rw [unitFourierCoeff, norm_div, Complex.norm_natCast]
  apply div_le_div_of_nonneg_right _ (by positivity)
  calc
    _ ≤ ∑ u : Rˣ, ‖f u * star (χ (u : R))‖ := norm_sum_le _ _
    _ = _ := by simp only [norm_mul, norm_star, norm_char_unit, mul_one]

theorem unitFourierCoeff_norm_le (f : Rˣ → ℂ) (B : ℝ)
    (hf : ∀ u, ‖f u‖ ≤ B) (χ : MulChar R ℂ) : ‖unitFourierCoeff f χ‖ ≤ B := by
  have hN : (Fintype.card Rˣ : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  calc
    _ ≤ (∑ u : Rˣ, ‖f u‖) / (Fintype.card Rˣ : ℝ) := unitFourierCoeff_norm_le_average f χ
    _ ≤ (∑ _u : Rˣ, B) / (Fintype.card Rˣ : ℝ) :=
      div_le_div_of_nonneg_right (Finset.sum_le_sum (fun u _ => hf u)) (by positivity)
    _ = B := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; field_simp

theorem character_card_eq_units : Fintype.card (MulChar R ℂ) = Fintype.card Rˣ := by
  simpa only [Nat.card_eq_fintype_card] using
    MulChar.card_eq_card_units_of_hasEnoughRootsOfUnity R ℂ

theorem unitFourierCoeff_sum_norm_le (f : Rˣ → ℂ) (B : ℝ)
    (hf : ∀ u, ‖f u‖ ≤ B) :
    (∑ χ : MulChar R ℂ, ‖unitFourierCoeff f χ‖) ≤ (Fintype.card Rˣ : ℝ) * B := by
  calc
    _ ≤ ∑ _χ : MulChar R ℂ, B :=
      Finset.sum_le_sum (fun χ _ => unitFourierCoeff_norm_le f B hf χ)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, character_card_eq_units]

theorem unitFourierCoeff_sum_norm_le_sum (f : Rˣ → ℂ) :
    (∑ χ : MulChar R ℂ, ‖unitFourierCoeff f χ‖) ≤ ∑ u : Rˣ, ‖f u‖ := by
  have hN : (Fintype.card Rˣ : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  calc
    _ ≤ ∑ _χ : MulChar R ℂ, (∑ u : Rˣ, ‖f u‖) / (Fintype.card Rˣ : ℝ) :=
      Finset.sum_le_sum (fun χ _ => unitFourierCoeff_norm_le_average f χ)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, character_card_eq_units]
      field_simp

def zeroExtendUnits (f : Rˣ → ℂ) (r : R) : ℂ :=
  if hr : IsUnit r then f hr.unit else 0

@[simp] theorem zeroExtendUnits_unit (f : Rˣ → ℂ) (u : Rˣ) :
    zeroExtendUnits f (u : R) = f u := by
  rw [zeroExtendUnits, dif_pos u.isUnit]
  congr 1
  exact Units.ext u.isUnit.unit_spec

@[simp] theorem zeroExtendUnits_nonunit (f : Rˣ → ℂ) (r : R) (hr : ¬ IsUnit r) :
    zeroExtendUnits f r = 0 := dif_neg hr

theorem zeroExtendUnits_fourier (f : Rˣ → ℂ) (r : R) :
    zeroExtendUnits f r = ∑ χ : MulChar R ℂ, unitFourierCoeff f χ * χ r := by
  by_cases hr : IsUnit r
  · obtain ⟨u, rfl⟩ := hr
    rw [zeroExtendUnits_unit]
    exact (unit_fourier_inversion f u).symm
  · rw [zeroExtendUnits_nonunit f r hr]
    simp only [MulChar.map_nonunit _ hr, mul_zero, Finset.sum_const_zero]

theorem zeroExtendUnits_restrict (f : R → ℂ) (r : R) :
    zeroExtendUnits (fun u : Rˣ => f (u : R)) r = (if IsUnit r then 1 else 0) * f r := by
  by_cases hr : IsUnit r
  · obtain ⟨u, rfl⟩ := hr
    simp only [zeroExtendUnits_unit, u.isUnit, ite_true, one_mul]
  · simp only [zeroExtendUnits_nonunit _ _ hr, hr, ite_false, zero_mul]

def unitTensorCoeff (f : Rˣ → Rˣ → ℂ) (χ η : MulChar R ℂ) : ℂ :=
  unitFourierCoeff (fun u => unitFourierCoeff (f u) η) χ

theorem unit_tensor_fourier_inversion (f : Rˣ → Rˣ → ℂ) (u v : Rˣ) :
    (∑ χ : MulChar R ℂ, ∑ η : MulChar R ℂ,
      unitTensorCoeff f χ η * χ (u : R) * η (v : R)) = f u v := by
  calc
    _ = ∑ η : MulChar R ℂ,
        (∑ χ : MulChar R ℂ, unitTensorCoeff f χ η * χ (u : R)) * η (v : R) := by
      rw [Finset.sum_comm]
      simp only [Finset.sum_mul]
    _ = ∑ η : MulChar R ℂ, unitFourierCoeff (f u) η * η (v : R) := by
      apply Finset.sum_congr rfl
      intro η _
      change (∑ χ : MulChar R ℂ,
        unitFourierCoeff (fun a => unitFourierCoeff (f a) η) χ * χ (u : R)) * η (v : R) = _
      rw [unit_fourier_inversion]
    _ = _ := unit_fourier_inversion (f u) v

theorem unitTensorCoeff_norm_le (f : Rˣ → Rˣ → ℂ) (B : ℝ)
    (hf : ∀ u v, ‖f u v‖ ≤ B) (χ η : MulChar R ℂ) :
    ‖unitTensorCoeff f χ η‖ ≤ B :=
  unitFourierCoeff_norm_le _ B (fun u => unitFourierCoeff_norm_le (f u) B (hf u) η) χ

theorem unitTensorCoeff_sum_norm_le (f : Rˣ → Rˣ → ℂ) (B : ℝ)
    (hf : ∀ u v, ‖f u v‖ ≤ B) :
    (∑ χ : MulChar R ℂ, ∑ η : MulChar R ℂ, ‖unitTensorCoeff f χ η‖) ≤
      (Fintype.card Rˣ : ℝ) ^ 2 * B := by
  calc
    _ ≤ ∑ _χ : MulChar R ℂ, ∑ _η : MulChar R ℂ, B :=
      Finset.sum_le_sum (fun χ _ => Finset.sum_le_sum (fun η _ => unitTensorCoeff_norm_le f B hf χ η))
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, character_card_eq_units]
      ring

theorem unitTensorCoeff_sum_norm_le_sum (f : Rˣ → Rˣ → ℂ) :
    (∑ χ : MulChar R ℂ, ∑ η : MulChar R ℂ, ‖unitTensorCoeff f χ η‖) ≤
      ∑ u : Rˣ, ∑ v : Rˣ, ‖f u v‖ := by
  rw [Finset.sum_comm]
  calc
    _ ≤ ∑ η : MulChar R ℂ, ∑ u : Rˣ, ‖unitFourierCoeff (f u) η‖ :=
      Finset.sum_le_sum (fun η _ => unitFourierCoeff_sum_norm_le_sum (fun u => unitFourierCoeff (f u) η))
    _ = ∑ u : Rˣ, ∑ η : MulChar R ℂ, ‖unitFourierCoeff (f u) η‖ := Finset.sum_comm
    _ ≤ _ := Finset.sum_le_sum (fun u _ => unitFourierCoeff_sum_norm_le_sum (f u))

def zeroExtendUnitPair (f : Rˣ → Rˣ → ℂ) (r s : R) : ℂ :=
  zeroExtendUnits (fun u => zeroExtendUnits (f u) s) r

theorem zeroExtendUnitPair_fourier (f : Rˣ → Rˣ → ℂ) (r s : R) :
    zeroExtendUnitPair f r s = ∑ χ : MulChar R ℂ, ∑ η : MulChar R ℂ,
      unitTensorCoeff f χ η * χ r * η s := by
  by_cases hr : IsUnit r
  · obtain ⟨u, rfl⟩ := hr
    by_cases hs : IsUnit s
    · obtain ⟨v, rfl⟩ := hs
      simp only [zeroExtendUnitPair, zeroExtendUnits_unit]
      exact (unit_tensor_fourier_inversion f u v).symm
    · simp only [zeroExtendUnitPair, zeroExtendUnits_unit, zeroExtendUnits_nonunit _ _ hs,
        MulChar.map_nonunit _ hs, mul_zero, Finset.sum_const_zero]
  · simp only [zeroExtendUnitPair, zeroExtendUnits_nonunit _ _ hr,
      MulChar.map_nonunit _ hr, mul_zero, zero_mul, Finset.sum_const_zero]

theorem zeroExtendUnitPair_restrict (f : R → R → ℂ) (r s : R) :
    zeroExtendUnitPair (fun u v : Rˣ => f (u : R) (v : R)) r s =
      (if IsUnit r then 1 else 0) * (if IsUnit s then 1 else 0) * f r s := by
  by_cases hr : IsUnit r
  · obtain ⟨u, rfl⟩ := hr
    simp only [zeroExtendUnitPair, zeroExtendUnits_unit, zeroExtendUnits_restrict,
      u.isUnit, ite_true, one_mul]
  · simp only [zeroExtendUnitPair, zeroExtendUnits_nonunit _ _ hr, hr, ite_false, zero_mul]

end FiniteRayExpansion

open scoped BigOperators Classical

namespace RayFourExpansion
abbrev O := ActualEisensteinCubic.O
open ActualEisensteinCubic ConcreteTraceCRT ActualEisensteinCoordinates QuadraticGaussRay
open FiniteRayExpansion

abbrev RayRing := O ⧸ Ideal.span {(4 : O)}

noncomputable instance rayRingFintype : Fintype RayRing := by
  letI : Finite RayRing := finite_quotient_span (by norm_num : (4 : O) ≠ 0)
  exact Fintype.ofFinite _

abbrev RayCharacter := MulChar RayRing ℂ
noncomputable instance rayCharacterFintype : Fintype RayCharacter := Fintype.ofFinite _

def rayCharacter (χ : RayCharacter) (a : O) : ℂ :=
  χ (Ideal.Quotient.mk (Ideal.span {(4 : O)}) a)

theorem rayCharacter_mul (χ : RayCharacter) (a b : O) :
    rayCharacter χ (a * b) = rayCharacter χ a * rayCharacter χ b := by
  simp only [rayCharacter, map_mul]

theorem rayCharacter_eq_of_mod_four (χ : RayCharacter) (a b : O) (h : (4 : O) ∣ a - b) :
    rayCharacter χ a = rayCharacter χ b := by
  unfold rayCharacter
  congr 1
  exact Ideal.Quotient.eq.mpr (Ideal.mem_span_singleton.mpr h)

def rayMask (a : O) : ℂ :=
  if IsUnit (Ideal.Quotient.mk (Ideal.span {(4 : O)}) a) then 1 else 0

theorem rayRing_card : Fintype.card RayRing = 16 := by
  have h := rational_modulus_card 4 (by decide)
  simpa only [Nat.card_eq_fintype_card, Nat.cast_ofNat, show (4 : ℕ) ^ 2 = 16 by decide] using h

theorem rayUnit_card_le : Fintype.card RayRingˣ ≤ 16 := by
  calc
    _ ≤ Fintype.card RayRing := Fintype.card_le_of_injective _ Units.val_injective
    _ = 16 := rayRing_card

theorem rayCharacter_card_le : Fintype.card RayCharacter ≤ 16 := by
  rw [character_card_eq_units]
  exact rayUnit_card_le

def phaseCoeff (f : RayRing → ℂ) (χ : RayCharacter) : ℂ :=
  unitFourierCoeff (fun u : RayRingˣ => f (u : RayRing)) χ

theorem phase_expansion (f : RayRing → ℂ) (a : O) :
    rayMask a * f (Ideal.Quotient.mk (Ideal.span {(4 : O)}) a) =
      ∑ χ : RayCharacter, phaseCoeff f χ * rayCharacter χ a := by
  rw [rayMask, ← zeroExtendUnits_restrict]
  exact zeroExtendUnits_fourier _ _

theorem phaseCoeff_norm_le (f : RayRing → ℂ) (B : ℝ)
    (hf : ∀ u : RayRingˣ, ‖f (u : RayRing)‖ ≤ B) (χ : RayCharacter) :
    ‖phaseCoeff f χ‖ ≤ B := unitFourierCoeff_norm_le _ B hf χ

theorem phaseCoeff_sum_norm_le (f : RayRing → ℂ) (B : ℝ)
    (hf : ∀ u : RayRingˣ, ‖f (u : RayRing)‖ ≤ B) :
    (∑ χ : RayCharacter, ‖phaseCoeff f χ‖) ≤ 16 * B := by
  have hB : 0 ≤ B := (norm_nonneg _).trans (hf 1)
  exact (unitFourierCoeff_sum_norm_le _ B hf).trans
    (mul_le_mul_of_nonneg_right (by exact_mod_cast rayUnit_card_le) hB)

def pairCoeff (f : RayRing → RayRing → ℂ) (χ η : RayCharacter) : ℂ :=
  unitTensorCoeff (fun u v : RayRingˣ => f (u : RayRing) (v : RayRing)) χ η

theorem pair_phase_expansion (f : RayRing → RayRing → ℂ) (a b : O) :
    rayMask a * rayMask b *
      f (Ideal.Quotient.mk (Ideal.span {(4 : O)}) a)
        (Ideal.Quotient.mk (Ideal.span {(4 : O)}) b) =
      ∑ χ : RayCharacter, ∑ η : RayCharacter,
        pairCoeff f χ η * rayCharacter χ a * rayCharacter η b := by
  rw [rayMask, rayMask, ← zeroExtendUnitPair_restrict]
  exact zeroExtendUnitPair_fourier _ _ _

theorem pairCoeff_norm_le (f : RayRing → RayRing → ℂ) (B : ℝ)
    (hf : ∀ u v : RayRingˣ, ‖f (u : RayRing) (v : RayRing)‖ ≤ B) (χ η : RayCharacter) :
    ‖pairCoeff f χ η‖ ≤ B := unitTensorCoeff_norm_le _ B hf χ η

theorem pairCoeff_sum_norm_le (f : RayRing → RayRing → ℂ) (B : ℝ)
    (hf : ∀ u v : RayRingˣ, ‖f (u : RayRing) (v : RayRing)‖ ≤ B) :
    (∑ χ : RayCharacter, ∑ η : RayCharacter, ‖pairCoeff f χ η‖) ≤ 256 * B := by
  have hB : 0 ≤ B := (norm_nonneg _).trans (hf 1 1)
  have hcard : (Fintype.card RayRingˣ : ℝ) ^ 2 ≤ 256 := by
    have h : (Fintype.card RayRingˣ : ℝ) ≤ 16 := by exact_mod_cast rayUnit_card_le
    nlinarith [Nat.cast_nonneg (α := ℝ) (Fintype.card RayRingˣ)]
  exact (unitTensorCoeff_sum_norm_le _ B hf).trans (mul_le_mul_of_nonneg_right hcard hB)

theorem quadraticRayValue_bounds (r : EisensteinEPrimaryPhase.Coord) :
    ‖quadraticRayValue r‖ ≤ 2 ∧ ‖(quadraticRayValue r)⁻¹‖ ≤ 1 := by
  rcases r with ⟨a, b⟩
  fin_cases a <;> fin_cases b <;>
    norm_num [quadraticRayValue, breveGaussianFourTerms_formula, zpow_neg,
      Complex.I_sq, Complex.I_pow_three, Complex.inv_I,
      ZMod.val] <;>
    ring_nf <;> norm_num [Complex.I_sq, Complex.inv_I]

theorem fixedGQuotientValue_norm_le_two (r : RayRing) : ‖fixedGQuotientValue r‖ ≤ 2 := by
  let : Fintype (O ⧸ cubicTwoIdeal) := Fintype.ofFinite _
  let χ : MulChar (O ⧸ cubicTwoIdeal) ℂ :=
    (cubicChar cubicTwoIdeal cubicTwoIdeal_good).ringHomComp eisEmbedding
  let x := Ideal.Quotient.mk cubicTwoIdeal (lift (residueQuotientFour r))
  have hc : ‖(χ x)⁻¹‖ ≤ 1 := by
    simpa only [MulChar.inv_apply_eq_inv'] using norm_char_le_one (χ⁻¹) x
  change ‖(χ x)⁻¹ * quadraticRayValue (residueQuotientFour r)‖ ≤ 2
  rw [norm_mul]
  calc
    _ ≤ 1 * 2 := mul_le_mul hc (quadraticRayValue_bounds _).1 (norm_nonneg _) (by norm_num)
    _ = 2 := by norm_num

def gCoeff : RayCharacter → ℂ := phaseCoeff fixedGQuotientValue

theorem gCoeff_norm_le_two (χ : RayCharacter) : ‖gCoeff χ‖ ≤ 2 :=
  phaseCoeff_norm_le _ 2 (fun u => fixedGQuotientValue_norm_le_two u) χ

theorem gCoeff_sum_norm_le : (∑ χ : RayCharacter, ‖gCoeff χ‖) ≤ 32 := by
  exact (phaseCoeff_sum_norm_le _ 2 (fun u => fixedGQuotientValue_norm_le_two u)).trans_eq (by norm_num)

theorem fixedG_character_expansion (a : O) :
    rayMask a * fixedGQuotientValue (Ideal.Quotient.mk (Ideal.span {(4 : O)}) a) =
      ∑ χ : RayCharacter, gCoeff χ * rayCharacter χ a := phase_expansion _ a

def crossQuotientPhase (r s : RayRing) : ℂ :=
  MixedCrossSeparation.quadraticRayPair (residueQuotientFour r) (residueQuotientFour s)

theorem crossQuotientPhase_norm_le_two (r s : RayRing) : ‖crossQuotientPhase r s‖ ≤ 2 := by
  unfold crossQuotientPhase MixedCrossSeparation.quadraticRayPair
  rw [div_eq_mul_inv, mul_inv_rev, norm_mul, norm_mul]
  calc
    _ ≤ 2 * (1 * 1) :=
      mul_le_mul (quadraticRayValue_bounds _).1
        (mul_le_mul (quadraticRayValue_bounds _).2 (quadraticRayValue_bounds _).2
          (norm_nonneg _) (by norm_num))
        (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (by norm_num)
    _ = 2 := by norm_num

def crossCoeff : RayCharacter → RayCharacter → ℂ := pairCoeff crossQuotientPhase

theorem crossCoeff_norm_le_two (χ η : RayCharacter) : ‖crossCoeff χ η‖ ≤ 2 :=
  pairCoeff_norm_le _ 2 (fun u v => crossQuotientPhase_norm_le_two u v) χ η

theorem crossCoeff_sum_norm_le :
    (∑ χ : RayCharacter, ∑ η : RayCharacter, ‖crossCoeff χ η‖) ≤ 512 := by
  exact (pairCoeff_sum_norm_le _ 2 (fun u v => crossQuotientPhase_norm_le_two u v)).trans_eq (by norm_num)

theorem quadraticRayPair_character_expansion (a b : O) :
    rayMask a * rayMask b * MixedCrossSeparation.quadraticRayPair (residue a) (residue b) =
      ∑ χ : RayCharacter, ∑ η : RayCharacter,
        crossCoeff χ η * rayCharacter χ a * rayCharacter η b := by
  simpa only [crossCoeff, crossQuotientPhase, residueQuotientFour_mk] using
    pair_phase_expansion crossQuotientPhase a b

end RayFourExpansion

end

end OAI

end


