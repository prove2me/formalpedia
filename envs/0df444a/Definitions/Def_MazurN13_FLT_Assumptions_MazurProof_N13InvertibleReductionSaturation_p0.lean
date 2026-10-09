-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13InvertibleReductionSaturation_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13InvertibleReductionSaturation_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-08T22:29:48.570624+00:00
-- url     : https://prove2.me/theorems/1ef7edb6-02d0-446e-902d-7a921680db09
-- title:
--   FLT.Assumptions.MazurProof.N13InvertibleReductionSaturation source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13InvertibleReductionSaturation

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13InvertibleReductionSaturation
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13QuadraticTwoChartSpreadSaturation_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13IntegralInfinityReduction_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13SpecialDivisorCharts_p0

set_option autoImplicit false




/-!
Source pin: 887d29cd9eb9b60a6e5ec438ff919a74ccda41e5.
New source candidate for the integral principal-comparison seam.
Lean compilation and axiom checks: NOT RUN.

An invertible ideal with nonzero image in a domain-valued reduction is
saturated by the generator of the reduction kernel. This is a genuine
descent lemma; it assumes no Picard comparison or specialization law.
-/

namespace MazurProof.N13InvertibleReductionSaturation

noncomputable section
open scoped nonZeroDivisors

section General

variable {A K S : Type*} [CommRing A] [IsDomain A] [Field K]
  [Algebra A K] [IsFractionRing A K] [CommRing S] [IsDomain S]

/-- Invertibility lets us test membership after multiplication by every
inverse-ideal section. Reduction modulo the kernel generator cancels the
nonzero reduction of one ideal section, and forces the apparent denominator
to divide. This removes one vertical factor. -/
theorem kernel_generator_saturated
    (red : A →+* S) (p : A) (hp : p ≠ 0)
    (hker : RingHom.ker red = Ideal.span ({p} : Set A))
    (I : Ideal A) (hI : IsUnit (I : FractionalIdeal A⁰ K))
    (hred : Ideal.map red I ≠ ⊥) :
    ∀ x : A, p * x ∈ I → x ∈ I := by
  classical
  have hex : ∃ a : A, a ∈ I ∧ red a ≠ 0 := by
    by_contra h
    push_neg at h
    apply hred
    apply (Ideal.map_eq_bot_iff_le_ker red).mpr
    intro a ha
    exact RingHom.mem_ker.mpr (h a ha)
  obtain ⟨a, ha, hared⟩ := hex
  have hpred : red p = 0 := by
    apply RingHom.mem_ker.mp
    rw [hker]
    exact Ideal.subset_span (Set.mem_singleton p)
  let U : (FractionalIdeal A⁰ K)ˣ := hI.unit
  have hU : (U : FractionalIdeal A⁰ K) = (I : FractionalIdeal A⁰ K) := hI.unit_spec
  have hUI : (↑U⁻¹ : FractionalIdeal A⁰ K) * (I : FractionalIdeal A⁰ K) = 1 := by
    rw [← hU]
    exact Units.inv_mul U
  have hIU : (I : FractionalIdeal A⁰ K) * (↑U⁻¹ : FractionalIdeal A⁰ K) = 1 := by
    rw [← hU]
    exact Units.mul_inv U
  intro x hpx
  have hInvSpan :
      (↑U⁻¹ : FractionalIdeal A⁰ K) *
        FractionalIdeal.spanSingleton A⁰ (algebraMap A K x) ≤ 1 := by
    rw [mul_comm, FractionalIdeal.spanSingleton_mul_le_iff]
    intro z hz
    have hcz : z * algebraMap A K (p * x) ∈ (1 : FractionalIdeal A⁰ K) := by
      rw [← hUI]
      exact FractionalIdeal.mul_mem_mul hz (FractionalIdeal.mem_coeIdeal_of_mem A⁰ hpx)
    have hdz : z * algebraMap A K a ∈ (1 : FractionalIdeal A⁰ K) := by
      rw [← hUI]
      exact FractionalIdeal.mul_mem_mul hz (FractionalIdeal.mem_coeIdeal_of_mem A⁰ ha)
    have hcTop : z * algebraMap A K (p * x) ∈ ((⊤ : Ideal A) : FractionalIdeal A⁰ K) := by
      simpa using hcz
    have hdTop : z * algebraMap A K a ∈ ((⊤ : Ideal A) : FractionalIdeal A⁰ K) := by
      simpa using hdz
    obtain ⟨c, _, hc⟩ := (FractionalIdeal.mem_coeIdeal A⁰).mp hcTop
    obtain ⟨d, _, hd⟩ := (FractionalIdeal.mem_coeIdeal A⁰).mp hdTop
    have hpc : p * (d * x) = a * c := by
      apply IsFractionRing.injective A K
      simp only [map_mul]
      rw [hc, hd, map_mul]
      ring
    have hcRed : red c = 0 := by
      have heq := congrArg red hpc
      have hz' : red a * red c = 0 := by
        simpa only [map_mul, hpred, zero_mul] using heq.symm
      exact (mul_eq_zero.mp hz').resolve_left hared
    have hcDiv : p ∣ c := by
      have hcKer : c ∈ RingHom.ker red := RingHom.mem_ker.mpr hcRed
      rwa [hker, Ideal.mem_span_singleton] at hcKer
    obtain ⟨e, he⟩ := hcDiv
    have hpK : algebraMap A K p ≠ 0 := by
      intro hz'
      apply hp
      apply IsFractionRing.injective A K
      simpa using hz'
    have hzx : z * algebraMap A K x = algebraMap A K e := by
      apply mul_left_cancel₀ hpK
      calc
        algebraMap A K p * (z * algebraMap A K x) = algebraMap A K c := by
          rw [hc, map_mul]
          ring
        _ = algebraMap A K p * algebraMap A K e := by rw [he, map_mul]
    have heOne : algebraMap A K e ∈ (1 : FractionalIdeal A⁰ K) := by
      simpa using (FractionalIdeal.mem_coeIdeal_of_mem A⁰
        (show e ∈ (⊤ : Ideal A) from Ideal.mem_top))
    rw [mul_comm, hzx]
    exact heOne
  have hspan : FractionalIdeal.spanSingleton A⁰ (algebraMap A K x) ≤
      (I : FractionalIdeal A⁰ K) := by
    calc
      FractionalIdeal.spanSingleton A⁰ (algebraMap A K x) =
          ((I : FractionalIdeal A⁰ K) * (↑U⁻¹ : FractionalIdeal A⁰ K)) *
            FractionalIdeal.spanSingleton A⁰ (algebraMap A K x) := by rw [hIU, one_mul]
      _ = (I : FractionalIdeal A⁰ K) *
          ((↑U⁻¹ : FractionalIdeal A⁰ K) *
            FractionalIdeal.spanSingleton A⁰ (algebraMap A K x)) := by rw [mul_assoc]
      _ ≤ (I : FractionalIdeal A⁰ K) * 1 :=
        mul_le_mul_right hInvSpan (I : FractionalIdeal A⁰ K)
      _ = (I : FractionalIdeal A⁰ K) := mul_one _
  have hxFrac : algebraMap A K x ∈ (I : FractionalIdeal A⁰ K) :=
    hspan (FractionalIdeal.mem_spanSingleton_self A⁰ (algebraMap A K x))
  obtain ⟨b, hb, hbx⟩ := (FractionalIdeal.mem_coeIdeal A⁰).mp hxFrac
  have hbx' : b = x := (IsFractionRing.injective A K) hbx
  simpa [hbx'] using hb

theorem kernel_generator_pow_saturated
    (red : A →+* S) (p : A) (hp : p ≠ 0)
    (hker : RingHom.ker red = Ideal.span ({p} : Set A))
    (I : Ideal A) (hI : IsUnit (I : FractionalIdeal A⁰ K))
    (hred : Ideal.map red I ≠ ⊥) (n : ℕ) :
    ∀ x : A, p ^ n * x ∈ I → x ∈ I := by
  induction n with
  | zero =>
    intro x hx
    simpa using hx
  | succ n ih =>
    intro x hx
    apply ih x
    apply kernel_generator_saturated red p hp hker I hI hred
    simpa only [pow_succ', mul_assoc] using hx

/-- Equality after inverting the vertical parameter descends for invertible
ideals whose reductions are nonzero. No choice of divisor representative
or Picard quotient occurs in this statement. -/
theorem eq_of_map_eq_after_inverting_kernel_generator
    {T : Type*} [CommRing T] [Algebra A T]
    (red : A →+* S) (p : A) (hp : p ≠ 0)
    [IsLocalization (Submonoid.powers p) T]
    (hker : RingHom.ker red = Ideal.span ({p} : Set A))
    (I J : Ideal A)
    (hI : IsUnit (I : FractionalIdeal A⁰ K))
    (hJ : IsUnit (J : FractionalIdeal A⁰ K))
    (hIr : Ideal.map red I ≠ ⊥) (hJr : Ideal.map red J ≠ ⊥)
    (hmap : Ideal.map (algebraMap A T) I = Ideal.map (algebraMap A T) J) : I = J := by
  have descend (U V : Ideal A)
      (hV : IsUnit (V : FractionalIdeal A⁰ K))
      (hVr : Ideal.map red V ≠ ⊥)
      (hm : Ideal.map (algebraMap A T) U = Ideal.map (algebraMap A T) V) : U ≤ V := by
    intro x hx
    have hxmap := Ideal.mem_map_of_mem (algebraMap A T) hx
    rw [hm, IsLocalization.algebraMap_mem_map_algebraMap_iff (Submonoid.powers p)] at hxmap
    obtain ⟨q, hq, hqx⟩ := hxmap
    obtain ⟨n, rfl⟩ := hq
    exact kernel_generator_pow_saturated red p hp hker V hV hVr n x hqx
  exact le_antisymm (descend I J hJ hJr hmap) (descend J I hI hIr hmap.symm)

private theorem coe_principal_isUnit (a : A) (ha : a ≠ 0) :
    IsUnit ((Ideal.span ({a} : Set A) : Ideal A) : FractionalIdeal A⁰ K) := by
  refine ⟨Units.mkOfMulEqOne
    ((Ideal.span ({a} : Set A) : Ideal A) : FractionalIdeal A⁰ K)
    (((Ideal.span ({a} : Set A) : Ideal A) : FractionalIdeal A⁰ K)⁻¹) ?_, rfl⟩
  exact FractionalIdeal.coe_ideal_span_singleton_mul_inv K ha

private theorem map_principal_mul_ne_bot
    (red : A →+* S) (a : A) (ha : red a ≠ 0)
    (I : Ideal A) (hI : Ideal.map red I ≠ ⊥) :
    Ideal.map red (Ideal.span ({a} : Set A) * I) ≠ ⊥ := by
  rw [Ideal.map_mul, Ideal.map_span, Set.image_singleton]
  intro h
  rcases Ideal.mul_eq_bot.mp h with hspan | hI'
  · have hm : red a ∈ Ideal.span ({red a} : Set S) :=
      Ideal.subset_span (Set.mem_singleton (red a))
    rw [hspan, Ideal.mem_bot] at hm
    exact ha hm
  · exact hI hI'

/-- A denominator-cleared generic principal equation already descends to
the integral chart once both presentations have nonzero reductions.
The missing global step is to construct such a common presentation and
establish the generic equation on both charts. -/
theorem cleared_eq_of_generic_eq
    {T : Type*} [CommRing T] [Algebra A T]
    (red : A →+* S) (p : A) (hp : p ≠ 0)
    [IsLocalization (Submonoid.powers p) T]
    (hker : RingHom.ker red = Ideal.span ({p} : Set A))
    (a b : A) (ha : red a ≠ 0) (hb : red b ≠ 0)
    (I J : Ideal A)
    (hI : IsUnit (I : FractionalIdeal A⁰ K))
    (hJ : IsUnit (J : FractionalIdeal A⁰ K))
    (hIr : Ideal.map red I ≠ ⊥) (hJr : Ideal.map red J ≠ ⊥)
    (hg : Ideal.map (algebraMap A T) (Ideal.span ({a} : Set A) * I) =
      Ideal.map (algebraMap A T) (Ideal.span ({b} : Set A) * J)) :
    Ideal.span ({a} : Set A) * I = Ideal.span ({b} : Set A) * J := by
  have ha0 : a ≠ 0 := fun h => ha (by simp [h])
  have hb0 : b ≠ 0 := fun h => hb (by simp [h])
  apply eq_of_map_eq_after_inverting_kernel_generator (K := K) red p hp hker _ _ _ _
    (map_principal_mul_ne_bot red a ha I hIr)
    (map_principal_mul_ne_bot red b hb J hJr) hg
  · rw [FractionalIdeal.coeIdeal_mul]
    exact (coe_principal_isUnit (K := K) a ha0).mul hI
  · rw [FractionalIdeal.coeIdeal_mul]
    exact (coe_principal_isUnit (K := K) b hb0).mul hJ

end General

section TwoAdic

local instance instFactPrimeOfNatNat_fLT : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

abbrev R₂ := N13IntegralModelContraction.R₂

variable {A K S : Type*} [CommRing A] [IsDomain A] [Field K]
  [Algebra A K] [IsFractionRing A K] [Algebra R₂ A]
  [CommRing S] [IsDomain S]

/-- Unit-times-power decomposition in Z2 extends one-factor saturation to
cancellation of every nonzero base scalar. -/
theorem twoAdic_scalar_saturated_of_reduction_ne_bot
    (red : A →+* S)
    (h2 : algebraMap R₂ A (2 : R₂) ≠ 0)
    (hker : RingHom.ker red = Ideal.span ({algebraMap R₂ A (2 : R₂)} : Set A))
    (I : Ideal A) (hI : IsUnit (I : FractionalIdeal A⁰ K))
    (hred : Ideal.map red I ≠ ⊥) :
    ∀ r : R₂, r ≠ 0 → ∀ x : A, algebraMap R₂ A r * x ∈ I → x ∈ I := by
  intro r hr x hx
  have hu : IsUnit (algebraMap R₂ A (PadicInt.unitCoeff hr : R₂)) :=
    (PadicInt.unitCoeff hr).isUnit.map (algebraMap R₂ A)
  rw [PadicInt.unitCoeff_spec hr, map_mul, map_pow] at hx
  have hxpow : (algebraMap R₂ A (2 : R₂)) ^ r.valuation * x ∈ I := by
    apply (I.mul_unit_mem_iff_mem hu).mp
    simpa only [mul_assoc, mul_comm, mul_left_comm, RingHom.map_one,
      Int.cast_ofNat, Nat.cast_two] using hx
  exact kernel_generator_pow_saturated red _ h2 hker I hI hred r.valuation x hxpow

end TwoAdic

section InfinityApplication

open Polynomial
open scoped Sym2
local instance instFactPrimeOfNatNat_fLT_1 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

abbrev B := N13IntegralInfinityPointSpread.InfinityCurve
abbrev Bs := N13SpecialDivisorCharts.SpecialInfinity

theorem special_infinityPointIdeal_ne_bot (t v : N13GoodModelTwo.F2) :
    N13SpecialDivisorCharts.infinityPointIdeal t v ≠ ⊥ := by
  have hd : N13SpecialInfinityChart.curvePoly.degree ≠ 0 := by
    rw [degree_eq_natDegree N13SpecialInfinityChart.curvePoly_monic.ne_zero,
      N13SpecialInfinityChart.curvePoly_natDegree]
    norm_num
  have hn : N13SpecialInfinityChart.tClass -
      algebraMap N13GoodModelTwo.F2[X] Bs (C t) ≠ 0 := by
    change algebraMap N13GoodModelTwo.F2[X] Bs X -
      algebraMap N13GoodModelTwo.F2[X] Bs (C t) ≠ 0
    rw [← map_sub, ← map_zero (algebraMap N13GoodModelTwo.F2[X] Bs)]
    exact (AdjoinRoot.of.injective_of_degree_ne_zero hd).ne (monic_X_sub_C t).ne_zero
  intro hbot
  have hm : N13SpecialInfinityChart.tClass -
      algebraMap N13GoodModelTwo.F2[X] Bs (C t) ∈
      N13SpecialDivisorCharts.infinityPointIdeal t v :=
    Ideal.subset_span (by simp)
  rw [hbot, Ideal.mem_bot] at hm
  exact hn hm

theorem special_point_infinityIdeal_ne_bot (p : N13SpecialDivisorCharts.CurvePoint) :
    (N13SpecialDivisorCharts.point p).infinityIdeal ≠ ⊥ := by
  cases p with
  | inl p =>
    unfold N13SpecialDivisorCharts.point
    by_cases hx : p.1.1 = 0
    · simp [hx, N13SpecialDivisorCharts.affineZeroPoint]
    · simp only [hx, N13SpecialDivisorCharts.affineOnePoint]
      exact special_infinityPointIdeal_ne_bot _ _
  | inr p =>
    unfold N13SpecialDivisorCharts.point
    exact special_infinityPointIdeal_ne_bot _ _

theorem special_divisor_infinityIdeal_ne_bot
    (D : N13SpecialDivisorCharts.EffectiveDivisorTwo) :
    (N13SpecialDivisorCharts.ofDivisor D).infinityIdeal ≠ ⊥ := by
  refine Sym2.inductionOn D ?_
  intro p q
  change (N13SpecialDivisorCharts.point p).infinityIdeal *
    (N13SpecialDivisorCharts.point q).infinityIdeal ≠ ⊥
  intro h
  rcases Ideal.mul_eq_bot.mp h with hp | hq
  · exact special_point_infinityIdeal_ne_bot p hp
  · exact special_point_infinityIdeal_ne_bot q hq

theorem infinity_two_ne_zero : algebraMap R₂ B (2 : R₂) ≠ 0 := by
  intro hz
  have hh : N13IntegralInfinityPointSpread.xClassHom (C (2 : R₂)) =
      N13IntegralInfinityPointSpread.xClassHom 0 := by
    have hmap : N13IntegralInfinityPointSpread.xClassHom (C (2 : R₂)) =
        algebraMap R₂ B (2 : R₂) := by
      simp [N13IntegralInfinityPointSpread.xClassHom]
      rfl
    rw [hmap, hz, map_zero]
  have hc := N13IntegralInfinityPointSpread.xClassHom_injective hh
  have hcc := congrArg (fun p : R₂[X] => p.coeff 0) hc
  norm_num at hcc

/-- Every two-fibre Data already has a vertically saturated infinity ideal:
invertibility is part of its line, and its actual special divisor gives a
nonzero reduction in the domain-valued special infinity chart. This does
not say that its independent infinityOrder is geometrically correct. -/
theorem data_infinityVerticallySaturated (R : N13TwoChartPicardRealization.Data) :
    ∀ r : R₂, r ≠ 0 → ∀ a : B,
      algebraMap R₂ B r * a ∈ R.charts.infinityIdeal → a ∈ R.charts.infinityIdeal := by
  have hred : Ideal.map N13IntegralInfinityReduction.reduceCoordinate
      R.charts.infinityIdeal ≠ ⊥ := by
    change (N13TwoChartSpecialRestriction.restrict R.charts).infinityIdeal ≠ ⊥
    rw [R.special_infinity]
    exact special_divisor_infinityIdeal_ne_bot R.specialDivisor
  exact twoAdic_scalar_saturated_of_reduction_ne_bot
    (K := N13IntegralInfinityPointSpread.FunctionField)
    N13IntegralInfinityReduction.reduceCoordinate infinity_two_ne_zero
    N13IntegralInfinityReduction.ker_reduceCoordinate R.charts.infinityIdeal
    R.charts.infinity_isUnit hred

end InfinityApplication

end
end MazurProof.N13InvertibleReductionSaturation


