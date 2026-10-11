-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0026
-- name    : PNT_ZeroFree_433_0026
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-10T13:35:34.820051+00:00
-- url     : https://prove2.me/theorems/7d1e50df-cc80-4971-a55f-36208e27ffc1
-- title:
--   Zero-free region foundations: Arithmetic.NormFiberMellin [0026]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.Arithmetic.NormFiberMellin
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Arithmetic/NormFiberMellin.lean#L33-L714

import Definitions.Def_PNT_ZeroFree_433_0025

/- Supporting source modules for the zero-free-region proof.
Ported and checked against Lean 4.33.1 / Mathlib 0df444a.
Original source attribution:
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Arithmetic/NormFiberMellin.lean#L33-L714
-/

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

-- Source module: OAI.NumberTheory.DirichletL.Arithmetic.NormFiberMellin
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

namespace ShortDraftLocal

theorem no_quadratic_scalar {F : Type*} [Field F] [Fintype F]
    (χ : MulChar F ℂ) (hχ : χ ≠ χ ^ 3) (c : ℂ) (hc : c ≠ 0) :
    ¬ ∃ d : ℂ, ∀ x : F, c * χ x = d * (χ ^ 3) x := by
  rintro ⟨d, hd⟩
  have hcd : c = d := by
    have h := hd 1
    simpa using h
  apply hχ
  ext x
  have h := hd x
  rw [← hcd] at h
  exact mul_left_cancel₀ hc h

end ShortDraftLocal

open MulChar AddChar

namespace ActualEisensteinCubic

theorem canonical_A5_jtwo_direct (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2)
    (ψ : AddChar (O ⧸ P) ℂ) (hψ : ψ ≠ 1)
    (σ : (O ⧸ P)ˣ) (ε x : O ⧸ P) :
    let χ := canonicalSextic P hgood
    (Nat.card (O ⧸ P) : ℂ)⁻¹ *
      (∑ h : (O ⧸ P)ˣ,
        (∑ t : O ⧸ P, (χ ^ 2) t * ψ (-(h * t))) *
        (χ ^ 2) (σ * h) *
        ψ ((ε * x) * ((h⁻¹ : (O ⧸ P)ˣ) : O ⧸ P))) =
      (χ ^ 2) σ *
      ((Nat.card (O ⧸ P) : ℂ)⁻¹ *
        gaussSum (χ ^ 2) (ψ.mulShift (-1)) *
        (if ε * x = 0 then (Nat.card (O ⧸ P)ˣ : ℂ) else -1)) := by
  let : Field (O ⧸ P) := Ideal.Quotient.field P
  let : Fintype (O ⧸ P) := Fintype.ofFinite _
  have hχ₂ : (canonicalSextic P hgood) ^ 2 ≠ 1 :=
    canonicalSextic_pow_ne_one P hgood hchar
      (j := 2) (by decide) (by decide)
  dsimp
  simp only [Nat.card_eq_fintype_card]
  exact ShortDraftLocal.direct_theta_jtwo_fourier_row
    (canonicalSextic P hgood) ψ hχ₂ hψ σ ε x

theorem canonical_A5_jzero_direct_active (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2)
    (ψ : AddChar (O ⧸ P) ℂ)
    (σ : (O ⧸ P)ˣ) (ε x : O ⧸ P) :
    let χ := canonicalSextic P hgood
    (-(Nat.card (O ⧸ P) : ℂ)⁻¹) *
      (∑ h : (O ⧸ P)ˣ, (χ ^ 2) (σ * h) *
        ψ ((ε * x) * ((h⁻¹ : (O ⧸ P)ˣ) : O ⧸ P))) =
      -(χ ^ 2) σ *
      ((Nat.card (O ⧸ P) : ℂ)⁻¹ *
        gaussSum ((χ ^ 2)⁻¹) ψ * (χ ^ 2) ε) * (χ ^ 2) x := by
  let : Field (O ⧸ P) := Ideal.Quotient.field P
  let : Fintype (O ⧸ P) := Fintype.ofFinite _
  have hχ₂ : (canonicalSextic P hgood) ^ 2 ≠ 1 :=
    canonicalSextic_pow_ne_one P hgood hchar
      (j := 2) (by decide) (by decide)
  dsimp
  rw [Nat.card_eq_fintype_card]
  exact ShortDraftLocal.direct_theta_active_zero_fourier_row
    (canonicalSextic P hgood) ψ hχ₂ σ ε x

theorem canonical_A5_jzero_direct_full (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2)
    (ψ : AddChar (O ⧸ P) ℂ) (hψ : ψ ≠ 1)
    (σ : (O ⧸ P)ˣ) (ε x : O ⧸ P) :
    let χ := canonicalSextic P hgood
    (Nat.card (O ⧸ P) : ℂ)⁻¹ *
      (∑ h : (O ⧸ P)ˣ,
        (∑ t : O ⧸ P, (χ ^ 0) t * ψ (-(h * t))) *
        (χ ^ 2) (σ * h) *
        ψ ((ε * x) * ((h⁻¹ : (O ⧸ P)ˣ) : O ⧸ P))) =
      -(χ ^ 2) σ *
      ((Nat.card (O ⧸ P) : ℂ)⁻¹ *
        gaussSum ((χ ^ 2)⁻¹) ψ * (χ ^ 2) ε) * (χ ^ 2) x := by
  let : Field (O ⧸ P) := Ideal.Quotient.field P
  let : Fintype (O ⧸ P) := Fintype.ofFinite _
  have hχ₂ : (canonicalSextic P hgood) ^ 2 ≠ 1 :=
    canonicalSextic_pow_ne_one P hgood hchar
      (j := 2) (by decide) (by decide)
  dsimp
  rw [Nat.card_eq_fintype_card]
  exact ShortDraftLocal.direct_theta_active_zero_full_row
    (canonicalSextic P hgood) ψ hχ₂ hψ σ ε x

end ActualEisensteinCubic

namespace ShortDraftHeckeBridge

noncomputable def chiMinusThree : DirichletCharacter ℂ 3 :=
  (quadraticChar (ZMod 3)).ringHomComp (Int.castRingHom ℂ)

noncomputable def baseChangeWeight {q : ℕ}
    (χ : DirichletCharacter ℂ q) (I : Ideal O) : ℂ :=
  (UniqueFactorizationMonoid.moebius I : ℂ) * χ (Ideal.absNorm I)

theorem baseChangeWeight_prime {q : ℕ} (χ : DirichletCharacter ℂ q)
    (P : Ideal O) (hP : Prime P) :
    baseChangeWeight χ P = -χ (Ideal.absNorm P) := by
  rw [baseChangeWeight, hP.irreducible.moebius_eq]
  norm_num

noncomputable def invCharAF {q : ℕ} (χ : DirichletCharacter ℂ q) : ArithmeticFunction ℂ :=
  (toArithmeticFunction (χ ·)).pmul (ArithmeticFunction.moebius : ArithmeticFunction ℂ)

theorem invCharAF_apply {q : ℕ} (χ : DirichletCharacter ℂ q)
    {n : ℕ} (hn : n ≠ 0) :
    invCharAF χ n = χ n * (ArithmeticFunction.moebius n : ℂ) := by
  change ((toArithmeticFunction (χ ·)).pmul
    (ArithmeticFunction.moebius : ArithmeticFunction ℂ)) n = _
  rw [ArithmeticFunction.pmul_apply]
  simp [toArithmeticFunction, hn]

private theorem invCharAF_mult {q : ℕ} (χ : DirichletCharacter ℂ q) :
    (invCharAF χ).IsMultiplicative := by
  exact (χ.isMultiplicative_toArithmeticFunction).pmul
    (ArithmeticFunction.isMultiplicative_moebius.intCast)

noncomputable def pairAF {q r : ℕ} (χ : DirichletCharacter ℂ q)
    (ψ : DirichletCharacter ℂ r) : ArithmeticFunction ℂ :=
  invCharAF χ * invCharAF ψ

theorem pairAF_mult {q r : ℕ} (χ : DirichletCharacter ℂ q)
    (ψ : DirichletCharacter ℂ r) :
    (pairAF χ ψ).IsMultiplicative :=
  (invCharAF_mult χ).mul (invCharAF_mult ψ)

theorem pairAF_eq_pairInverseCoeff {q r : ℕ}
    (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r)
    (n : ℕ) : pairAF χ ψ n = pairInverseCoeff χ ψ n := by
  rw [pairAF, ← ArithmeticFunction.coe_mul]
  apply congrFun
  exact (LSeries.convolution_congr
    (fun {k} hk => invCharAF_apply χ hk)
    (fun {k} hk => invCharAF_apply ψ hk))

theorem normFiber_eq_pair_of_prime_powers
    {q r : ℕ} (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r)
    (weight : Ideal O → ℂ)
    (hb : (toArithmeticFunction (normFiberCoeff weight)).IsMultiplicative)
    (hlocal : ∀ p k : ℕ, p.Prime →
      (toArithmeticFunction (normFiberCoeff weight)) (p ^ k) =
        pairAF χ ψ (p ^ k))
    (n : ℕ) (hn : n ≠ 0) :
    normFiberCoeff weight n = pairInverseCoeff χ ψ n := by
  have heq : toArithmeticFunction (normFiberCoeff weight) = pairAF χ ψ :=
    (ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers
      _ hb _ (pairAF_mult χ ψ)).2 hlocal
  have h := congrFun (congrArg DFunLike.coe heq) n
  calc
    normFiberCoeff weight n = (toArithmeticFunction (normFiberCoeff weight)) n := by
      simp [toArithmeticFunction, hn]
    _ = pairAF χ ψ n := h
    _ = pairInverseCoeff χ ψ n := pairAF_eq_pairInverseCoeff χ ψ n

theorem pairAF_prime {q r : ℕ} (χ : DirichletCharacter ℂ q)
    (ψ : DirichletCharacter ℂ r) {p : ℕ} (hp : p.Prime) :
    pairAF χ ψ p = -(χ p + ψ p) := by
  have h1χ : invCharAF χ 1 = 1 := (invCharAF_mult χ).map_one
  have h1ψ : invCharAF ψ 1 = 1 := (invCharAF_mult ψ).map_one
  have hpχ : invCharAF χ p = -χ p := by
    rw [invCharAF_apply χ hp.ne_zero, ArithmeticFunction.moebius_apply_prime hp]
    simp
  have hpψ : invCharAF ψ p = -ψ p := by
    rw [invCharAF_apply ψ hp.ne_zero, ArithmeticFunction.moebius_apply_prime hp]
    simp
  rw [pairAF, ArithmeticFunction.mul_apply]
  conv_lhs => rw [Nat.sum_divisorsAntidiagonal
    (fun a b => invCharAF χ a * invCharAF ψ b)]
  rw [hp.divisors]
  have hnot : 1 ∉ ({p} : Finset ℕ) := by simpa using hp.ne_one.symm
  rw [Finset.sum_insert hnot, Finset.sum_singleton]
  simp [Nat.div_one, Nat.div_self hp.pos, h1χ, h1ψ, hpχ, hpψ]

theorem pairAF_prime_sq {q r : ℕ} (χ : DirichletCharacter ℂ q)
    (ψ : DirichletCharacter ℂ r) {p : ℕ} (hp : p.Prime) :
    pairAF χ ψ (p ^ 2) = χ p * ψ p := by
  have h1χ : invCharAF χ 1 = 1 := (invCharAF_mult χ).map_one
  have h1ψ : invCharAF ψ 1 = 1 := (invCharAF_mult ψ).map_one
  have hpχ : invCharAF χ p = -χ p := by
    rw [invCharAF_apply χ hp.ne_zero, ArithmeticFunction.moebius_apply_prime hp]
    simp
  have hpψ : invCharAF ψ p = -ψ p := by
    rw [invCharAF_apply ψ hp.ne_zero, ArithmeticFunction.moebius_apply_prime hp]
    simp
  have hp2χ : invCharAF χ (p ^ 2) = 0 := by
    rw [invCharAF_apply χ (pow_ne_zero 2 hp.ne_zero),
      ArithmeticFunction.moebius_apply_prime_pow hp (by decide)]
    simp
  have hp2ψ : invCharAF ψ (p ^ 2) = 0 := by
    rw [invCharAF_apply ψ (pow_ne_zero 2 hp.ne_zero),
      ArithmeticFunction.moebius_apply_prime_pow hp (by decide)]
    simp
  have hdiv : (p ^ 2).divisors = ({1, p, p ^ 2} : Finset ℕ) := by
    ext x
    rw [Nat.mem_divisors_prime_pow hp 2]
    simp only [Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨j, hj, rfl⟩
      interval_cases j <;> simp
    · rintro (rfl | rfl | rfl)
      · exact ⟨0, by decide, by simp⟩
      · exact ⟨1, by decide, by simp⟩
      · exact ⟨2, by decide, by simp⟩
  rw [pairAF, ArithmeticFunction.mul_apply]
  conv_lhs => rw [Nat.sum_divisorsAntidiagonal
    (fun a b => invCharAF χ a * invCharAF ψ b)]
  rw [hdiv]
  have hpge : 2 ≤ p := hp.two_le
  have h1p2 : 1 ≠ p ^ 2 := by nlinarith
  have hpp2 : p ≠ p ^ 2 := by nlinarith
  have hnot1 : 1 ∉ ({p, p ^ 2} : Finset ℕ) := by
    simp [hp.ne_one.symm, h1p2]
  have hnotp : p ∉ ({p ^ 2} : Finset ℕ) := by
    simp [hpp2]
  rw [Finset.sum_insert hnot1, Finset.sum_insert hnotp, Finset.sum_singleton]
  have hdivp : p ^ 2 / p = p := by simp [pow_two, hp.pos]
  simp [Nat.div_one, hdivp, h1χ,  hpχ, hpψ, hp2χ, hp2ψ]

theorem chiMinusThree_two : chiMinusThree (2 : ℕ) = -1 := by
  have h3 : ringChar (ZMod 3) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; decide
  have h2 : (2 : ZMod 3) ≠ 0 := by decide
  have h21 : (2 : ZMod 3) ≠ 1 := by decide
  change ((quadraticChar (ZMod 3) (2 : ZMod 3) : ℤ) : ℂ) = -1
  rw [quadraticChar_eq_pow_of_char_ne_two h3 h2]
  simp [h21]

theorem chiMinusThree_ne_one : chiMinusThree ≠ 1 := by
  intro h
  have hh := congrArg (fun ξ : DirichletCharacter ℂ 3 => ξ (2 : ℕ)) h
  rw [chiMinusThree_two] at hh
  have hunit : IsUnit (2 : ZMod 3) := by decide
  change (-1 : ℂ) = (1 : DirichletCharacter ℂ 3) (2 : ZMod 3) at hh
  rw [MulChar.one_apply hunit] at hh
  norm_num at hh

theorem not_both_principal {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) :
    ¬ ((χ.changeLevel (Nat.dvd_mul_right q 3) = 1) ∧
      χ.changeLevel (Nat.dvd_mul_right q 3) *
        chiMinusThree.changeLevel (Nat.dvd_mul_left 3 q) = 1) := by
  rintro ⟨hχ, hprod⟩
  rw [hχ, one_mul] at hprod
  have hη : chiMinusThree = 1 :=
    (DirichletCharacter.changeLevel_eq_one_iff (Nat.dvd_mul_left 3 q)).mp hprod
  exact chiMinusThree_ne_one hη

end ShortDraftHeckeBridge
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology

namespace ShortDraftHeckeBridge

noncomputable def normFiberExpSum (weight : Ideal O → ℂ) (t : ℝ) : ℂ :=
  ∑' n : ℕ, normFiberCoeff weight n * Real.exp (-(n : ℝ) * t)

noncomputable def normFiberMellin (weight : Ideal O → ℂ) (s : ℂ) : ℂ :=
  mellin (fun D : ℝ => normFiberExpSum weight D⁻¹) (-s) / Complex.Gamma s

theorem pairInverseCoeff_zero
    {q r : ℕ} (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r) :
    pairInverseCoeff χ ψ 0 = 0 := by
  simp [pairInverseCoeff]

theorem pairInverseCoeff_LSeriesSummable
    {q r : ℕ} [NeZero q] [NeZero r]
    (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r)
    (s : ℂ) (hs : 1 < s.re) :
    LSeriesSummable (pairInverseCoeff χ ψ) s := by
  have hχ : LSeriesSummable
      (fun n : ℕ => χ n * (ArithmeticFunction.moebius n : ℂ)) s :=
    DirichletCharacter.LSeriesSummable_mul χ
      (ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hs)
  have hψ : LSeriesSummable
      (fun n : ℕ => ψ n * (ArithmeticFunction.moebius n : ℂ)) s :=
    DirichletCharacter.LSeriesSummable_mul ψ
      (ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hs)
  exact hχ.convolution hψ

private theorem mobius_char_coeff_norm_le_one
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (n : ℕ) :
    ‖χ n * (ArithmeticFunction.moebius n : ℂ)‖ ≤ 1 := by
  rw [norm_mul]
  have hχ : ‖χ n‖ ≤ 1 := χ.norm_le_one _
  have hμ : ‖(ArithmeticFunction.moebius n : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_intCast]
    exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := n))
  nlinarith [mul_nonneg (sub_nonneg.mpr hχ)
    (norm_nonneg ((ArithmeticFunction.moebius n : ℂ))),
    mul_nonneg (sub_nonneg.mpr hμ) (norm_nonneg (χ n))]

theorem pairInverseCoeff_norm_le
    {q r : ℕ} [NeZero q] [NeZero r]
    (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r)
    (n : ℕ) : ‖pairInverseCoeff χ ψ n‖ ≤ (n : ℝ) := by
  rw [pairInverseCoeff, LSeries.convolution_def]
  have hcard : (n.divisorsAntidiagonal.card : ℝ) ≤ n := by
    rw [← Nat.map_div_right_divisors, Finset.card_map]
    exact_mod_cast Nat.card_divisors_le_self n
  calc
    ‖∑ p ∈ n.divisorsAntidiagonal,
        (χ p.1 * (ArithmeticFunction.moebius p.1 : ℂ)) *
        (ψ p.2 * (ArithmeticFunction.moebius p.2 : ℂ))‖ ≤
      ∑ p ∈ n.divisorsAntidiagonal,
        ‖(χ p.1 * (ArithmeticFunction.moebius p.1 : ℂ)) *
        (ψ p.2 * (ArithmeticFunction.moebius p.2 : ℂ))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _p ∈ n.divisorsAntidiagonal, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro p hp
      rw [norm_mul]
      have hχ := mobius_char_coeff_norm_le_one χ p.1
      have hψ := mobius_char_coeff_norm_le_one ψ p.2
      nlinarith [mul_nonneg (sub_nonneg.mpr hχ)
        (norm_nonneg (ψ p.2 * (ArithmeticFunction.moebius p.2 : ℂ))),
        mul_nonneg (sub_nonneg.mpr hψ)
          (norm_nonneg (χ p.1 * (ArithmeticFunction.moebius p.1 : ℂ)))]
    _ = (n.divisorsAntidiagonal.card : ℝ) := by simp
    _ ≤ n := hcard

theorem normFiberCoeff_norm_le
    {q r : ℕ} [NeZero q] [NeZero r]
    (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r)
    (weight : Ideal O → ℂ)
    (hcoeff : ∀ n : ℕ, n ≠ 0 → normFiberCoeff weight n = pairInverseCoeff χ ψ n)
    (ha0 : normFiberCoeff weight 0 = 0)
    (n : ℕ) : ‖normFiberCoeff weight n‖ ≤ (n : ℝ) := by
  by_cases hn : n = 0
  · subst n
    simp [ha0]
  · rw [hcoeff n hn]
    exact pairInverseCoeff_norm_le χ ψ n

theorem normFiberExpSum_summable
    {q r : ℕ} [NeZero q] [NeZero r]
    (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r)
    (weight : Ideal O → ℂ)
    (hcoeff : ∀ n : ℕ, n ≠ 0 → normFiberCoeff weight n = pairInverseCoeff χ ψ n)
    (ha0 : normFiberCoeff weight 0 = 0)
    (t : ℝ) (ht : 0 < t) :
    Summable (fun n : ℕ => normFiberCoeff weight n * Real.exp (-(n : ℝ) * t)) := by
  have hexp : Summable (fun n : ℕ => (n : ℝ) * Real.exp (-(n : ℝ) * t)) := by
    convert! Real.summable_pow_mul_exp_neg_nat_mul 1 ht using 1
    ext n
    simp only [pow_one]
    congr 1
    ring_nf
  apply hexp.of_norm_bounded
  intro n
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  exact mul_le_mul_of_nonneg_right
    (normFiberCoeff_norm_le χ ψ weight hcoeff ha0 n) (Real.exp_pos _).le

theorem normFiberExpSum_continuousOn_pos
    {q r : ℕ} [NeZero q] [NeZero r]
    (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r)
    (weight : Ideal O → ℂ)
    (hcoeff : ∀ n : ℕ, n ≠ 0 → normFiberCoeff weight n = pairInverseCoeff χ ψ n)
    (ha0 : normFiberCoeff weight 0 = 0) :
    ContinuousOn (normFiberExpSum weight) (Set.Ioi (0 : ℝ)) := by
  intro t ht
  change 0 < t at ht
  let eps0 : ℝ := t / 2
  have heps0 : 0 < eps0 := by dsimp [eps0]; linarith
  have heps0t : eps0 < t := by dsimp [eps0]; linarith
  have hexp : Summable (fun n : ℕ => (n : ℝ) * Real.exp (-(n : ℝ) * eps0)) := by
    convert! Real.summable_pow_mul_exp_neg_nat_mul 1 heps0 using 1
    ext n
    simp only [pow_one]
    congr 1
    ring_nf
  have hcontTerm (n : ℕ) : ContinuousOn
      (fun u : ℝ => normFiberCoeff weight n * Real.exp (-(n : ℝ) * u))
      (Set.Ici eps0) := by
    fun_prop
  have hbound (n : ℕ) (u : ℝ) (hu : u ∈ Set.Ici eps0) :
      ‖normFiberCoeff weight n * Real.exp (-(n : ℝ) * u)‖ ≤
        (n : ℝ) * Real.exp (-(n : ℝ) * eps0) := by
    have hnu : -(n : ℝ) * u ≤ -(n : ℝ) * eps0 := by
      have hu' : eps0 ≤ u := hu
      nlinarith [mul_le_mul_of_nonneg_left hu'
        (Nat.cast_nonneg (α := ℝ) n)]
    have hexpmon := Real.exp_le_exp.mpr hnu
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    calc
      ‖normFiberCoeff weight n‖ * Real.exp (-(n : ℝ) * u) ≤
          (n : ℝ) * Real.exp (-(n : ℝ) * u) :=
        mul_le_mul_of_nonneg_right
          (normFiberCoeff_norm_le χ ψ weight hcoeff ha0 n) (Real.exp_pos _).le
      _ ≤ (n : ℝ) * Real.exp (-(n : ℝ) * eps0) :=
        mul_le_mul_of_nonneg_left hexpmon (Nat.cast_nonneg (α := ℝ) n)
  have hcontHalf : ContinuousOn (normFiberExpSum weight) (Set.Ici eps0) := by
    change ContinuousOn
      (fun u : ℝ => ∑' n : ℕ,
        normFiberCoeff weight n * Real.exp (-(n : ℝ) * u)) (Set.Ici eps0)
    exact continuousOn_tsum hcontTerm hexp hbound
  exact (hcontHalf.continuousAt (Ici_mem_nhds heps0t)).continuousWithinAt

theorem normFiberExpSum_inv_locallyIntegrableOn_pos
    {q r : ℕ} [NeZero q] [NeZero r]
    (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r)
    (weight : Ideal O → ℂ)
    (hcoeff : ∀ n : ℕ, n ≠ 0 → normFiberCoeff weight n = pairInverseCoeff χ ψ n)
    (ha0 : normFiberCoeff weight 0 = 0) :
    LocallyIntegrableOn
      (fun D : ℝ => normFiberExpSum weight D⁻¹) (Set.Ioi 0) := by
  have hcont : ContinuousOn
      (fun D : ℝ => normFiberExpSum weight D⁻¹) (Set.Ioi 0) := by
    apply (normFiberExpSum_continuousOn_pos χ ψ weight hcoeff ha0).comp
      (continuousOn_inv₀.mono (by
        intro D hD
        exact ne_of_gt hD))
    intro D hD
    exact inv_pos.mpr (show 0 < D from hD)
  exact hcont.locallyIntegrableOn measurableSet_Ioi

theorem normFiberExpSum_norm_le_exp
    {q r : ℕ} [NeZero q] [NeZero r]
    (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r)
    (weight : Ideal O → ℂ)
    (hcoeff : ∀ n : ℕ, n ≠ 0 → normFiberCoeff weight n = pairInverseCoeff χ ψ n)
    (ha0 : normFiberCoeff weight 0 = 0)
    (t : ℝ) (ht : 1 ≤ t) :
    ‖normFiberExpSum weight t‖ ≤
      (∑' n : ℕ, (n : ℝ) * Real.exp (-(n : ℝ) / 2)) *
        Real.exp (-t / 2) := by
  have hmajor : Summable (fun n : ℕ =>
      (n : ℝ) * Real.exp (-(n : ℝ) / 2)) := by
    convert! Real.summable_pow_mul_exp_neg_nat_mul 1 (by norm_num : (0 : ℝ) < 1 / 2) using 1
    ext n
    simp only [pow_one]
    congr 1
    ring_nf
  have hbound (n : ℕ) :
      ‖normFiberCoeff weight n * Real.exp (-(n : ℝ) * t)‖ ≤
        ((n : ℝ) * Real.exp (-(n : ℝ) / 2)) * Real.exp (-t / 2) := by
    by_cases hn : n = 0
    · subst n
      simp [ha0]
    have hn1 : (1 : ℝ) ≤ n := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
    have hdiff : -(n : ℝ) * t ≤ -(n : ℝ) / 2 - t / 2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hn1) (sub_nonneg.mpr ht)]
    have hexp : Real.exp (-(n : ℝ) * t) ≤
        Real.exp (-(n : ℝ) / 2) * Real.exp (-t / 2) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      convert! hdiff using 1
      ring
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    calc
      ‖normFiberCoeff weight n‖ * Real.exp (-(n : ℝ) * t) ≤
          (n : ℝ) * Real.exp (-(n : ℝ) * t) :=
        mul_le_mul_of_nonneg_right
          (normFiberCoeff_norm_le χ ψ weight hcoeff ha0 n) (Real.exp_pos _).le
      _ ≤ ((n : ℝ) * Real.exp (-(n : ℝ) / 2)) * Real.exp (-t / 2) := by
        nlinarith [mul_le_mul_of_nonneg_left hexp
          (Nat.cast_nonneg (α := ℝ) n)]
  have hnormsum : Summable (fun n : ℕ =>
      ‖normFiberCoeff weight n * Real.exp (-(n : ℝ) * t)‖) :=
    (hmajor.mul_right (Real.exp (-t / 2))).of_nonneg_of_le
      (fun _ => norm_nonneg _) hbound
  calc
    ‖normFiberExpSum weight t‖ ≤
      ∑' n : ℕ, ‖normFiberCoeff weight n * Real.exp (-(n : ℝ) * t)‖ :=
      norm_tsum_le_tsum_norm hnormsum
    _ ≤ ∑' n : ℕ,
        ((n : ℝ) * Real.exp (-(n : ℝ) / 2)) * Real.exp (-t / 2) :=
      hnormsum.tsum_le_tsum hbound (hmajor.mul_right _)
    _ = (∑' n : ℕ, (n : ℝ) * Real.exp (-(n : ℝ) / 2)) *
        Real.exp (-t / 2) := by rw [tsum_mul_right]

theorem normFiberExpSum_flat_at_zero
    {q r : ℕ} [NeZero q] [NeZero r]
    (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r)
    (weight : Ideal O → ℂ)
    (hcoeff : ∀ n : ℕ, n ≠ 0 → normFiberCoeff weight n = pairInverseCoeff χ ψ n)
    (ha0 : normFiberCoeff weight 0 = 0)
    (b : ℝ) :
    (fun D : ℝ => normFiberExpSum weight D⁻¹) =O[𝓝[>] (0 : ℝ)]
      (fun D : ℝ => D ^ b) := by
  let C : ℝ := ∑' n : ℕ, (n : ℝ) * Real.exp (-(n : ℝ) / 2)
  have hExp : (fun t : ℝ => normFiberExpSum weight t) =O[atTop]
      (fun t : ℝ => Real.exp (-t / 2)) := by
    apply isBigO_iff_isBigOWith.mpr
    refine ⟨C, IsBigOWith.of_bound ?_⟩
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
    simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using
      normFiberExpSum_norm_le_exp χ ψ weight hcoeff ha0 t ht
  have hpow : (fun t : ℝ => normFiberExpSum weight t) =O[atTop]
      (fun t : ℝ => t ^ (-b)) := by
    apply hExp.trans
    have heq : (fun t : ℝ => Real.exp (-t / 2)) =
        (fun t : ℝ => Real.exp (-(1 / 2 : ℝ) * t)) := by
      funext t
      congr 1
      ring
    rw [heq]
    exact
      (isLittleO_exp_neg_mul_rpow_atTop
        (by norm_num : (0 : ℝ) < 1 / 2) (-b)).isBigO
  have hcomp := hpow.comp_tendsto tendsto_inv_nhdsGT_zero
  refine hcomp.congr (fun _ => rfl) ?_
  intro D
  dsimp
  rw [← Real.rpow_neg_eq_inv_rpow]
  simp

theorem normFiberExpSum_mellin
    {q r : ℕ} [NeZero q] [NeZero r]
    (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r)
    (weight : Ideal O → ℂ)
    (hcoeff : ∀ n : ℕ, n ≠ 0 → normFiberCoeff weight n = pairInverseCoeff χ ψ n)
    (ha0 : normFiberCoeff weight 0 = 0)
    (hexp : ∀ t : ℝ, 0 < t → Summable
      (fun n : ℕ => normFiberCoeff weight n * Real.exp (-(n : ℝ) * t)))
    (s : ℂ) (hs : 1 < s.re) :
    mellin (fun D : ℝ => normFiberExpSum weight D⁻¹) (-s) =
      Complex.Gamma s * LSeries (normFiberCoeff weight) s := by
  apply ShortDraftMellin.mellin_of_exponential_smoothing
    (normFiberCoeff weight) (normFiberExpSum weight) s hs ha0
  · intro t ht
    exact (hexp t ht).hasSum
  · exact (LSeriesSummable_congr s (fun {n} hn => hcoeff n hn)).mpr
      (pairInverseCoeff_LSeriesSummable χ ψ s hs)

theorem normFiberMellin_analytic
    (weight : Ideal O → ℂ) (σ : ℝ) (hσpos : 0 < σ)
    (hlocal : LocallyIntegrableOn
      (fun D : ℝ => normFiberExpSum weight D⁻¹) (Set.Ioi 0))
    (htop : (fun D : ℝ => normFiberExpSum weight D⁻¹) =O[atTop]
      (fun D : ℝ => D ^ σ))
    (hflat : ∀ b : ℝ,
      (fun D : ℝ => normFiberExpSum weight D⁻¹) =O[𝓝[>] (0 : ℝ)]
        (fun D : ℝ => D ^ b)) :
    AnalyticOnNhd ℂ (normFiberMellin weight) {s : ℂ | σ < s.re} := by
  let U : Set ℂ := {s : ℂ | σ < s.re}
  have hopen : IsOpen U := Complex.isOpen_re_gt σ
  have hM : AnalyticOnNhd ℂ
      (fun s : ℂ => mellin (fun D : ℝ => normFiberExpSum weight D⁻¹) (-s)) U :=
    ShortDraftMellin.inverse_mellin_analytic_of_flat _ σ hlocal htop hflat
  have hGamma : AnalyticOnNhd ℂ Complex.Gamma U := by
    apply (Complex.analyticOnNhd_iff_differentiableOn hopen).2
    intro s hs
    apply (Complex.differentiableAt_Gamma s ?_).differentiableWithinAt
    intro m hm
    have hreal : s.re = -(m : ℝ) := by
      simpa using congrArg Complex.re hm
    have hspos : 0 < s.re := lt_trans hσpos hs
    linarith [Nat.cast_nonneg (α := ℝ) m]
  have hGamma0 : ∀ s ∈ U, Complex.Gamma s ≠ 0 := by
    intro s hs
    exact Complex.Gamma_ne_zero_of_re_pos (lt_trans hσpos hs)
  exact hM.div hGamma hGamma0

theorem normFiberMellin_eq_LSeries
    {q r : ℕ} [NeZero q] [NeZero r]
    (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r)
    (weight : Ideal O → ℂ)
    (hcoeff : ∀ n : ℕ, n ≠ 0 → normFiberCoeff weight n = pairInverseCoeff χ ψ n)
    (ha0 : normFiberCoeff weight 0 = 0)
    (hexp : ∀ t : ℝ, 0 < t → Summable
      (fun n : ℕ => normFiberCoeff weight n * Real.exp (-(n : ℝ) * t)))
    (s : ℂ) (hs : 1 < s.re) :
    normFiberMellin weight s = LSeries (normFiberCoeff weight) s := by
  rw [normFiberMellin, normFiberExpSum_mellin χ ψ weight hcoeff ha0 hexp s hs]
  exact mul_div_cancel_left₀ _
    (Complex.Gamma_ne_zero_of_re_pos (lt_trans zero_lt_one hs))

theorem pair_zero_free_of_normFiber_exp_power_bound
    {q r : ℕ} [NeZero q] [NeZero r]
    (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r)
    (hχ : χ ≠ 1) (hψ : ψ ≠ 1)
    (weight : Ideal O → ℂ)
    (hcoeff : ∀ n : ℕ, n ≠ 0 → normFiberCoeff weight n = pairInverseCoeff χ ψ n)
    (ha0 : normFiberCoeff weight 0 = 0)
    (hexp : ∀ t : ℝ, 0 < t → Summable
      (fun n : ℕ => normFiberCoeff weight n * Real.exp (-(n : ℝ) * t)))
    (σ : ℝ) (hσpos : 0 < σ) (hσ : σ < 1)
    (hlocal : LocallyIntegrableOn
      (fun D : ℝ => normFiberExpSum weight D⁻¹) (Set.Ioi 0))
    (htop : (fun D : ℝ => normFiberExpSum weight D⁻¹) =O[atTop]
      (fun D : ℝ => D ^ σ))
    (hflat : ∀ b : ℝ,
      (fun D : ℝ => normFiberExpSum weight D⁻¹) =O[𝓝[>] (0 : ℝ)]
        (fun D : ℝ => D ^ b))
    (ρ : ℂ) (hρ : σ < ρ.re) :
    χ.LFunction ρ ≠ 0 ∧ ψ.LFunction ρ ≠ 0 := by
  exact pair_zero_free_of_normFiber_continuation χ ψ hχ hψ weight hcoeff
    σ hσ (normFiberMellin weight)
    (normFiberMellin_analytic weight σ hσpos hlocal htop hflat)
    (fun s hs => normFiberMellin_eq_LSeries χ ψ weight hcoeff ha0 hexp s hs)
    ρ hρ

theorem normFiberMellin_analytic_of_coeff
    {q r : ℕ} [NeZero q] [NeZero r]
    (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r)
    (weight : Ideal O → ℂ)
    (hcoeff : ∀ n : ℕ, n ≠ 0 → normFiberCoeff weight n = pairInverseCoeff χ ψ n)
    (ha0 : normFiberCoeff weight 0 = 0)
    (σ : ℝ) (hσpos : 0 < σ)
    (htop : (fun D : ℝ => normFiberExpSum weight D⁻¹) =O[atTop]
      (fun D : ℝ => D ^ σ)) :
    AnalyticOnNhd ℂ (normFiberMellin weight) {s : ℂ | σ < s.re} :=
  normFiberMellin_analytic weight σ hσpos
    (normFiberExpSum_inv_locallyIntegrableOn_pos χ ψ weight hcoeff ha0)
    htop (normFiberExpSum_flat_at_zero χ ψ weight hcoeff ha0)

theorem normFiberMellin_eq_LSeries_of_coeff
    {q r : ℕ} [NeZero q] [NeZero r]
    (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r)
    (weight : Ideal O → ℂ)
    (hcoeff : ∀ n : ℕ, n ≠ 0 → normFiberCoeff weight n = pairInverseCoeff χ ψ n)
    (ha0 : normFiberCoeff weight 0 = 0)
    (s : ℂ) (hs : 1 < s.re) :
    normFiberMellin weight s = LSeries (normFiberCoeff weight) s :=
  normFiberMellin_eq_LSeries χ ψ weight hcoeff ha0
    (normFiberExpSum_summable χ ψ weight hcoeff ha0) s hs

theorem pair_zero_free_of_normFiber_exp_power_bound_only
    {q r : ℕ} [NeZero q] [NeZero r]
    (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r)
    (hχ : χ ≠ 1) (hψ : ψ ≠ 1)
    (weight : Ideal O → ℂ)
    (hcoeff : ∀ n : ℕ, n ≠ 0 → normFiberCoeff weight n = pairInverseCoeff χ ψ n)
    (ha0 : normFiberCoeff weight 0 = 0)
    (σ : ℝ) (hσpos : 0 < σ) (hσ : σ < 1)
    (htop : (fun D : ℝ => normFiberExpSum weight D⁻¹) =O[atTop]
      (fun D : ℝ => D ^ σ))
    (ρ : ℂ) (hρ : σ < ρ.re) :
    χ.LFunction ρ ≠ 0 ∧ ψ.LFunction ρ ≠ 0 := by
  exact pair_zero_free_of_normFiber_continuation χ ψ hχ hψ weight hcoeff
    σ hσ (normFiberMellin weight)
    (normFiberMellin_analytic_of_coeff χ ψ weight hcoeff ha0 σ hσpos htop)
    (fun s hs => normFiberMellin_eq_LSeries_of_coeff χ ψ weight hcoeff ha0 s hs)
    ρ hρ

theorem pair_zero_free_of_normFiber_exp_power_bound_principal_left
    {q r : ℕ} [NeZero q] [NeZero r]
    (ψ : DirichletCharacter ℂ r) (hψ : ψ ≠ 1)
    (weight : Ideal O → ℂ)
    (hcoeff : ∀ n : ℕ, n ≠ 0 →
      normFiberCoeff weight n =
        pairInverseCoeff (1 : DirichletCharacter ℂ q) ψ n)
    (ha0 : normFiberCoeff weight 0 = 0)
    (σ : ℝ) (hσpos : 0 < σ) (hσ : σ < 1)
    (htop : (fun D : ℝ => normFiberExpSum weight D⁻¹) =O[atTop]
      (fun D : ℝ => D ^ σ))
    (ρ : ℂ) (hρ : σ < ρ.re) (hρone : ρ ≠ 1) :
    DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q) ρ ≠ 0 ∧
      ψ.LFunction ρ ≠ 0 := by
  exact pair_zero_free_of_normFiber_continuation_principal_left ψ hψ
    weight hcoeff σ hσ (normFiberMellin weight)
    (normFiberMellin_analytic_of_coeff 1 ψ weight hcoeff ha0 σ hσpos htop)
    (fun s hs => normFiberMellin_eq_LSeries_of_coeff 1 ψ weight hcoeff ha0 s hs)
    ρ hρ hρone

theorem pair_zero_free_of_normFiber_exp_power_bound_principal_right
    {q r : ℕ} [NeZero q] [NeZero r]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (weight : Ideal O → ℂ)
    (hcoeff : ∀ n : ℕ, n ≠ 0 →
      normFiberCoeff weight n =
        pairInverseCoeff χ (1 : DirichletCharacter ℂ r) n)
    (ha0 : normFiberCoeff weight 0 = 0)
    (σ : ℝ) (hσpos : 0 < σ) (hσ : σ < 1)
    (htop : (fun D : ℝ => normFiberExpSum weight D⁻¹) =O[atTop]
      (fun D : ℝ => D ^ σ))
    (ρ : ℂ) (hρ : σ < ρ.re) (hρone : ρ ≠ 1) :
    χ.LFunction ρ ≠ 0 ∧
      DirichletCharacter.LFunction (1 : DirichletCharacter ℂ r) ρ ≠ 0 := by
  exact pair_zero_free_of_normFiber_continuation_principal_right χ hχ
    weight hcoeff σ hσ (normFiberMellin weight)
    (normFiberMellin_analytic_of_coeff χ 1 weight hcoeff ha0 σ hσpos htop)
    (fun s hs => normFiberMellin_eq_LSeries_of_coeff χ 1 weight hcoeff ha0 s hs)
    ρ hρ hρone

end ShortDraftHeckeBridge

end

end OAI

end


