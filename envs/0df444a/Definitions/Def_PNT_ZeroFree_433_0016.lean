-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0016
-- name    : PNT_ZeroFree_433_0016
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-10T12:21:40.12634+00:00
-- url     : https://prove2.me/theorems/8313feeb-5ae3-4934-aa74-c44b82612f96
-- title:
--   Zero-free region foundations: GaussSum.QuadraticNormalization [0016]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.GaussSum.QuadraticNormalization
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/GaussSum/QuadraticNormalization.lean#L22-L861

import Definitions.Def_PNT_ZeroFree_433_0015

/- Supporting source modules for the zero-free-region proof.
Ported and checked against Lean 4.33.1 / Mathlib 0df444a.
Original source attribution:
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/GaussSum/QuadraticNormalization.lean#L22-L861
-/

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

-- Source module: OAI.NumberTheory.DirichletL.GaussSum.QuadraticNormalization
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

namespace ActualEisensteinCubic

open EisensteinEmbedding ConcreteTraceCRT ConcreteBreveE

noncomputable def quadraticGammaO (c : O) (hc : c ≠ 0) : ℂ := by
  letI : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
  letI : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
  let ψ := eisTraceModChar ShortDraftTrace.breveE breveE_period_coordinates c hc
  exact (∑ x : O ⧸ Ideal.span {c}, ψ (x ^ 2)) /
    (‖eisEmbedding c‖ : ℂ)

theorem quadraticGammaO_traceLambda :
    quadraticGammaO traceLambda traceLambda_ne_zero =
      quadraticGammaTraceLambda := by rfl

theorem quadraticGammaO_negTraceLambda :
    quadraticGammaO (-traceLambda) (neg_ne_zero.mpr traceLambda_ne_zero) =
      quadraticGammaNegTraceLambda := by rfl

theorem quadraticGammaO_rational (m : ℕ) (hm : m ≠ 0)
    (hc : (m : O) ≠ 0) :
    quadraticGammaO (m : O) hc = quadraticGammaRational m hm := by rfl

theorem quadraticGammaO_rational_odd (m : ℕ) (hm : m ≠ 0)
    (hodd : Odd m) (hc : (m : O) ≠ 0) :
    quadraticGammaO (m : O) hc = breveGaussianFourTerms (m : ℤ) 0 := by
  rw [quadraticGammaO_rational m hm hc,
    quadraticGammaRational_eq_fourTerms m hm hodd]

end ActualEisensteinCubic

namespace PowerExtraction

theorem from_mean_square_and_prime_rows_with_constant
    (D ε J A C : ℝ) (hD : 1 ≤ D) (hε : 0 ≤ ε)
    (hA : 0 ≤ A) (hC : 1 ≤ C)
    (hJ : D ^ ((11 / 60 : ℝ) - ε) ≤ J)
    (hmean : J * A ^ 2 ≤
      2 * D ^ ((21 / 10 : ℝ) + ε) +
      2 * J * C ^ 2 * D ^ (49 / 30 : ℝ)) :
    A ≤ 2 * C * D ^ ((23 / 24 : ℝ) + ε) := by
  let E : ℝ := (23 / 24 : ℝ) + ε
  have hDpos : 0 < D := lt_of_lt_of_le zero_lt_one hD
  have hJpos : 0 < J := lt_of_lt_of_le (Real.rpow_pos_of_pos hDpos _) hJ
  have hpow :
      D ^ ((21 / 10 : ℝ) + ε) ≤
        J * D ^ ((23 / 12 : ℝ) + 2 * ε) := by
    calc
      D ^ ((21 / 10 : ℝ) + ε) =
          D ^ ((11 / 60 : ℝ) - ε) *
            D ^ ((23 / 12 : ℝ) + 2 * ε) := by
            rw [← Real.rpow_add hDpos]
            congr 1
            ring
      _ ≤ J * D ^ ((23 / 12 : ℝ) + 2 * ε) :=
          mul_le_mul_of_nonneg_right hJ (by positivity)
  have herr : D ^ (49 / 30 : ℝ) ≤
      D ^ ((23 / 12 : ℝ) + 2 * ε) := by
    apply Real.rpow_le_rpow_of_exponent_le hD
    linarith
  have hC2 : 1 ≤ C ^ 2 := by nlinarith
  have hP : 0 ≤ J * D ^ ((23 / 12 : ℝ) + 2 * ε) := by positivity
  have hsq : A ^ 2 ≤
      4 * C ^ 2 * D ^ ((23 / 12 : ℝ) + 2 * ε) := by
    have hmain : J * A ^ 2 ≤
        4 * J * C ^ 2 * D ^ ((23 / 12 : ℝ) + 2 * ε) := by
      calc
        J * A ^ 2 ≤
            2 * D ^ ((21 / 10 : ℝ) + ε) +
            2 * J * C ^ 2 * D ^ (49 / 30 : ℝ) := hmean
        _ ≤ 2 * (J * D ^ ((23 / 12 : ℝ) + 2 * ε)) +
            2 * J * C ^ 2 * D ^ ((23 / 12 : ℝ) + 2 * ε) := by
              gcongr
        _ ≤ 4 * J * C ^ 2 * D ^ ((23 / 12 : ℝ) + 2 * ε) := by
          nlinarith [mul_nonneg (sub_nonneg.mpr hC2) hP]
    nlinarith
  have hexp : (23 / 12 : ℝ) + 2 * ε = E * 2 := by
    dsimp [E]
    ring
  have hpow2 : (D ^ E) ^ 2 = D ^ ((23 / 12 : ℝ) + 2 * ε) := by
    calc
      (D ^ E) ^ 2 = D ^ (E * 2) :=
        (Real.rpow_mul_natCast hDpos.le E 2).symm
      _ = D ^ ((23 / 12 : ℝ) + 2 * ε) := by rw [hexp]
  have htwo : 0 ≤ 2 * C * D ^ E := by positivity
  apply (sq_le_sq₀ hA htwo).mp
  rw [mul_pow, mul_pow, hpow2]
  nlinarith

theorem from_finite_sixth_power_rows_with_constant
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (rows : Finset α) (primes : Finset β) (row : β → α)
    (A : α → ℂ) (untwisted : α) (D ε C : ℝ)
    (hD : 1 ≤ D) (hε : 0 ≤ ε) (hC : 1 ≤ C)
    (hrows : primes.image row ⊆ rows)
    (hinj : Set.InjOn row (primes : Set β))
    (happrox : ∀ p ∈ primes,
      ‖A untwisted - A (row p)‖ ≤ C * D ^ (49 / 60 : ℝ))
    (hcount : D ^ ((11 / 60 : ℝ) - ε) ≤ (primes.card : ℝ))
    (hmean : (∑ u ∈ rows, ‖A u‖ ^ 2) ≤
      D ^ ((21 / 10 : ℝ) + ε)) :
    ‖A untwisted‖ ≤ 2 * C * D ^ ((23 / 24 : ℝ) + ε) := by
  have hDpos : 0 < D := lt_of_lt_of_le zero_lt_one hD
  have hextract := ShortDraft.complex_row_extraction rows primes row A untwisted
    (C * D ^ (49 / 60 : ℝ)) (D ^ ((21 / 10 : ℝ) + ε))
    (by positivity) hrows hinj happrox hmean
  have herror : (C * D ^ (49 / 60 : ℝ)) ^ 2 =
      C ^ 2 * D ^ (49 / 30 : ℝ) := by
    rw [mul_pow]
    congr 1
    calc
      (D ^ (49 / 60 : ℝ)) ^ 2 = D ^ ((49 / 60 : ℝ) * 2) :=
        (Real.rpow_mul_natCast hDpos.le _ 2).symm
      _ = D ^ (49 / 30 : ℝ) := by congr 1; norm_num
  rw [herror] at hextract
  exact from_mean_square_and_prime_rows_with_constant D ε
    (primes.card : ℝ) ‖A untwisted‖ C hD hε (norm_nonneg _) hC
    hcount (by simpa only [mul_assoc] using hextract)

end PowerExtraction

namespace ActualEisensteinCubic

theorem finite_actual_prime_extraction_with_constant
    {ι β : Type*} (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hgood : ∀ i, lambda ∉ P i)
    (columns : Finset O) (support : O → Finset ι) (weight : O → ℂ)
    (selected : Finset β) (p : β → O) (rows : Finset O)
    (D : ℕ) (ε C : ℝ) (hD : 1 ≤ D) (hε : 0 ≤ ε)
    (hC : 1 ≤ C)
    (hp : ∀ i ∈ selected, p i ≠ 0)
    (hprime : ∀ i ∈ selected, (Ideal.span {p i} : Ideal O).IsMaximal)
    (hinj : Set.InjOn (fun i => (Ideal.span {p i} : Ideal O)) (selected : Set β))
    (hrows : selected.image (fun i => p i ^ 6) ⊆ rows)
    (hsupport : ∀ n ∈ columns, ∀ i ∈ support n, n ∈ P i)
    (hcolnorm : ∀ n ∈ columns, Ideal.absNorm (Ideal.span {n}) ≤ D)
    (hweight : ∀ n ∈ columns, ‖weight n‖ ≤ 1)
    (hrowbound : ∀ i ∈ selected,
      ((64 * (D / Ideal.absNorm (Ideal.span {p i}) + 1) : ℕ) : ℝ) ≤
        C * (D : ℝ) ^ (49 / 60 : ℝ))
    (hcount : (D : ℝ) ^ ((11 / 60 : ℝ) - ε) ≤ (selected.card : ℝ))
    (hmean :
      (∑ u ∈ rows,
        ‖∑ n ∈ columns,
          weight n * finiteSquarefreeRow P hgood (support n) u‖ ^ 2) ≤
        (D : ℝ) ^ ((21 / 10 : ℝ) + ε)) :
    ‖∑ n ∈ columns, weight n‖ ≤
      2 * C * (D : ℝ) ^ ((23 / 24 : ℝ) + ε) := by
  classical
  let A : O → ℂ := fun u =>
    ∑ n ∈ columns, weight n * finiteSquarefreeRow P hgood (support n) u
  have hone : A 1 = ∑ n ∈ columns, weight n := by
    dsimp [A]
    apply Finset.sum_congr rfl
    intro n hn
    rw [finiteSquarefreeRow_one]
    ring
  have hinjRows : Set.InjOn (fun i => p i ^ 6) (selected : Set β) := by
    apply sixth_power_rows_injective selected
      (fun i => (Ideal.span {p i} : Ideal O)) p
    · exact hprime
    · intro i hi; rfl
    · exact hinj
  have happrox : ∀ i ∈ selected,
      ‖A 1 - A (p i ^ 6)‖ ≤ C * (D : ℝ) ^ (49 / 60 : ℝ) := by
    intro i hi
    rw [hone]
    change ‖(∑ n ∈ columns, weight n) -
      (∑ n ∈ columns,
        weight n * finiteSquarefreeRow P hgood (support n) (p i ^ 6))‖ ≤ _
    exact (prime_sixth_row_approx_ideal_norm P hgood columns support
      weight (p i) (hp i hi) (hprime i hi) D hsupport hcolnorm hweight).trans
      (hrowbound i hi)
  have hmean' : (∑ u ∈ rows, ‖A u‖ ^ 2) ≤
      (D : ℝ) ^ ((21 / 10 : ℝ) + ε) := hmean
  have hbound := PowerExtraction.from_finite_sixth_power_rows_with_constant
    rows selected (fun i => p i ^ 6) A 1 (D : ℝ) ε C
    (by exact_mod_cast hD) hε hC hrows hinjRows happrox hcount hmean'
  simpa only [hone] using hbound

end ActualEisensteinCubic

namespace PowerExtraction

theorem dyadic_prime_error_bound (D N : ℕ) (hD : 1 ≤ D)
    (hN : (D : ℝ) ^ (11 / 60 : ℝ) / 2 ≤ (N : ℝ)) :
    ((64 * (D / N + 1) : ℕ) : ℝ) ≤
      192 * (D : ℝ) ^ (49 / 60 : ℝ) := by
  have hDreal : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hDpos : (0 : ℝ) < D := lt_of_lt_of_le zero_lt_one hDreal
  have hYpos : 0 < (D : ℝ) ^ (11 / 60 : ℝ) :=
    Real.rpow_pos_of_pos hDpos _
  have hNpos : (0 : ℝ) < N := by linarith
  have hpow :
      (D : ℝ) ^ (49 / 60 : ℝ) *
        (D : ℝ) ^ (11 / 60 : ℝ) = D := by
    rw [← Real.rpow_add hDpos]
    norm_num
  have hfrac : (D : ℝ) / N ≤
      2 * (D : ℝ) ^ (49 / 60 : ℝ) := by
    apply (div_le_iff₀ hNpos).mpr
    calc
      (D : ℝ) =
          (D : ℝ) ^ (49 / 60 : ℝ) *
            (D : ℝ) ^ (11 / 60 : ℝ) := hpow.symm
      _ =
          (2 * (D : ℝ) ^ (49 / 60 : ℝ)) *
            ((D : ℝ) ^ (11 / 60 : ℝ) / 2) := by
              ring
      _ ≤ (2 * (D : ℝ) ^ (49 / 60 : ℝ)) * N :=
          mul_le_mul_of_nonneg_left hN (by positivity)
  have hcast : ((D / N : ℕ) : ℝ) ≤ (D : ℝ) / N :=
    Nat.cast_div_le
  have hone : (1 : ℝ) ≤ (D : ℝ) ^ (49 / 60 : ℝ) :=
    Real.one_le_rpow hDreal (by norm_num)
  have hnatcast : ((64 * (D / N + 1) : ℕ) : ℝ) =
      64 * (((D / N : ℕ) : ℝ) + 1) := by push_cast; ring
  rw [hnatcast]
  nlinarith

end PowerExtraction

namespace ActualEisensteinCubic

theorem cubicChar_unit_eq_one_of_card_mod_nine
    (P : Ideal O) [P.IsMaximal] (hgood : lambda ∉ P)
    (hcard : Nat.card (O ⧸ P) % 9 = 1) (u : Oˣ) :
    cubicChar P hgood (Ideal.Quotient.mk P (u : O)) = 1 := by
  let ζ := IsCyclotomicExtension.zeta_spec 3 ℚ K
  let η : Oˣ := (ζ.toInteger_isPrimitiveRoot.isUnit (by decide)).unit
  have hη : (η : O) = omega := rfl
  have hu : u ∈ ([1, -1, η, -η, η ^ 2, -η ^ 2] : List Oˣ) :=
    IsCyclotomicExtension.Rat.Three.Units.mem ζ u
  have hone : cubicChar P hgood (Ideal.Quotient.mk P omega) = 1 :=
    cubicChar_omega_eq_one_of_card_mod_nine P hgood hcard
  have hminus : cubicChar P hgood (-1 : O ⧸ P) = 1 :=
    A3_cubicChar_neg_one P hgood
  have hneg (x : O) :
      cubicChar P hgood (Ideal.Quotient.mk P (-x)) =
        cubicChar P hgood (Ideal.Quotient.mk P x) := by
    have hx : -x = (-1 : O) * x := by ring
    rw [hx, map_mul, map_mul, map_neg, map_one, hminus, one_mul]
  simp only [List.mem_cons] at hu
  rcases hu with h | h | h | h | h | h
  · rw [h]
    simp
  · rw [h]
    simpa only [Units.val_neg, Units.val_one, map_neg, map_one] using hminus
  · rw [h, hη]
    exact hone
  · rw [h, Units.val_neg, hneg, hη]
    exact hone
  · rw [h, Units.val_pow_eq_pow_val, hη, map_pow, map_pow, hone]
    norm_num
  · rcases h with h | h
    · rw [h, Units.val_neg, hneg, Units.val_pow_eq_pow_val, hη, map_pow, map_pow, hone]
      norm_num
    · simp at h

theorem cubicChar_omega_agree_of_card_mod_nine
    (P Q : Ideal O) [P.IsMaximal] [Q.IsMaximal]
    (hP : lambda ∉ P) (hQ : lambda ∉ Q)
    (hcard : Nat.card (O ⧸ P) % 9 = Nat.card (O ⧸ Q) % 9) :
    cubicChar P hP (Ideal.Quotient.mk P omega) =
      cubicChar Q hQ (Ideal.Quotient.mk Q omega) := by
  rw [cubicChar_omega P hP, cubicChar_omega Q hQ]
  apply ((omega_primitive.isOfFinOrder (by decide)).pow_inj_mod).mpr
  rw [← omega_primitive.eq_orderOf]
  have hPpos : 0 < Nat.card (O ⧸ P) := Nat.card_pos
  have hQpos : 0 < Nat.card (O ⧸ Q) := Nat.card_pos
  omega

theorem cubicChar_units_agree_of_card_mod_nine
    (P Q : Ideal O) [P.IsMaximal] [Q.IsMaximal]
    (hP : lambda ∉ P) (hQ : lambda ∉ Q)
    (hcard : Nat.card (O ⧸ P) % 9 = Nat.card (O ⧸ Q) % 9)
    (u : Oˣ) :
    cubicChar P hP (Ideal.Quotient.mk P (u : O)) =
      cubicChar Q hQ (Ideal.Quotient.mk Q (u : O)) := by
  let ζ := IsCyclotomicExtension.zeta_spec 3 ℚ K
  let η : Oˣ := (ζ.toInteger_isPrimitiveRoot.isUnit (by decide)).unit
  have hη : (η : O) = omega := rfl
  have hu : u ∈ ([1, -1, η, -η, η ^ 2, -η ^ 2] : List Oˣ) :=
    IsCyclotomicExtension.Rat.Three.Units.mem ζ u
  have hω := cubicChar_omega_agree_of_card_mod_nine P Q hP hQ hcard
  have hnegP := A3_cubicChar_neg_one P hP
  have hnegQ := A3_cubicChar_neg_one Q hQ
  have hminus (R : Ideal O) [R.IsMaximal] (hR : lambda ∉ R) (x : O) :
      cubicChar R hR (Ideal.Quotient.mk R (-x)) =
        cubicChar R hR (Ideal.Quotient.mk R x) := by
    have hx : -x = (-1 : O) * x := by ring
    rw [hx, map_mul, map_mul, map_neg, map_one,
      A3_cubicChar_neg_one R hR, one_mul]
  simp only [List.mem_cons] at hu
  rcases hu with h | h | h | h | h | h
  · rw [h]
    simp
  · rw [h]
    simpa only [Units.val_neg, Units.val_one, map_neg, map_one] using
      hnegP.trans hnegQ.symm
  · rw [h, hη]
    exact hω
  · rw [h, Units.val_neg, hminus P hP, hminus Q hQ, hη]
    exact hω
  · rw [h, Units.val_pow_eq_pow_val, hη, map_pow, map_pow,
      map_pow, map_pow, hω]
  · rcases h with h | h
    · rw [h, Units.val_neg, hminus P hP, hminus Q hQ,
        Units.val_pow_eq_pow_val, hη, map_pow, map_pow, map_pow, map_pow, hω]
    · simp at h

open EisensteinEmbedding ConcreteTraceCRT Complex
theorem eisenstein_coord_norm_zero (a b : ℤ)
    (h : a*a-a*b+b*b = 0) : a = 0 ∧ b = 0 := by
  have hs : (a-b)^2 + a^2 + b^2 = 0 := by nlinarith [h]
  have ha : a^2 = 0 := by
    nlinarith [sq_nonneg (a-b), sq_nonneg b]
  have hb : b^2 = 0 := by
    nlinarith [sq_nonneg (a-b), sq_nonneg a]
  constructor <;> nlinarith

theorem quadraticTraceModChar_coordinate (a b x y : ℤ)
    (hc : ActualEisensteinCoordinates.eval a b ≠ 0) :
    let c : O := ActualEisensteinCoordinates.eval a b
    let z : O := ActualEisensteinCoordinates.eval x y
    (eisTraceModChar ShortDraftTrace.breveE
      ConcreteBreveE.breveE_period_coordinates c hc)
      (Ideal.Quotient.mk (Ideal.span {c}) z ^ 2) =
      Complex.exp (2 * Real.pi * Complex.I *
        ((-b*x*x + 2*a*x*y + (b-a)*y*y : ℤ) : ℂ) /
        ((a*a-a*b+b*b : ℤ) : ℂ)) := by
  have hq : a*a-a*b+b*b ≠ 0 := by
    intro h
    obtain ⟨ha,hb⟩ := eisenstein_coord_norm_zero a b h
    subst a
    subst b
    exact hc (by simp [ActualEisensteinCoordinates.eval])
  change ShortDraftTrace.breveE
    (eisEmbedding (ActualEisensteinCoordinates.eval x y ^ 2) /
      (eisEmbedding (ActualEisensteinCoordinates.eval a b) * eisLam)) = _
  rw [map_pow, eisEmbedding_eval, eisEmbedding_eval]
  exact breveE_quadratic_coordinate a b x y hq

end ActualEisensteinCubic

namespace GaussianAbelPartition

theorem tsum_by_finite_fibers {A B : Type*} [Fintype B]
    (q : A → B) (f : A → ℂ) (hf : Summable f) :
    (∑' a : A, f a) =
      ∑ b : B, ∑' a : (q ⁻¹' {b}), f a.1 := by
  have h := (hf.hasSum.tsum_fiberwise q).tsum_eq
  simpa only [tsum_fintype] using h.symm

theorem tsum_periodic_weighted_partition {A B : Type*} [Fintype B]
    (q : A → B) (P : B → ℂ) (W : A → ℂ)
    (hf : Summable (fun a => P (q a) * W a)) :
    (∑' a : A, P (q a) * W a) =
      ∑ b : B, P b * ∑' a : (q ⁻¹' {b}), W a.1 := by
  rw [tsum_by_finite_fibers q _ hf]
  apply Finset.sum_congr rfl
  intro b hb
  calc
    (∑' a : (q ⁻¹' {b}), P (q a.1) * W a.1) =
        ∑' a : (q ⁻¹' {b}), P b * W a.1 := by
      apply tsum_congr
      intro a
      have ha : q a.1 = b := by
        simpa only [Set.mem_preimage, Set.mem_singleton_iff] using a.property
      rw [ha]
    _ = P b * ∑' a : (q ⁻¹' {b}), W a.1 := tsum_mul_left

open ConcreteTraceCRT ConcreteBreveE ActualEisensteinCubic

theorem actual_quadratic_gaussian_partition (c : O) (hc : c ≠ 0)
    (W : O → ℂ)
    (hsum : Summable (fun z : O =>
      (eisTraceModChar ShortDraftTrace.breveE breveE_period_coordinates c hc)
        ((Ideal.Quotient.mk (Ideal.span {c}) z) ^ 2) * W z)) :
    letI : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
    letI : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
    (∑' z : O,
      (eisTraceModChar ShortDraftTrace.breveE breveE_period_coordinates c hc)
        ((Ideal.Quotient.mk (Ideal.span {c}) z) ^ 2) * W z) =
      ∑ r : O ⧸ Ideal.span {c},
        (eisTraceModChar ShortDraftTrace.breveE breveE_period_coordinates c hc)
          (r ^ 2) *
          ∑' z : ((Ideal.Quotient.mk (Ideal.span {c})) ⁻¹' {r}), W z.1 := by
  let : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
  let : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
  exact tsum_periodic_weighted_partition
    (Ideal.Quotient.mk (Ideal.span {c}))
    (fun r => (eisTraceModChar ShortDraftTrace.breveE breveE_period_coordinates c hc)
      (r ^ 2)) W hsum

end GaussianAbelPartition

namespace ActualEisensteinCubic

theorem finite_actual_prime_extraction_dyadic
    {ι β : Type*} (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hgood : ∀ i, lambda ∉ P i)
    (columns : Finset O) (support : O → Finset ι) (weight : O → ℂ)
    (selected : Finset β) (p : β → O) (rows : Finset O)
    (D : ℕ) (ε : ℝ) (hD : 1 ≤ D) (hε : 0 ≤ ε)
    (hp : ∀ i ∈ selected, p i ≠ 0)
    (hprime : ∀ i ∈ selected, (Ideal.span {p i} : Ideal O).IsMaximal)
    (hinj : Set.InjOn (fun i => (Ideal.span {p i} : Ideal O)) (selected : Set β))
    (hrows : selected.image (fun i => p i ^ 6) ⊆ rows)
    (hsupport : ∀ n ∈ columns, ∀ i ∈ support n, n ∈ P i)
    (hcolnorm : ∀ n ∈ columns, Ideal.absNorm (Ideal.span {n}) ≤ D)
    (hweight : ∀ n ∈ columns, ‖weight n‖ ≤ 1)
    (hnormlower : ∀ i ∈ selected,
      (D : ℝ) ^ (11 / 60 : ℝ) / 2 ≤
        (Ideal.absNorm (Ideal.span {p i}) : ℝ))
    (hcount : (D : ℝ) ^ ((11 / 60 : ℝ) - ε) ≤ (selected.card : ℝ))
    (hmean :
      (∑ u ∈ rows,
        ‖∑ n ∈ columns,
          weight n * finiteSquarefreeRow P hgood (support n) u‖ ^ 2) ≤
        (D : ℝ) ^ ((21 / 10 : ℝ) + ε)) :
    ‖∑ n ∈ columns, weight n‖ ≤
      384 * (D : ℝ) ^ ((23 / 24 : ℝ) + ε) := by
  have hbound := finite_actual_prime_extraction_with_constant P hgood
    columns support weight selected p rows D ε 192 hD hε (by norm_num)
    hp hprime hinj hrows hsupport hcolnorm hweight
    (by
      intro i hi
      exact PowerExtraction.dyadic_prime_error_bound D
        (Ideal.absNorm (Ideal.span {p i})) hD (hnormlower i hi))
    hcount hmean
  simpa only [show (2 : ℝ) * 192 = 384 by norm_num] using hbound

end ActualEisensteinCubic

namespace GaussianFiberEquiv

open ActualEisensteinCubic

def fiberMap (c : O) (r : O ⧸ Ideal.span {c})
    (r0 : O) (hr : Ideal.Quotient.mk (Ideal.span {c}) r0 = r)
    (w : O) : ((Ideal.Quotient.mk (Ideal.span {c})) ⁻¹' {r}) := by
  refine ⟨r0 + c*w, ?_⟩
  change Ideal.Quotient.mk (Ideal.span {c}) (r0 + c*w) = r
  rw [map_add, map_mul]
  have hc0 : Ideal.Quotient.mk (Ideal.span {c}) c = 0 :=
    (Ideal.Quotient.eq_zero_iff_mem).mpr (Ideal.subset_span (Set.mem_singleton c))
  rw [hc0, zero_mul, add_zero, hr]

private theorem fiberMap_injective (c : O) (hc : c ≠ 0)
    (r : O ⧸ Ideal.span {c}) (r0 : O)
    (hr : Ideal.Quotient.mk (Ideal.span {c}) r0 = r) :
    Function.Injective (fiberMap c r r0 hr) := by
  intro u v h
  have hval := congrArg Subtype.val h
  change r0 + c*u = r0 + c*v at hval
  exact mul_left_cancel₀ hc (add_left_cancel hval)

private theorem fiberMap_surjective (c : O)
    (r : O ⧸ Ideal.span {c}) (r0 : O)
    (hr : Ideal.Quotient.mk (Ideal.span {c}) r0 = r) :
    Function.Surjective (fiberMap c r r0 hr) := by
  rintro ⟨z, hz⟩
  have hz' : Ideal.Quotient.mk (Ideal.span {c}) z = r := by
    simpa only [Set.mem_preimage, Set.mem_singleton_iff] using hz
  have hdiff : z-r0 ∈ Ideal.span {c} :=
    (Ideal.Quotient.mk_eq_mk_iff_sub_mem z r0).mp (hz'.trans hr.symm)
  obtain ⟨w, hw⟩ := (Ideal.mem_span_singleton).mp hdiff
  refine ⟨w, ?_⟩
  apply Subtype.ext
  change r0 + c*w = z
  rw [← hw]
  ring

noncomputable def fiberEquiv (c : O) (hc : c ≠ 0)
    (r : O ⧸ Ideal.span {c}) (r0 : O)
    (hr : Ideal.Quotient.mk (Ideal.span {c}) r0 = r) :
    O ≃ ((Ideal.Quotient.mk (Ideal.span {c})) ⁻¹' {r}) :=
  Equiv.ofBijective (fiberMap c r r0 hr)
    ⟨fiberMap_injective c hc r r0 hr, fiberMap_surjective c r r0 hr⟩

theorem fiber_tsum (c : O) (hc : c ≠ 0)
    (r : O ⧸ Ideal.span {c}) (r0 : O)
    (hr : Ideal.Quotient.mk (Ideal.span {c}) r0 = r)
    (W : O → ℂ) :
    (∑' z : ((Ideal.Quotient.mk (Ideal.span {c})) ⁻¹' {r}), W z.1) =
      ∑' w : O, W (r0 + c*w) := by
  have h := (fiberEquiv c hc r r0 hr).tsum_eq (fun z => W z.1)
  have happ (w : O) : ((fiberEquiv c hc r r0 hr) w).1 = r0 + c*w := rfl
  simpa only [happ] using h.symm

end GaussianFiberEquiv

namespace RankTwoPoisson

open Real

theorem schwartz_int_summable (f : 𝓢(ℝ, ℂ)) :
    Summable (fun n : ℤ => f (n : ℝ)) := by
  exact summable_of_isBigO (Real.summable_abs_int_rpow (show (1 : ℝ) < 2 by norm_num))
    ((f.isBigO_cocompact_rpow (-2)).comp_tendsto Int.tendsto_coe_cofinite)

theorem schwartz_int_norm_summable (f : 𝓢(ℝ, ℂ)) :
    Summable (fun n : ℤ => ‖f (n : ℝ)‖) :=
  (schwartz_int_summable f).norm

theorem schwartz_int_poisson (f : 𝓢(ℝ, ℂ)) :
    (∑' n : ℤ, f (n : ℝ)) = ∑' n : ℤ, (𝓕 f) (n : ℝ) := by
  simpa [fourier_eval_zero] using
    SchwartzMap.tsum_eq_tsum_fourier f 0

theorem tensor_poisson (f g : 𝓢(ℝ, ℂ)) :
    (∑' z : ℤ × ℤ, f (z.1 : ℝ) * g (z.2 : ℝ)) =
      ∑' z : ℤ × ℤ, (𝓕 f) (z.1 : ℝ) * (𝓕 g) (z.2 : ℝ) := by
  calc
    (∑' z : ℤ × ℤ, f (z.1 : ℝ) * g (z.2 : ℝ)) =
        (∑' m : ℤ, f (m : ℝ)) * (∑' n : ℤ, g (n : ℝ)) :=
      (tsum_mul_tsum_of_summable_norm
        (schwartz_int_norm_summable f) (schwartz_int_norm_summable g)).symm
    _ = (∑' m : ℤ, (𝓕 f) (m : ℝ)) * (∑' n : ℤ, (𝓕 g) (n : ℝ)) :=
      congrArg₂ (· * ·) (schwartz_int_poisson f) (schwartz_int_poisson g)
    _ = ∑' z : ℤ × ℤ, (𝓕 f) (z.1 : ℝ) * (𝓕 g) (z.2 : ℝ) :=
      tsum_mul_tsum_of_summable_norm
        (schwartz_int_norm_summable (𝓕 f))
        (schwartz_int_norm_summable (𝓕 g))
  rfl

private theorem gauss_int_summable {a : ℂ} (ha : 0 < a.re) :
    Summable (fun n : ℤ => Complex.exp (-((Real.pi : ℂ) * a) * (n : ℂ) ^ 2)) := by
  have hpa : 0 < ((Real.pi : ℂ) * a).re := by
    simpa using mul_pos Real.pi_pos ha
  exact summable_of_isBigO (Real.summable_abs_int_rpow (show (1 : ℝ) < 2 by norm_num))
    ((isLittleO_exp_neg_mul_sq_cocompact hpa (-2)).isBigO.comp_tendsto
      Int.tendsto_coe_cofinite)

noncomputable def cg (a : ℂ) (n : ℤ) : ℂ :=
  Complex.exp (-((Real.pi : ℂ) * a) * (n : ℂ) ^ 2)

private theorem cg_summable {a : ℂ} (ha : 0 < a.re) : Summable (cg a) :=
  gauss_int_summable ha

private theorem cg_poisson {a : ℂ} (ha : 0 < a.re) :
    (∑' n : ℤ, cg a n) =
      (1 / a ^ (1 / 2 : ℂ)) * ∑' n : ℤ, cg a⁻¹ n := by
  simpa only [cg, div_eq_mul_inv, neg_mul, mul_assoc] using
    Complex.tsum_exp_neg_mul_int_sq ha

theorem diagonal_gaussian_poisson {a b : ℂ}
    (ha : 0 < a.re) (hb : 0 < b.re)
    (hai : 0 < (a⁻¹).re) (hbi : 0 < (b⁻¹).re) :
    (∑' z : ℤ × ℤ, cg a z.1 * cg b z.2) =
      (1 / a ^ (1 / 2 : ℂ)) * (1 / b ^ (1 / 2 : ℂ)) *
        ∑' z : ℤ × ℤ, cg a⁻¹ z.1 * cg b⁻¹ z.2 := by
  calc
    (∑' z : ℤ × ℤ, cg a z.1 * cg b z.2) =
        (∑' m : ℤ, cg a m) * (∑' n : ℤ, cg b n) :=
      (tsum_mul_tsum_of_summable_norm (cg_summable ha).norm (cg_summable hb).norm).symm
    _ = ((1 / a ^ (1 / 2 : ℂ)) * ∑' m : ℤ, cg a⁻¹ m) *
        ((1 / b ^ (1 / 2 : ℂ)) * ∑' n : ℤ, cg b⁻¹ n) := by
      rw [cg_poisson ha, cg_poisson hb]
    _ = (1 / a ^ (1 / 2 : ℂ)) * (1 / b ^ (1 / 2 : ℂ)) *
        ∑' z : ℤ × ℤ, cg a⁻¹ z.1 * cg b⁻¹ z.2 := by
      rw [← tsum_mul_tsum_of_summable_norm (cg_summable hai).norm (cg_summable hbi).norm]
      ring

theorem real_gauss_summable {t : ℝ} (ht : 0 < t) :
    Summable (fun n : ℤ => Real.exp (-Real.pi * t * (n : ℝ) ^ 2)) := by
  have htc : 0 < (t : ℂ).re := by simpa using ht
  have h := (cg_summable htc).norm
  simpa [cg, Complex.norm_exp, ← Complex.ofReal_intCast, ← Complex.ofReal_pow, mul_assoc] using h

noncomputable def eisQ (z : ℤ × ℤ) : ℝ :=
  (z.1 : ℝ) ^ 2 - (z.1 : ℝ) * (z.2 : ℝ) + (z.2 : ℝ) ^ 2

noncomputable def eisGauss (t : ℝ) (z : ℤ × ℤ) : ℂ :=
  Complex.exp ((-Real.pi * t * eisQ z : ℝ) : ℂ)

theorem eisQ_lower (z : ℤ × ℤ) :
    ((z.1 : ℝ) ^ 2 + (z.2 : ℝ) ^ 2) / 2 ≤ eisQ z := by
  dsimp [eisQ]
  nlinarith [sq_nonneg ((z.1 : ℝ) - (z.2 : ℝ))]

theorem eis_gauss_summable {t : ℝ} (ht : 0 < t) :
    Summable (eisGauss t) := by
  have ht2 : 0 < t / 2 := by positivity
  have h1 := real_gauss_summable ht2
  have hmaj : Summable (fun z : ℤ × ℤ =>
      Real.exp (-Real.pi * (t / 2) * (z.1 : ℝ) ^ 2) *
      Real.exp (-Real.pi * (t / 2) * (z.2 : ℝ) ^ 2)) :=
    h1.mul_of_nonneg h1 (fun _ => (Real.exp_pos _).le) (fun _ => (Real.exp_pos _).le)
  refine hmaj.of_norm_bounded ?_
  intro z
  have hq := eisQ_lower z
  have hpi : 0 ≤ Real.pi * t := (mul_pos Real.pi_pos ht).le
  have hmul := mul_le_mul_of_nonneg_left hq hpi
  have hexp : -Real.pi * t * eisQ z ≤
      -Real.pi * (t / 2) * (z.1 : ℝ) ^ 2 +
      -Real.pi * (t / 2) * (z.2 : ℝ) ^ 2 := by
    nlinarith [hmul]
  simpa [eisGauss, Complex.norm_exp, Real.exp_add] using
    (Real.exp_le_exp.mpr hexp)

private noncomputable def phase (k n : ℤ) : ℂ :=
  Complex.exp (((-Real.pi * (k : ℝ) * (n : ℝ) : ℝ) : ℂ) * Complex.I)

private noncomputable def g1 (t : ℝ) (z : ℤ × ℤ) : ℂ :=
  cg ((t⁻¹ : ℝ) : ℂ) z.1 * cg (((3 * t) / 4 : ℝ) : ℂ) z.2 * phase z.1 z.2

private theorem phase_norm (k n : ℤ) : ‖phase k n‖ = 1 := by
  simp [phase, Complex.norm_exp, Complex.mul_re]

private theorem g1_summable {t : ℝ} (ht : 0 < t) : Summable (g1 t) := by
  have htinv : 0 < t⁻¹ := inv_pos.mpr ht
  have ht3 : 0 < 3 * t / 4 := by positivity
  have h1 := (cg_summable (a := ((t⁻¹ : ℝ) : ℂ)) (by simpa using htinv)).norm
  have h2 := (cg_summable (a := (((3 * t) / 4 : ℝ) : ℂ)) (by simpa using ht3)).norm
  have hmaj : Summable (fun z : ℤ × ℤ =>
      ‖cg ((t⁻¹ : ℝ) : ℂ) z.1‖ * ‖cg (((3 * t) / 4 : ℝ) : ℂ) z.2‖) :=
    h1.mul_of_nonneg h2 (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
  refine hmaj.of_norm_bounded ?_
  intro z
  simp [g1,  phase_norm]

private theorem eisGauss_split (t : ℝ) (m n : ℤ) :
    eisGauss t (m, n) =
      Complex.exp ((-Real.pi * t * (n : ℝ) ^ 2 : ℝ) : ℂ) *
        Complex.exp (-(Real.pi : ℂ) * (t : ℂ) * (m : ℂ) ^ 2 +
          2 * (Real.pi : ℂ) * (((t : ℂ) * (n : ℂ)) / 2) * (m : ℂ)) := by
  dsimp [eisGauss, eisQ]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

private theorem eis_exponent_identity {t : ℝ} (ht : 0 < t) (k n : ℤ) :
    (-(Real.pi : ℂ) * (t : ℂ) * (n : ℂ) ^ 2) +
      (-(Real.pi : ℂ) / (t : ℂ) *
        ((k : ℂ) + Complex.I * ((t : ℂ) * (n : ℂ) / 2)) ^ 2) =
      (-(Real.pi : ℂ) * (((t⁻¹ : ℝ) : ℂ)) * (k : ℂ) ^ 2) +
        (-(Real.pi : ℂ) * ((((3 * t) / 4 : ℝ) : ℂ)) * (n : ℂ) ^ 2) +
        (((-Real.pi * (k : ℝ) * (n : ℝ) : ℝ) : ℂ) * Complex.I) := by
  have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt ht
  push_cast
  field_simp [ht0]
  ring_nf
  simp [Complex.I_sq]
  ring

private theorem first_transform_term {t : ℝ} (ht : 0 < t) (k n : ℤ) :
    Complex.exp ((-Real.pi * t * (n : ℝ) ^ 2 : ℝ) : ℂ) *
      Complex.exp (-(Real.pi : ℂ) / (t : ℂ) *
        ((k : ℂ) + Complex.I * (((t : ℂ) * (n : ℂ)) / 2)) ^ 2) =
      g1 t (k, n) := by
  have hn : ((-Real.pi * t * (n : ℝ) ^ 2 : ℝ) : ℂ) =
      -(Real.pi : ℂ) * (t : ℂ) * (n : ℂ) ^ 2 := by
    push_cast
    ring
  rw [hn, ← Complex.exp_add, eis_exponent_identity ht k n]
  simp only [Complex.exp_add]
  dsimp [g1, cg, phase]
  push_cast
  ring_nf

private theorem first_poisson_slice {t : ℝ} (ht : 0 < t) (n : ℤ) :
    (∑' m : ℤ, eisGauss t (m, n)) =
      (1 / (t : ℂ) ^ (1 / 2 : ℂ)) * ∑' k : ℤ, g1 t (k, n) := by
  have htc : 0 < (t : ℂ).re := by simpa using ht
  let C : ℂ := Complex.exp ((-Real.pi * t * (n : ℝ) ^ 2 : ℝ) : ℂ)
  let B : ℂ := ((t : ℂ) * (n : ℂ)) / 2
  let F : ℤ → ℂ := fun m => Complex.exp
    (-(Real.pi : ℂ) * (t : ℂ) * (m : ℂ) ^ 2 +
      2 * (Real.pi : ℂ) * B * (m : ℂ))
  let H : ℤ → ℂ := fun k => Complex.exp
    (-(Real.pi : ℂ) / (t : ℂ) * ((k : ℂ) + Complex.I * B) ^ 2)
  have hsplit : (∑' m : ℤ, eisGauss t (m, n)) = C * ∑' m : ℤ, F m := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro m
    exact eisGauss_split t m n
  have hpoisson : (∑' m : ℤ, F m) =
      (1 / (t : ℂ) ^ (1 / 2 : ℂ)) * ∑' k : ℤ, H k := by
    exact Complex.tsum_exp_neg_quadratic htc B
  calc
    (∑' m : ℤ, eisGauss t (m, n)) = C * ∑' m : ℤ, F m := hsplit
    _ = C * ((1 / (t : ℂ) ^ (1 / 2 : ℂ)) * ∑' k : ℤ, H k) := by rw [hpoisson]
    _ = (1 / (t : ℂ) ^ (1 / 2 : ℂ)) * (C * ∑' k : ℤ, H k) := by ring
    _ = (1 / (t : ℂ) ^ (1 / 2 : ℂ)) * ∑' k : ℤ, g1 t (k, n) := by
      congr 1
      rw [← tsum_mul_left]
      apply tsum_congr
      intro k
      exact first_transform_term ht k n

private noncomputable def dualTerm (t : ℝ) (z : ℤ × ℤ) : ℂ :=
  cg ((t⁻¹ : ℝ) : ℂ) z.1 *
    Complex.exp (-(Real.pi : ℂ) / (((3 * t) / 4 : ℝ) : ℂ) *
      ((z.2 : ℂ) + (z.1 : ℂ) / 2) ^ 2)

private theorem second_transform_term (t : ℝ) (k n : ℤ) :
    cg ((((3 * t) / 4 : ℝ) : ℂ)) n * phase k n =
      Complex.exp (-(Real.pi : ℂ) * ((((3 * t) / 4 : ℝ) : ℂ)) * (n : ℂ) ^ 2 +
        2 * (Real.pi : ℂ) * (-(Complex.I * (k : ℂ)) / 2) * (n : ℂ)) := by
  dsimp [cg, phase]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

private theorem second_poisson_slice {t : ℝ} (ht : 0 < t) (k : ℤ) :
    (∑' n : ℤ, g1 t (k, n)) =
      (1 / ((((3 * t) / 4 : ℝ) : ℂ)) ^ (1 / 2 : ℂ)) *
        ∑' l : ℤ, dualTerm t (k, l) := by
  have ht3 : 0 < 3 * t / 4 := by positivity
  have ht3c : 0 < (((3 * t) / 4 : ℝ) : ℂ).re := by simpa using ht3
  let A : ℂ := (((3 * t) / 4 : ℝ) : ℂ)
  let B : ℂ := -(Complex.I * (k : ℂ)) / 2
  let C : ℂ := cg ((t⁻¹ : ℝ) : ℂ) k
  let F : ℤ → ℂ := fun n => Complex.exp
    (-(Real.pi : ℂ) * A * (n : ℂ) ^ 2 + 2 * (Real.pi : ℂ) * B * (n : ℂ))
  let H : ℤ → ℂ := fun l => Complex.exp
    (-(Real.pi : ℂ) / A * ((l : ℂ) + Complex.I * B) ^ 2)
  have hsplit : (∑' n : ℤ, g1 t (k,n)) = C * ∑' n : ℤ, F n := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro n
    calc
      g1 t (k, n) = C * (cg A n * phase k n) := by
        dsimp [g1, C, A]
        ring
      _ = C * F n := by rw [second_transform_term t k n]
  have hpoisson : (∑' n : ℤ, F n) =
      (1 / A ^ (1 / 2 : ℂ)) * ∑' l : ℤ, H l :=
    Complex.tsum_exp_neg_quadratic ht3c B
  have hterm (l : ℤ) : C * H l = dualTerm t (k,l) := by
    have hb : Complex.I * B = (k : ℂ) / 2 := by
      dsimp [B]
      field_simp
      ring_nf
      simp [Complex.I_sq]
    dsimp [H, dualTerm, C, A]
    rw [hb]
  calc
    (∑' n : ℤ, g1 t (k,n)) = C * ∑' n : ℤ, F n := hsplit
    _ = C * ((1 / A ^ (1 / 2 : ℂ)) * ∑' l : ℤ, H l) := by rw [hpoisson]
    _ = (1 / A ^ (1 / 2 : ℂ)) * (C * ∑' l : ℤ, H l) := by ring
    _ = (1 / ((((3 * t) / 4 : ℝ) : ℂ)) ^ (1 / 2 : ℂ)) *
          ∑' l : ℤ, dualTerm t (k,l) := by
      change (1 / A ^ (1 / 2 : ℂ)) * (C * ∑' l : ℤ, H l) =
        (1 / A ^ (1 / 2 : ℂ)) * ∑' l : ℤ, dualTerm t (k,l)
      congr 1
      rw [← tsum_mul_left]
      exact tsum_congr hterm

theorem eisenstein_gaussian_poisson_iterated {t : ℝ} (ht : 0 < t) :
    (∑' z : ℤ × ℤ, eisGauss t z) =
      (1 / (t : ℂ) ^ (1 / 2 : ℂ)) *
        (1 / ((((3 * t) / 4 : ℝ) : ℂ)) ^ (1 / 2 : ℂ)) *
        ∑' k : ℤ, ∑' l : ℤ, dualTerm t (k,l) := by
  have hE := eis_gauss_summable ht
  have hG := g1_summable ht
  have hEcomm :
      (∑' n : ℤ, ∑' m : ℤ, eisGauss t (m,n)) =
        ∑' m : ℤ, ∑' n : ℤ, eisGauss t (m,n) :=
    (show Summable (Function.uncurry (fun m n : ℤ => eisGauss t (m,n))) from hE).tsum_comm
  have hGcomm :
      (∑' n : ℤ, ∑' k : ℤ, g1 t (k,n)) =
        ∑' k : ℤ, ∑' n : ℤ, g1 t (k,n) :=
    (show Summable (Function.uncurry (fun k n : ℤ => g1 t (k,n))) from hG).tsum_comm
  calc
    (∑' z : ℤ × ℤ, eisGauss t z) =
        ∑' m : ℤ, ∑' n : ℤ, eisGauss t (m,n) := hE.tsum_prod
    _ = ∑' n : ℤ, ∑' m : ℤ, eisGauss t (m,n) := hEcomm.symm
    _ = ∑' n : ℤ, (1 / (t : ℂ) ^ (1 / 2 : ℂ)) *
          ∑' k : ℤ, g1 t (k,n) := by
      apply tsum_congr
      intro n
      exact first_poisson_slice ht n
    _ = (1 / (t : ℂ) ^ (1 / 2 : ℂ)) *
          (∑' n : ℤ, ∑' k : ℤ, g1 t (k,n)) := tsum_mul_left
    _ = (1 / (t : ℂ) ^ (1 / 2 : ℂ)) *
          (∑' k : ℤ, ∑' n : ℤ, g1 t (k,n)) := by
      rw [hGcomm]
    _ = (1 / (t : ℂ) ^ (1 / 2 : ℂ)) *
          (∑' k : ℤ, (1 / ((((3 * t) / 4 : ℝ) : ℂ)) ^ (1 / 2 : ℂ)) *
            ∑' l : ℤ, dualTerm t (k,l)) := by
      congr 1
      apply tsum_congr
      intro k
      exact second_poisson_slice ht k
    _ = (1 / (t : ℂ) ^ (1 / 2 : ℂ)) *
          (1 / ((((3 * t) / 4 : ℝ) : ℂ)) ^ (1 / 2 : ℂ)) *
          ∑' k : ℤ, ∑' l : ℤ, dualTerm t (k,l) := by
      rw [tsum_mul_left]
      ring

private theorem dualTerm_eq_eisGauss {t : ℝ} (ht : 0 < t) (k l : ℤ) :
    dualTerm t (k,l) = eisGauss (4 / (3 * t)) (k,-l) := by
  have ht0 : t ≠ 0 := ne_of_gt ht
  dsimp [dualTerm, cg, eisGauss, eisQ]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  field_simp [ht0]
  ring

private theorem dualTerm_summable {t : ℝ} (ht : 0 < t) :
    Summable (dualTerm t) := by
  have htd : 0 < 4 / (3 * t) := by positivity
  let e : ℤ × ℤ ≃ ℤ × ℤ :=
    Equiv.prodCongr (Equiv.refl ℤ) (Equiv.neg ℤ)
  have h := (e.summable_iff).2 (eis_gauss_summable htd)
  apply h.congr
  intro z
  change eisGauss (4 / (3 * t)) (z.1, -z.2) = dualTerm t z
  exact (dualTerm_eq_eisGauss ht z.1 z.2).symm

theorem eisenstein_gaussian_poisson {t : ℝ} (ht : 0 < t) :
    (∑' z : ℤ × ℤ, eisGauss t z) =
      (1 / (t : ℂ) ^ (1 / 2 : ℂ)) *
        (1 / ((((3 * t) / 4 : ℝ) : ℂ)) ^ (1 / 2 : ℂ)) *
        ∑' z : ℤ × ℤ, eisGauss (4 / (3 * t)) z := by
  let e : ℤ × ℤ ≃ ℤ × ℤ :=
    Equiv.prodCongr (Equiv.refl ℤ) (Equiv.neg ℤ)
  have hdual : (∑' z : ℤ × ℤ, dualTerm t z) =
      ∑' z : ℤ × ℤ, eisGauss (4 / (3 * t)) z := by
    calc
      (∑' z : ℤ × ℤ, dualTerm t z) =
          ∑' z : ℤ × ℤ, eisGauss (4 / (3 * t)) (e z) := by
        apply tsum_congr
        intro z
        exact dualTerm_eq_eisGauss ht z.1 z.2
      _ = ∑' z : ℤ × ℤ, eisGauss (4 / (3 * t)) z :=
        Equiv.tsum_eq e _
  calc
    (∑' z : ℤ × ℤ, eisGauss t z) =
        (1 / (t : ℂ) ^ (1 / 2 : ℂ)) *
          (1 / ((((3 * t) / 4 : ℝ) : ℂ)) ^ (1 / 2 : ℂ)) *
          (∑' k : ℤ, ∑' l : ℤ, dualTerm t (k,l)) :=
      eisenstein_gaussian_poisson_iterated ht
    _ = (1 / (t : ℂ) ^ (1 / 2 : ℂ)) *
          (1 / ((((3 * t) / 4 : ℝ) : ℂ)) ^ (1 / 2 : ℂ)) *
          (∑' z : ℤ × ℤ, dualTerm t z) := by
      rw [(dualTerm_summable ht).tsum_prod]
    _ = _ := by rw [hdual]

end RankTwoPoisson

end

end OAI

end


