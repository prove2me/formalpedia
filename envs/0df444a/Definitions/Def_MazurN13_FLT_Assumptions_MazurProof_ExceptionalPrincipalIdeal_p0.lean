-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_ExceptionalPrincipalIdeal_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_ExceptionalPrincipalIdeal_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-07T22:17:35.805527+00:00
-- url     : https://prove2.me/theorems/f0fec7af-ac1b-459b-b17e-ac32c3645b9f
-- title:
--   FLT.Assumptions.MazurProof.ExceptionalPrincipalIdeal source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.ExceptionalPrincipalIdeal

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.ExceptionalPrincipalIdeal
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_EvenPrincipalIdeal_p0
import Mathlib.Data.ZMod.Basic

set_option autoImplicit false




/-!
# Principal ideals with two exceptional carriers

In a Dedekind PID, even height-one counts away from two explicit principal
primes leave exactly two parity bits.  The proof extracts those bits from
the ideal factorization, removes the corresponding integral carriers, and
halves the remaining factorization through EvenPrincipalIdeal.

No height-one primes are enumerated and no ideal-class computation is used.
-/

open scoped nonZeroDivisors

open IsDedekindDomain
open UniqueFactorizationMonoid

noncomputable section

namespace MazurProof.ExceptionalPrincipalIdeal

open EvenPrincipalIdeal

variable {O L : Type*}
variable [CommRing O] [IsDedekindDomain O]
variable [Field L] [Algebra O L] [IsFractionRing O L]

theorem factorization_heightOne_self
    (P : HeightOneSpectrum O) :
    factorization P.asIdeal P.asIdeal = 1 := by
  classical
  rw [factorization_eq_count,
    normalizedFactors_irreducible P.irreducible]
  simp

theorem factorization_heightOne_apply_of_ne
    (P R : HeightOneSpectrum O)
    (hRP : R ≠ P) :
    factorization P.asIdeal R.asIdeal = 0 := by
  classical
  rw [factorization_eq_count,
    normalizedFactors_irreducible P.irreducible]
  have hideal : R.asIdeal ≠ P.asIdeal := by
    intro h
    apply hRP
    exact HeightOneSpectrum.ext h
  simp [hideal]

theorem principalCount_mul
    {a b : O} (ha : a ≠ 0) (hb : b ≠ 0)
    (R : HeightOneSpectrum O) :
    principalCount (L := L) R (a * b) =
      principalCount (L := L) R a +
        principalCount (L := L) R b := by
  have haL : algebraMap O L a ≠ 0 :=
    by
      simpa only [map_zero] using
        (IsFractionRing.injective O L).ne ha
  have hbL : algebraMap O L b ≠ 0 :=
    by
      simpa only [map_zero] using
        (IsFractionRing.injective O L).ne hb
  unfold principalCount
  rw [map_mul,
    ← FractionalIdeal.spanSingleton_mul_spanSingleton,
    FractionalIdeal.count_mul L R
      (FractionalIdeal.spanSingleton_ne_zero_iff.mpr haL)
      (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hbL)]

theorem principalCount_pow
    (a : O) (n : ℕ)
    (R : HeightOneSpectrum O) :
    principalCount (L := L) R (a ^ n) =
      (n : ℤ) * principalCount (L := L) R a := by
  unfold principalCount
  rw [map_pow, ← FractionalIdeal.spanSingleton_pow,
    FractionalIdeal.count_pow]

theorem principalCount_generator_self
    {A : O} (P : HeightOneSpectrum O)
    (hA : P.asIdeal =
      Ideal.span ({A} : Set O))
    (hA0 : A ≠ 0) :
    principalCount (L := L) P A = 1 := by
  rw [principalCount_eq_factorization_span A hA0 P,
    ← hA, factorization_heightOne_self]
  norm_num

theorem principalCount_generator_of_ne
    {A : O} (P R : HeightOneSpectrum O)
    (hA : P.asIdeal =
      Ideal.span ({A} : Set O))
    (hA0 : A ≠ 0)
    (hRP : R ≠ P) :
    principalCount (L := L) R A = 0 := by
  rw [principalCount_eq_factorization_span A hA0 R,
    ← hA, factorization_heightOne_apply_of_ne P R hRP]
  norm_num

/-- An oriented ideal factorization with two explicit principal carriers
immediately gives an element factorization. -/
theorem exists_unit_two_carriers_mul_sq_of_ideal_factorization
    [IsPrincipalIdealRing O]
    {x A Q : O} {r q : ℕ}
    (J : Ideal O)
    (h :
      Ideal.span ({x} : Set O) =
        (Ideal.span ({A} : Set O)) ^ r *
          (Ideal.span ({Q} : Set O)) ^ q *
            J ^ 2) :
    ∃ ε : Oˣ, ∃ y : O,
      x = (ε : O) * A ^ r * Q ^ q * y ^ 2 := by
  let y : O := Submodule.IsPrincipal.generator J
  have hJ :
      Ideal.span ({y} : Set O) = J :=
    Ideal.span_singleton_generator J
  have hspan :
      Ideal.span ({x} : Set O) =
        Ideal.span
          ({A ^ r * Q ^ q * y ^ 2} : Set O) := by
    calc
      Ideal.span ({x} : Set O) =
          (Ideal.span ({A} : Set O)) ^ r *
            (Ideal.span ({Q} : Set O)) ^ q *
              J ^ 2 := h
      _ =
          Ideal.span ({A ^ r} : Set O) *
            Ideal.span ({Q ^ q} : Set O) *
              Ideal.span ({y ^ 2} : Set O) := by
        rw [← hJ, Ideal.span_singleton_pow,
          Ideal.span_singleton_pow,
          Ideal.span_singleton_pow]
      _ =
          Ideal.span
            ({A ^ r * Q ^ q * y ^ 2} : Set O) := by
        rw [Ideal.span_singleton_mul_span_singleton,
          Ideal.span_singleton_mul_span_singleton]
  have hassoc :
      Associated x (A ^ r * Q ^ q * y ^ 2) :=
    Ideal.span_singleton_eq_span_singleton.mp hspan
  rcases hassoc.symm with ⟨ε, hε⟩
  refine ⟨ε, y, ?_⟩
  simpa [mul_assoc, mul_left_comm, mul_comm] using hε.symm

/-- If every height-one count away from two explicit principal primes is
even, only the two parity bits of those primes remain. -/
theorem exists_unit_two_carriers_mul_sq_of_even_away
    [IsPrincipalIdealRing O]
    (P Q : HeightOneSpectrum O)
    (hPQ : P ≠ Q)
    (A Qelt x : O)
    (hPgen :
      P.asIdeal = Ideal.span ({A} : Set O))
    (hQgen :
      Q.asIdeal = Ideal.span ({Qelt} : Set O))
    (hx : x ≠ 0)
    (hAway :
      ∀ R : HeightOneSpectrum O,
        R ≠ P → R ≠ Q →
          Even (principalCount (L := L) R x)) :
    ∃ r q : ZMod 2, ∃ ε : Oˣ, ∃ y : O,
      x =
        (ε : O) * A ^ r.val *
          Qelt ^ q.val * y ^ 2 := by
  classical
  let I : Ideal O :=
    Ideal.span ({x} : Set O)
  let nP : ℕ := factorization I P.asIdeal
  let nQ : ℕ := factorization I Q.asIdeal
  let rN : ℕ := nP % 2
  let qN : ℕ := nQ % 2
  have hrN_lt : rN < 2 := by
    exact Nat.mod_lt _ (by omega)
  have hqN_lt : qN < 2 := by
    exact Nat.mod_lt _ (by omega)
  have hA0 : A ≠ 0 := by
    intro hzero
    apply P.ne_bot
    rw [hPgen, hzero]
    simp
  have hQ0 : Qelt ≠ 0 := by
    intro hzero
    apply Q.ne_bot
    rw [hQgen, hzero]
    simp
  have hxP_of_rN_eq_one
      (hr : rN = 1) :
      x ∈ P.asIdeal := by
    have hnP : nP ≠ 0 := by
      intro hzero
      simp [rN, hzero] at hr
    have hPmem :
        P.asIdeal ∈ normalizedFactors I := by
      rw [← Multiset.count_ne_zero]
      simpa [nP, factorization_eq_count] using hnP
    have hPdvd :
        P.asIdeal ∣ I :=
      dvd_of_mem_normalizedFactors hPmem
    exact
      (Ideal.dvd_span_singleton.mp
        (by simpa only [I] using hPdvd))
  have hxQ_of_qN_eq_one
      (hq : qN = 1) :
      x ∈ Q.asIdeal := by
    have hnQ : nQ ≠ 0 := by
      intro hzero
      simp [qN, hzero] at hq
    have hQmem :
        Q.asIdeal ∈ normalizedFactors I := by
      rw [← Multiset.count_ne_zero]
      simpa [nQ, factorization_eq_count] using hnQ
    have hQdvd :
        Q.asIdeal ∣ I :=
      dvd_of_mem_normalizedFactors hQmem
    exact
      (Ideal.dvd_span_singleton.mp
        (by simpa only [I] using hQdvd))
  have hdiv :
      A ^ rN * Qelt ^ qN ∣ x := by
    rcases Nat.mod_two_eq_zero_or_one nP with hr | hr
    · have hrN : rN = 0 := by
        exact hr
      rcases Nat.mod_two_eq_zero_or_one nQ with hq | hq
      · have hqN : qN = 0 := by
          exact hq
        simp [hrN, hqN]
      · have hqN : qN = 1 := by
          exact hq
        have hxQ : x ∈ Q.asIdeal :=
          hxQ_of_qN_eq_one hqN
        have hQdiv : Qelt ∣ x := by
          rw [← Ideal.mem_span_singleton,
            ← hQgen]
          exact hxQ
        simpa [hrN, hqN] using hQdiv
    · have hrN : rN = 1 := by
        exact hr
      rcases Nat.mod_two_eq_zero_or_one nQ with hq | hq
      · have hqN : qN = 0 := by
          exact hq
        have hxP : x ∈ P.asIdeal :=
          hxP_of_rN_eq_one hrN
        have hAdiv : A ∣ x := by
          rw [← Ideal.mem_span_singleton,
            ← hPgen]
          exact hxP
        simpa [hrN, hqN] using hAdiv
      · have hqN : qN = 1 := by
          exact hq
        have hxP : x ∈ P.asIdeal :=
          hxP_of_rN_eq_one hrN
        have hxQ : x ∈ Q.asIdeal :=
          hxQ_of_qN_eq_one hqN
        have hPQideal :
            P.asIdeal ≠ Q.asIdeal := by
          intro h
          apply hPQ
          exact HeightOneSpectrum.ext h
        have hcoprime :
            P.asIdeal ⊔ Q.asIdeal = ⊤ :=
          (P.isPrime.isMaximal P.ne_bot).coprime_of_ne
            (Q.isPrime.isMaximal Q.ne_bot) hPQideal
        have hxMul :
            x ∈ P.asIdeal * Q.asIdeal := by
          rw [Ideal.mul_eq_inf_of_coprime hcoprime]
          exact ⟨hxP, hxQ⟩
        have hAQdiv : A * Qelt ∣ x := by
          rw [← Ideal.mem_span_singleton,
            ← Ideal.span_singleton_mul_span_singleton,
            ← hPgen, ← hQgen]
          exact hxMul
        simpa [hrN, hqN] using hAQdiv
  have hcorrect0 :
      A ^ rN * Qelt ^ qN ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ hA0)
      (pow_ne_zero _ hQ0)
  have hparity :
      ∀ R : HeightOneSpectrum O,
        Even
          (principalCount (L := L) R x -
            principalCount (L := L) R
              (A ^ rN * Qelt ^ qN)) := by
    intro R
    have hcountCorrection :
        principalCount (L := L) R
            (A ^ rN * Qelt ^ qN) =
          (rN : ℤ) *
              principalCount (L := L) R A +
            (qN : ℤ) *
              principalCount (L := L) R Qelt := by
      rw [principalCount_mul
          (pow_ne_zero _ hA0) (pow_ne_zero _ hQ0),
        principalCount_pow, principalCount_pow]
    by_cases hRP : R = P
    · subst R
      have hQP : P ≠ Q := hPQ
      rw [hcountCorrection,
        principalCount_generator_self P hPgen hA0,
        principalCount_generator_of_ne
          Q P hQgen hQ0 hQP]
      rw [principalCount_eq_factorization_span
        x hx P]
      change Even ((nP : ℤ) - ((rN : ℤ) * 1 + (qN : ℤ) * 0))
      refine ⟨(nP / 2 : ℕ), ?_⟩
      have hdivmod := Nat.mod_add_div nP 2
      dsimp only [rN]
      omega
    · by_cases hRQ : R = Q
      · subst R
        have hPQ' : Q ≠ P := Ne.symm hPQ
        rw [hcountCorrection,
          principalCount_generator_of_ne
            P Q hPgen hA0 hPQ',
          principalCount_generator_self Q hQgen hQ0]
        rw [principalCount_eq_factorization_span
          x hx Q]
        change Even ((nQ : ℤ) - ((rN : ℤ) * 0 + (qN : ℤ) * 1))
        refine ⟨(nQ / 2 : ℕ), ?_⟩
        have hdivmod := Nat.mod_add_div nQ 2
        dsimp only [qN]
        omega
      · rw [hcountCorrection,
          principalCount_generator_of_ne
            P R hPgen hA0 hRP,
          principalCount_generator_of_ne
            Q R hQgen hQ0 hRQ]
        simpa using hAway R hRP hRQ
  obtain ⟨ε, y, hxy⟩ :=
    exists_unit_mul_correction_mul_sq
      (L := L)
      (A ^ rN * Qelt ^ qN) x
      hcorrect0 hx hdiv hparity
  let r : ZMod 2 := rN
  let q : ZMod 2 := qN
  have hrval : r.val = rN := by
    exact ZMod.val_cast_of_lt hrN_lt
  have hqval : q.val = qN := by
    exact ZMod.val_cast_of_lt hqN_lt
  refine ⟨r, q, ε, y, ?_⟩
  simpa only [hrval, hqval, mul_assoc] using hxy


theorem principalCount_unit
    (ε : Oˣ) (R : HeightOneSpectrum O) :
    principalCount (L := L) R (ε : O) = 0 := by
  rw [principalCount_eq_factorization_span
    (ε : O) ε.ne_zero R]
  rw [Ideal.span_singleton_eq_top.mpr
    (Units.isUnit ε)]
  rw [← Ideal.one_eq_top, factorization_one]
  norm_num

/-- If the two exceptional counts have the same parity, their two carrier
bits collapse to the single product carrier. -/
theorem exists_unit_common_carrier_mul_sq_of_even_away
    [IsPrincipalIdealRing O]
    (P Q : HeightOneSpectrum O)
    (hPQ : P ≠ Q)
    (A Qelt x : O)
    (hPgen :
      P.asIdeal = Ideal.span ({A} : Set O))
    (hQgen :
      Q.asIdeal = Ideal.span ({Qelt} : Set O))
    (hx : x ≠ 0)
    (hAway :
      ∀ R : HeightOneSpectrum O,
        R ≠ P → R ≠ Q →
          Even (principalCount (L := L) R x))
    (hpair :
      Even
        (principalCount (L := L) P x -
          principalCount (L := L) Q x)) :
    ∃ d : ZMod 2, ∃ ε : Oˣ, ∃ y : O,
      x =
        (ε : O) * (A * Qelt) ^ d.val *
          y ^ 2 := by
  obtain ⟨r, q, ε, y, hxy⟩ :=
    exists_unit_two_carriers_mul_sq_of_even_away
      (L := L) P Q hPQ A Qelt x
      hPgen hQgen hx hAway
  have hA0 : A ≠ 0 := by
    intro hzero
    apply P.ne_bot
    rw [hPgen, hzero]
    simp
  have hQ0 : Qelt ≠ 0 := by
    intro hzero
    apply Q.ne_bot
    rw [hQgen, hzero]
    simp
  have hy0 : y ≠ 0 := by
    intro hzero
    apply hx
    simpa [hzero] using hxy
  have hε0 : (ε : O) ≠ 0 := ε.ne_zero
  have hAr0 : A ^ r.val ≠ 0 :=
    pow_ne_zero _ hA0
  have hQq0 : Qelt ^ q.val ≠ 0 :=
    pow_ne_zero _ hQ0
  have hy20 : y ^ 2 ≠ 0 :=
    pow_ne_zero _ hy0
  have hcountP :
      principalCount (L := L) P x =
        (r.val : ℤ) +
          2 * principalCount (L := L) P y := by
    calc
      principalCount (L := L) P x =
          principalCount (L := L) P
            ((ε : O) * A ^ r.val *
              Qelt ^ q.val * y ^ 2) :=
        congrArg (principalCount (L := L) P) hxy
      _ =
          principalCount (L := L) P
                ((ε : O) * A ^ r.val *
                  Qelt ^ q.val) +
            principalCount (L := L) P (y ^ 2) := by
        rw [principalCount_mul
          (mul_ne_zero
            (mul_ne_zero hε0 hAr0) hQq0)
          hy20]
      _ =
          (principalCount (L := L) P
                ((ε : O) * A ^ r.val) +
              principalCount (L := L) P
                (Qelt ^ q.val)) +
            principalCount (L := L) P (y ^ 2) := by
        rw [principalCount_mul
          (mul_ne_zero hε0 hAr0) hQq0]
      _ =
          ((principalCount (L := L) P (ε : O) +
                principalCount (L := L) P
                  (A ^ r.val)) +
              principalCount (L := L) P
                (Qelt ^ q.val)) +
            principalCount (L := L) P (y ^ 2) := by
        rw [principalCount_mul hε0 hAr0]
      _ = (r.val : ℤ) +
            2 * principalCount (L := L) P y := by
        rw [principalCount_unit,
          principalCount_pow,
          principalCount_generator_self
            P hPgen hA0,
          principalCount_pow,
          principalCount_generator_of_ne
            Q P hQgen hQ0 hPQ,
          principalCount_pow]
        ring
  have hcountQ :
      principalCount (L := L) Q x =
        (q.val : ℤ) +
          2 * principalCount (L := L) Q y := by
    calc
      principalCount (L := L) Q x =
          principalCount (L := L) Q
            ((ε : O) * A ^ r.val *
              Qelt ^ q.val * y ^ 2) :=
        congrArg (principalCount (L := L) Q) hxy
      _ =
          principalCount (L := L) Q
                ((ε : O) * A ^ r.val *
                  Qelt ^ q.val) +
            principalCount (L := L) Q (y ^ 2) := by
        rw [principalCount_mul
          (mul_ne_zero
            (mul_ne_zero hε0 hAr0) hQq0)
          hy20]
      _ =
          (principalCount (L := L) Q
                ((ε : O) * A ^ r.val) +
              principalCount (L := L) Q
                (Qelt ^ q.val)) +
            principalCount (L := L) Q (y ^ 2) := by
        rw [principalCount_mul
          (mul_ne_zero hε0 hAr0) hQq0]
      _ =
          ((principalCount (L := L) Q (ε : O) +
                principalCount (L := L) Q
                  (A ^ r.val)) +
              principalCount (L := L) Q
                (Qelt ^ q.val)) +
            principalCount (L := L) Q (y ^ 2) := by
        rw [principalCount_mul hε0 hAr0]
      _ = (q.val : ℤ) +
            2 * principalCount (L := L) Q y := by
        rw [principalCount_unit,
          principalCount_pow,
          principalCount_generator_of_ne
            P Q hPgen hA0 (Ne.symm hPQ),
          principalCount_pow,
          principalCount_generator_self
            Q hQgen hQ0,
          principalCount_pow]
        ring
  obtain ⟨k, hk⟩ := hpair
  rw [hcountP, hcountQ] at hk
  have hrlt : r.val < 2 := ZMod.val_lt r
  have hqlt : q.val < 2 := ZMod.val_lt q
  have hrq : r.val = q.val := by
    omega
  refine ⟨r, ε, y, ?_⟩
  rw [← hrq] at hxy
  simpa only [mul_pow, mul_assoc] using hxy


end MazurProof.ExceptionalPrincipalIdeal


