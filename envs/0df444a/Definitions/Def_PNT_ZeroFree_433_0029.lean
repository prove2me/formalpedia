-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0029
-- name    : PNT_ZeroFree_433_0029
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-10T13:45:53.99983+00:00
-- url     : https://prove2.me/theorems/128e3668-a73d-45df-bcf8-5d0fe2d8657d
-- title:
--   Zero-free region foundations: Hecke.PrimeExtraction [0029]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.Hecke.PrimeExtraction
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Hecke/PrimeExtraction.lean#L38-L585

import Definitions.Def_PNT_ZeroFree_433_0028

/- Supporting source modules for the zero-free-region proof.
Ported and checked against Lean 4.33.1 / Mathlib 0df444a.
Original source attribution:
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Hecke/PrimeExtraction.lean#L38-L585
-/

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

-- Source module: OAI.NumberTheory.DirichletL.Hecke.PrimeExtraction
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

namespace ShortDraftHeckeBridge

theorem dirichletTarget_of_normFiber_prefix_power
    (hprefix : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
      (ρ : ℂ), (23 / 24 : ℝ) < ρ.re → ρ.re < 1 →
        ∃ σ C : ℝ, 0 < σ ∧ σ < ρ.re ∧ σ ≤ 1 ∧ 0 ≤ C ∧
          ∀ n : ℕ,
            ‖prefixCoeff (normFiberCoeff (baseChangeWeight χ)) n‖ ≤
              C * (((n : ℝ) + 1) ^ σ)) :
    ShortDraft.DirichletTarget := by
  apply dirichletTarget_of_normFiber_exp_bound
  intro q _ χ ρ h23 hρ
  obtain ⟨σ, C, hσpos, hσρ, hσone, hC, hsum⟩ :=
    hprefix q χ ρ h23 hρ
  refine ⟨σ, hσpos, hσρ, ?_⟩
  apply normFiberExpSum_isBigO_of_prefix_power χ (baseChangeChar χ)
    (baseChangeWeight χ)
    (normFiberCoeff_baseChange_eq_pairInverseCoeff χ)
    (normFiberCoeff_baseChangeWeight_zero χ)
    σ C hσpos.le hσone hC hsum

end ShortDraftHeckeBridge
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid

namespace FiniteSFactor

abbrev O := NumberField.RingOfIntegers (CyclotomicField 3 ℚ)

theorem extract_prime_of_squarefree {I P : Ideal O}
    (hI : I ≠ ⊥) (hP : Prime P) (hsq : Squarefree I) (hdvd : P ∣ I) :
    ∃ J : Ideal O, IsRelPrime P J ∧ I = P * J := by
  let : P.IsMaximal := (Ideal.isPrime_of_prime hP).isMaximal hP.ne_zero
  obtain ⟨J, hcop, hfactor⟩ := Ideal.eq_prime_pow_mul_coprime hI P
  have hmem : P ∈ normalizedFactors I := by
    rw [Ideal.mem_normalizedFactors_iff hI]
    exact ⟨Ideal.isPrime_of_prime hP, (Ideal.dvd_iff_le).mp hdvd⟩
  have hpos : 0 < (normalizedFactors I).count P := Multiset.count_pos.mpr hmem
  have hnodup : (normalizedFactors I).Nodup :=
    (UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors hI).mp hsq
  have hle : (normalizedFactors I).count P ≤ 1 :=
    (Multiset.nodup_iff_count_le_one.mp hnodup) P
  have he : (normalizedFactors I).count P = 1 := by omega
  refine ⟨J, ?_, ?_⟩
  · exact IsCoprime.isRelPrime ((Ideal.isCoprime_iff_gcd).mpr (by simpa using hcop))
  · simpa [he] using hfactor

noncomputable def outsideWeight (S : Finset (Ideal O))
    (w : Ideal O → ℂ) (I : Ideal O) : ℂ := by
  classical
  exact if ∀ P ∈ S, ¬ P ∣ I then w I else 0

theorem outsideWeight_mul (S : Finset (Ideal O))
    (hprime : ∀ P ∈ S, Prime P) (w : Ideal O → ℂ)
    (I J : Ideal O) (hweight : w (I * J) = w I * w J) :
    outsideWeight S w (I * J) =
      outsideWeight S w I * outsideWeight S w J := by
  classical
  let good (K : Ideal O) : Prop := ∀ P ∈ S, ¬ P ∣ K
  have hleft : good (I * J) → good I := by
    intro h P hP hd
    exact h P hP (dvd_mul_of_dvd_left hd J)
  have hright : good (I * J) → good J := by
    intro h P hP hd
    exact h P hP (dvd_mul_of_dvd_right hd I)
  have hboth : good I → good J → good (I * J) := by
    intro hI hJ P hP hd
    rcases (hprime P hP).dvd_mul.mp hd with hdI | hdJ
    · exact hI P hP hdI
    · exact hJ P hP hdJ
  change (if good (I * J) then w (I * J) else 0) =
    (if good I then w I else 0) * (if good J then w J else 0)
  by_cases hI : good I
  · by_cases hJ : good J
    · have hIJ := hboth hI hJ
      simp [hI, hJ, hIJ, hweight]
    · have hIJ : ¬good (I * J) := fun h => hJ (hright h)
      simp [hI, hJ, hIJ]
  · have hIJ : ¬good (I * J) := fun h => hI (hleft h)
    simp [hI, hIJ]

noncomputable def fiber (n : ℕ) : Finset (Ideal O) :=
  (Ideal.finite_setOfPred_absNorm_eq (S := O) n).toFinset

theorem mem_fiber {n : ℕ} {I : Ideal O} : I ∈ fiber n ↔ Ideal.absNorm I = n := by
  simp [fiber]

noncomputable def badFiber (P : Ideal O) (m : ℕ) : Finset (Ideal O) := by
  classical
  exact (fiber (Ideal.absNorm P * m)).filter (fun I => Squarefree I ∧ P ∣ I)

noncomputable def goodFiber (P : Ideal O) (m : ℕ) : Finset (Ideal O) := by
  classical
  exact (fiber m).filter (fun J => Squarefree J ∧ ¬ P ∣ J)

theorem mem_badFiber {P : Ideal O} {m : ℕ} {I : Ideal O} :
    I ∈ badFiber P m ↔ Ideal.absNorm I = Ideal.absNorm P * m ∧ Squarefree I ∧ P ∣ I := by
  classical
  simp [badFiber, mem_fiber]

theorem mem_goodFiber {P : Ideal O} {m : ℕ} {J : Ideal O} :
    J ∈ goodFiber P m ↔ Ideal.absNorm J = m ∧ Squarefree J ∧ ¬P ∣ J := by
  classical
  simp [goodFiber, mem_fiber]

private noncomputable def pick (P : Ideal O) (hP : Prime P) (m : ℕ)
    (I : Ideal O) (hI : I ∈ badFiber P m) : Ideal O :=
  Classical.choose (extract_prime_of_squarefree
    ((mem_badFiber.mp hI).2.1.ne_zero) hP
    (mem_badFiber.mp hI).2.1 (mem_badFiber.mp hI).2.2)

private theorem pick_spec (P : Ideal O) (hP : Prime P) (m : ℕ)
    (I : Ideal O) (hI : I ∈ badFiber P m) :
    IsRelPrime P (pick P hP m I hI) ∧ I = P * pick P hP m I hI := by
  unfold pick
  exact Classical.choose_spec (extract_prime_of_squarefree
    ((mem_badFiber.mp hI).2.1.ne_zero) hP
    (mem_badFiber.mp hI).2.1 (mem_badFiber.mp hI).2.2)

theorem squarefree_prime_fiber_sum (P : Ideal O) (hP : Prime P)
    (m : ℕ) (w : Ideal O → ℂ) :
    (∑ I ∈ badFiber P m, w I) =
      ∑ J ∈ goodFiber P m, w (P * J) := by
  classical
  have hPnorm : Ideal.absNorm P ≠ 0 :=
    (Ideal.absNorm_eq_zero_iff).not.mpr hP.ne_zero
  refine Finset.sum_bij' (pick P hP m) (fun J _ => P * J) ?_ ?_ ?_ ?_ ?_
  · intro I hI
    have hinfo := pick_spec P hP m I hI
    have hJnorm : Ideal.absNorm (pick P hP m I hI) = m := by
      have hInorm := (mem_badFiber.mp hI).1
      rw [hinfo.2, map_mul] at hInorm
      exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hPnorm) hInorm
    have hJsq : Squarefree (pick P hP m I hI) := by
      have hsqI := (mem_badFiber.mp hI).2.1
      rw [hinfo.2] at hsqI
      exact hsqI.of_mul_right
    have hJnot : ¬P ∣ pick P hP m I hI :=
      hP.irreducible.isRelPrime_iff_not_dvd.mp hinfo.1
    exact mem_goodFiber.mpr ⟨hJnorm, hJsq, hJnot⟩
  · intro J hJ
    have hJnorm := (mem_goodFiber.mp hJ).1
    have hJsq := (mem_goodFiber.mp hJ).2.1
    have hJnot := (mem_goodFiber.mp hJ).2.2
    have hsq : Squarefree (P * J) :=
      squarefree_mul_iff.mpr ⟨hP.irreducible.isRelPrime_iff_not_dvd.mpr hJnot,
        hP.irreducible.squarefree, hJsq⟩
    exact mem_badFiber.mpr ⟨by rw [map_mul, hJnorm], hsq, dvd_mul_right P J⟩
  · intro I hI
    exact (pick_spec P hP m I hI).2.symm
  · intro J hJ
    have hPJ : P * J ∈ badFiber P m := by
      have hJnorm := (mem_goodFiber.mp hJ).1
      have hJsq := (mem_goodFiber.mp hJ).2.1
      have hJnot := (mem_goodFiber.mp hJ).2.2
      exact mem_badFiber.mpr ⟨by rw [map_mul, hJnorm],
        squarefree_mul_iff.mpr ⟨hP.irreducible.isRelPrime_iff_not_dvd.mpr hJnot,
          hP.irreducible.squarefree, hJsq⟩, dvd_mul_right P J⟩
    have hchosen := (pick_spec P hP m (P * J) hPJ).2
    exact (mul_left_cancel₀ hP.ne_zero hchosen).symm
  · intro I hI
    exact congrArg w (pick_spec P hP m I hI).2

open scoped Classical

noncomputable def exceptPrimeCoeff (P : Ideal O) (w : Ideal O → ℂ) (n : ℕ) : ℂ := by
  classical
  exact ∑ I ∈ fiber n, if ¬P ∣ I then w I else 0

private theorem sum_filter_squarefree (pred : Ideal O → Prop) (w : Ideal O → ℂ)
    (hzero : ∀ I, ¬Squarefree I → w I = 0) (n : ℕ) :
    (∑ I ∈ fiber n, if pred I then w I else 0) =
      ∑ I ∈ (fiber n).filter (fun I => Squarefree I ∧ pred I), w I := by
  classical
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro I hI
  by_cases hsq : Squarefree I
  · simp [hsq]
  · simp [hsq, hzero I hsq]

theorem restore_one_prime (P : Ideal O) (hP : Prime P)
    (w : Ideal O → ℂ)
    (hzero : ∀ I, ¬Squarefree I → w I = 0)
    (hmul : ∀ J, ¬P ∣ J → w (P * J) = w P * w J)
    (m : ℕ) :
    (∑ I ∈ fiber (Ideal.absNorm P * m), w I) =
      exceptPrimeCoeff P w (Ideal.absNorm P * m) +
        w P * exceptPrimeCoeff P w m := by
  classical
  let n := Ideal.absNorm P * m
  have hsplit : (∑ I ∈ fiber n, w I) =
      (∑ I ∈ fiber n, if ¬P ∣ I then w I else 0) +
      (∑ I ∈ fiber n, if P ∣ I then w I else 0) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro I hI
    by_cases h : P ∣ I <;> simp [h]
  have hbad : (∑ I ∈ fiber n, if P ∣ I then w I else 0) =
      ∑ I ∈ badFiber P m, w I := by
    rw [badFiber]
    exact sum_filter_squarefree (fun I => P ∣ I) w hzero n
  have hgood : (∑ J ∈ goodFiber P m, w J) = exceptPrimeCoeff P w m := by
    rw [goodFiber, exceptPrimeCoeff, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro J hJ
    by_cases hsq : Squarefree J
    · simp [hsq]
    · simp [hsq, hzero J hsq]
  calc
    (∑ I ∈ fiber n, w I) =
        (∑ I ∈ fiber n, if ¬P ∣ I then w I else 0) +
          (∑ I ∈ fiber n, if P ∣ I then w I else 0) := hsplit
    _ = exceptPrimeCoeff P w n + ∑ I ∈ badFiber P m, w I := by
      rw [hbad]
      rfl
    _ = exceptPrimeCoeff P w n + ∑ J ∈ goodFiber P m, w (P * J) := by
      rw [squarefree_prime_fiber_sum P hP m w]
    _ = exceptPrimeCoeff P w n + w P * ∑ J ∈ goodFiber P m, w J := by
      rw [Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro J hJ
      exact hmul J (mem_goodFiber.mp hJ).2.2
    _ = exceptPrimeCoeff P w n + w P * exceptPrimeCoeff P w m := by rw [hgood]

theorem restore_one_prime_all (P : Ideal O) (hP : Prime P)
    (w : Ideal O → ℂ)
    (hzero : ∀ I, ¬Squarefree I → w I = 0)
    (hmul : ∀ J, ¬P ∣ J → w (P * J) = w P * w J)
    (n : ℕ) :
    (∑ I ∈ fiber n, w I) = exceptPrimeCoeff P w n +
      (if Ideal.absNorm P ∣ n then
        w P * exceptPrimeCoeff P w (n / Ideal.absNorm P) else 0) := by
  classical
  by_cases hdiv : Ideal.absNorm P ∣ n
  · have hn : Ideal.absNorm P * (n / Ideal.absNorm P) = n :=
      Nat.mul_div_cancel' hdiv
    rw [← hn]
    have hPnorm : Ideal.absNorm P ≠ 0 :=
      (Ideal.absNorm_eq_zero_iff).not.mpr hP.ne_zero
    simpa [Nat.mul_div_cancel_left, hPnorm] using
      restore_one_prime P hP w hzero hmul (n / Ideal.absNorm P)
  · have hnone : ∀ I ∈ fiber n, ¬P ∣ I := by
      intro I hI hd
      apply hdiv
      have hnorm : Ideal.absNorm I = n := mem_fiber.mp hI
      rw [← hnorm]
      exact Ideal.absNorm_dvd_absNorm_of_le (Ideal.dvd_iff_le.mp hd)
    simp only [if_neg hdiv, add_zero]
    rw [exceptPrimeCoeff]
    apply Finset.sum_congr rfl
    intro I hI
    simp [hnone I hI]

open scoped Classical

noncomputable def outsideCoeff (S : Finset (Ideal O))
    (w : Ideal O → ℂ) (n : ℕ) : ℂ :=
  ∑ I ∈ fiber n, outsideWeight S w I

private theorem outsideWeight_zero_of_not_squarefree (S : Finset (Ideal O))
    (w : Ideal O → ℂ) (hzero : ∀ I, ¬Squarefree I → w I = 0)
    (I : Ideal O) (hsq : ¬Squarefree I) : outsideWeight S w I = 0 := by
  by_cases hg : ∀ P ∈ S, ¬P ∣ I
  · simp [outsideWeight,  hzero I hsq]
  · simp [outsideWeight, hg]

private theorem outsideWeight_prime_of_not_mem (S : Finset (Ideal O))
    (hprime : ∀ Q ∈ S, Prime Q) (P : Ideal O) (hP : Prime P)
    (hPnot : P ∉ S) (w : Ideal O → ℂ) :
    outsideWeight S w P = w P := by
  have hgood : ∀ Q ∈ S, ¬Q ∣ P := by
    intro Q hQ hd
    have heq : Q = P :=
      associated_iff_eq.mp ((hprime Q hQ).associated_of_dvd hP hd)
    exact hPnot (heq ▸ hQ)
  change (if ∀ Q ∈ S, ¬Q ∣ P then w P else 0) = w P
  exact if_pos hgood

private theorem exceptPrimeCoeff_outsideWeight (S : Finset (Ideal O))
    (P : Ideal O) (w : Ideal O → ℂ) (n : ℕ) :
    exceptPrimeCoeff P (outsideWeight S w) n =
      outsideCoeff (insert P S) w n := by
  classical
  unfold exceptPrimeCoeff outsideCoeff
  apply Finset.sum_congr rfl
  intro I hI
  by_cases hd : P ∣ I
  · simp [outsideWeight, hd]
  · by_cases hs : ∀ Q ∈ S, ¬Q ∣ I
    · simp [outsideWeight, hd]
    · simp [outsideWeight, hd, hs]

theorem restore_insert_prime (S : Finset (Ideal O))
    (hprime : ∀ Q ∈ S, Prime Q) (P : Ideal O) (hP : Prime P)
    (hPnot : P ∉ S) (w : Ideal O → ℂ)
    (hzero : ∀ I, ¬Squarefree I → w I = 0)
    (hmul : ∀ I J, IsRelPrime I J → w (I * J) = w I * w J)
    (n : ℕ) :
    outsideCoeff S w n = outsideCoeff (insert P S) w n +
      (if Ideal.absNorm P ∣ n then
        w P * outsideCoeff (insert P S) w (n / Ideal.absNorm P) else 0) := by
  have hzeroS : ∀ I, ¬Squarefree I → outsideWeight S w I = 0 :=
    outsideWeight_zero_of_not_squarefree S w hzero
  have hmulS : ∀ J, ¬P ∣ J →
      outsideWeight S w (P * J) = outsideWeight S w P * outsideWeight S w J := by
    intro J hnot
    apply outsideWeight_mul S hprime w P J
    exact hmul P J (hP.irreducible.isRelPrime_iff_not_dvd.mpr hnot)
  have hrest := restore_one_prime_all P hP (outsideWeight S w) hzeroS hmulS n
  unfold outsideCoeff at hrest ⊢
  rw [exceptPrimeCoeff_outsideWeight S P w n,
    exceptPrimeCoeff_outsideWeight S P w (n / Ideal.absNorm P),
    outsideWeight_prime_of_not_mem S hprime P hP hPnot w] at hrest
  exact hrest

end FiniteSFactor
namespace ShortDraftHeckeBridge

theorem baseChangeWeight_zero_of_not_squarefree {q : ℕ}
    (χ : DirichletCharacter ℂ q) (I : Ideal O) (hsq : ¬Squarefree I) :
    baseChangeWeight χ I = 0 := by
  rw [baseChangeWeight, UniqueFactorizationMonoid.moebius_of_not_squarefree hsq]
  simp

theorem baseChangeWeight_mul_of_isRelPrime {q : ℕ}
    (χ : DirichletCharacter ℂ q) (I J : Ideal O) (h : IsRelPrime I J) :
    baseChangeWeight χ (I * J) =
      baseChangeWeight χ I * baseChangeWeight χ J := by
  simp only [baseChangeWeight, map_mul, h.moebius_mul, Int.cast_mul, Nat.cast_mul]
  ring

theorem baseChange_restore_insert_prime {q : ℕ}
    (χ : DirichletCharacter ℂ q)
    (S : Finset (Ideal O)) (hS : ∀ Q ∈ S, Prime Q)
    (P : Ideal O) (hP : Prime P) (hPnot : P ∉ S) (n : ℕ) :
    FiniteSFactor.outsideCoeff S (baseChangeWeight χ) n =
      FiniteSFactor.outsideCoeff (insert P S) (baseChangeWeight χ) n +
      (if Ideal.absNorm P ∣ n then
        baseChangeWeight χ P *
          FiniteSFactor.outsideCoeff (insert P S) (baseChangeWeight χ)
            (n / Ideal.absNorm P) else 0) := by
  exact FiniteSFactor.restore_insert_prime S hS P hP hPnot
    (baseChangeWeight χ) (baseChangeWeight_zero_of_not_squarefree χ)
    (baseChangeWeight_mul_of_isRelPrime χ) n

end ShortDraftHeckeBridge

namespace DyadicTransfer

noncomputable def annularCutoff (φ : ℝ → ℂ) (y : ℝ) : ℂ :=
  φ y - φ (2 * y)

theorem annularCutoff_eq_zero_of_le_half (φ : ℝ → ℂ)
    (hsmall : ∀ y : ℝ, y ≤ 1 → φ y = 1)
    {y : ℝ} (hy : y ≤ 1 / 2) : annularCutoff φ y = 0 := by
  have hy1 : y ≤ 1 := by linarith
  have h2y : 2 * y ≤ 1 := by linarith
  simp [annularCutoff, hsmall y hy1, hsmall (2 * y) h2y]

theorem annularCutoff_eq_zero_of_two_le (φ : ℝ → ℂ)
    (hlarge : ∀ y : ℝ, 2 ≤ y → φ y = 0)
    {y : ℝ} (hy : 2 ≤ y) : annularCutoff φ y = 0 := by
  have h2y : 2 ≤ 2 * y := by linarith
  simp [annularCutoff, hlarge y hy, hlarge (2 * y) h2y]

theorem partial_partition (φ : ℝ → ℂ) (x : ℝ) (K : ℕ) :
    (∑ k ∈ Finset.range (K + 1),
      annularCutoff φ (x / (2 : ℝ) ^ k)) =
      φ (x / (2 : ℝ) ^ K) - φ (2 * x) := by
  induction K with
  | zero =>
      simp [annularCutoff]
  | succ K ih =>
      rw [Finset.sum_range_succ, ih]
      unfold annularCutoff
      have hpow : (2 : ℝ) ^ (K + 1) ≠ 0 := by positivity
      have hshift : 2 * (x / (2 : ℝ) ^ (K + 1)) = x / (2 : ℝ) ^ K := by
        rw [pow_succ]
        field_simp
      rw [hshift]
      ring

theorem partition_nat (φ : ℝ → ℂ)
    (hsmall : ∀ y : ℝ, y ≤ 1 → φ y = 1)
    (hlarge : ∀ y : ℝ, 2 ≤ y → φ y = 0)
    (n K : ℕ) (hn : 1 ≤ n) (hK : (n : ℝ) ≤ (2 : ℝ) ^ K) :
    (∑ k ∈ Finset.range (K + 1),
      annularCutoff φ ((n : ℝ) / (2 : ℝ) ^ k)) = 1 := by
  rw [partial_partition]
  have hpow : 0 < (2 : ℝ) ^ K := by positivity
  have hnsmall : (n : ℝ) / (2 : ℝ) ^ K ≤ 1 :=
    (div_le_iff₀ hpow).mpr (by simpa using hK)
  rw [hsmall _ hnsmall, hlarge]
  · ring
  · exact_mod_cast (show (2 : ℕ) ≤ 2 * n by omega)

noncomputable def expAnnularTest (φ : ℝ → ℂ) (D : ℝ) (k : ℕ) (y : ℝ) : ℂ :=
  annularCutoff φ y * Real.exp (-((2 : ℝ) ^ k / D) * y)

theorem expAnnularTest_eq_zero_of_le_half (φ : ℝ → ℂ)
    (hsmall : ∀ y : ℝ, y ≤ 1 → φ y = 1)
    (D : ℝ) (k : ℕ) {y : ℝ} (hy : y ≤ 1 / 2) :
    expAnnularTest φ D k y = 0 := by
  simp [expAnnularTest, annularCutoff_eq_zero_of_le_half φ hsmall hy]

theorem expAnnularTest_eq_zero_of_two_le (φ : ℝ → ℂ)
    (hlarge : ∀ y : ℝ, 2 ≤ y → φ y = 0)
    (D : ℝ) (k : ℕ) {y : ℝ} (hy : 2 ≤ y) :
    expAnnularTest φ D k y = 0 := by
  simp [expAnnularTest, annularCutoff_eq_zero_of_two_le φ hlarge hy]

theorem expAnnularTest_norm_le (φ : ℝ → ℂ) (D : ℝ) (k : ℕ)
    (hD : 0 < D) (M : ℝ) (hM : ∀ y : ℝ, ‖annularCutoff φ y‖ ≤ M)
    {y : ℝ} (hy : 1 / 2 ≤ y) :
    ‖expAnnularTest φ D k y‖ ≤
      M * Real.exp (-((2 : ℝ) ^ k / D) / 2) := by
  let t : ℝ := (2 : ℝ) ^ k / D
  have ht : 0 ≤ t := div_nonneg (by positivity) hD.le
  have harg : -(t * y) ≤ -t / 2 := by
    nlinarith [mul_nonneg ht (sub_nonneg.mpr hy)]
  have hexp : Real.exp (-(t * y)) ≤ Real.exp (-t / 2) :=
    Real.exp_le_exp.mpr harg
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM y)
  calc
    ‖expAnnularTest φ D k y‖ = ‖annularCutoff φ y‖ * Real.exp (-(t * y)) := by
      rw [expAnnularTest, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _)]
      simp [t]
    _ ≤ M * Real.exp (-(t * y)) :=
      mul_le_mul_of_nonneg_right (hM y) (Real.exp_pos _).le
    _ ≤ M * Real.exp (-t / 2) := mul_le_mul_of_nonneg_left hexp hM0
    _ = M * Real.exp (-((2 : ℝ) ^ k / D) / 2) := rfl

theorem finite_exp_reassembly (a : ℕ → ℂ) (φ : ℝ → ℂ)
    (ha0 : a 0 = 0)
    (hsmall : ∀ y : ℝ, y ≤ 1 → φ y = 1)
    (hlarge : ∀ y : ℝ, 2 ≤ y → φ y = 0)
    (D : ℝ) (N K : ℕ)
    (hK : ∀ n ∈ Finset.range N, 1 ≤ n → (n : ℝ) ≤ (2 : ℝ) ^ K) :
    (∑ n ∈ Finset.range N, a n * Real.exp (-(n : ℝ) / D)) =
      ∑ k ∈ Finset.range (K + 1),
        ∑ n ∈ Finset.range N,
          a n * expAnnularTest φ D k ((n : ℝ) / (2 : ℝ) ^ k) := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hn0 : n = 0
  · subst n
    simp [ha0, expAnnularTest, annularCutoff]
  · have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
    have hpart := partition_nat φ hsmall hlarge n K hn1 (hK n hn hn1)
    simp_rw [expAnnularTest]
    have hexp (k : ℕ) :
        Real.exp (-((2 : ℝ) ^ k / D) * ((n : ℝ) / (2 : ℝ) ^ k)) =
          Real.exp (-(n : ℝ) / D) := by
      congr 1
      have hpow : (2 : ℝ) ^ k ≠ 0 := by positivity
      field_simp
    simp_rw [hexp]
    rw [← Finset.mul_sum]
    rw [← Finset.sum_mul, hpart]
    simp

theorem finite_dyadic_piece_bound
    (F : ℕ → ℂ) (C r : ℝ) (hC : 0 ≤ C) (hr : 1 < r)
    (b : ℕ → ℝ) (hb : Summable b) (hb0 : ∀ m, 0 ≤ b m)
    (N M : ℕ)
    (hlow : ∀ k ≤ N, ‖F k‖ ≤ C * r ^ k)
    (hhigh : ∀ m, ‖F (N + 1 + m)‖ ≤ C * r ^ N * b m) :
    ‖∑ k ∈ Finset.range (N + 1 + M), F k‖ ≤
      C * (r ^ (N + 1) / (r - 1) + r ^ N * ∑' m, b m) := by
  have hr0 : 0 ≤ r := by linarith
  have hrden : 0 < r - 1 := by linarith
  have hlowSum :
      ‖∑ k ∈ Finset.range (N + 1), F k‖ ≤
        C * (r ^ (N + 1) / (r - 1)) := by
    calc
      ‖∑ k ∈ Finset.range (N + 1), F k‖ ≤
          ∑ k ∈ Finset.range (N + 1), ‖F k‖ := norm_sum_le _ _
      _ ≤ ∑ k ∈ Finset.range (N + 1), C * r ^ k := by
        apply Finset.sum_le_sum
        intro k hk
        exact hlow k (Nat.le_of_lt_succ (Finset.mem_range.mp hk))
      _ = C * ((r ^ (N + 1) - 1) / (r - 1)) := by
        rw [← Finset.mul_sum, geom_sum_eq (ne_of_gt hr)]
      _ ≤ C * (r ^ (N + 1) / (r - 1)) := by
        apply mul_le_mul_of_nonneg_left _ hC
        exact div_le_div_of_nonneg_right (by linarith) hrden.le
  have hhighSum :
      ‖∑ m ∈ Finset.range M, F (N + 1 + m)‖ ≤
        C * r ^ N * ∑' m, b m := by
    calc
      ‖∑ m ∈ Finset.range M, F (N + 1 + m)‖ ≤
          ∑ m ∈ Finset.range M, ‖F (N + 1 + m)‖ := norm_sum_le _ _
      _ ≤ ∑ m ∈ Finset.range M, C * r ^ N * b m := by
        apply Finset.sum_le_sum
        intro m _
        exact hhigh m
      _ = C * r ^ N * ∑ m ∈ Finset.range M, b m := by
        rw [← Finset.mul_sum]
      _ ≤ C * r ^ N * ∑' m, b m := by
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg hC (pow_nonneg hr0 N))
        exact hb.sum_le_tsum _ (fun m _ => hb0 m)
  rw [Finset.sum_range_add]
  calc
    ‖(∑ k ∈ Finset.range (N + 1), F k) +
      ∑ m ∈ Finset.range M, F (N + 1 + m)‖ ≤
        ‖∑ k ∈ Finset.range (N + 1), F k‖ +
          ‖∑ m ∈ Finset.range M, F (N + 1 + m)‖ := norm_add_le _ _
    _ ≤ C * (r ^ (N + 1) / (r - 1)) + C * r ^ N * ∑' m, b m :=
      add_le_add hlowSum hhighSum
    _ = C * (r ^ (N + 1) / (r - 1) + r ^ N * ∑' m, b m) := by ring

end DyadicTransfer

open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid

namespace FiniteSFactor

theorem restore_two_primes (P Q : Ideal O) (hP : Prime P) (hQ : Prime Q)
    (hne : P ≠ Q) (w : Ideal O → ℂ)
    (hzero : ∀ I, ¬Squarefree I → w I = 0)
    (hmul : ∀ I J, IsRelPrime I J → w (I * J) = w I * w J)
    (n : ℕ) :
    outsideCoeff ∅ w n =
      (outsideCoeff (insert Q {P}) w n +
        (if Ideal.absNorm Q ∣ n then
          w Q * outsideCoeff (insert Q {P}) w (n / Ideal.absNorm Q) else 0)) +
      (if Ideal.absNorm P ∣ n then
        w P *
          (outsideCoeff (insert Q {P}) w (n / Ideal.absNorm P) +
            (if Ideal.absNorm Q ∣ n / Ideal.absNorm P then
              w Q * outsideCoeff (insert Q {P}) w
                ((n / Ideal.absNorm P) / Ideal.absNorm Q) else 0))
        else 0) := by
  classical
  have hPnot : P ∉ (∅ : Finset (Ideal O)) := by simp
  have hSprime : ∀ R ∈ ({P} : Finset (Ideal O)), Prime R := by
    intro R hR
    have heq : R = P := Finset.mem_singleton.mp hR
    exact heq ▸ hP
  have hQnot : Q ∉ ({P} : Finset (Ideal O)) := by simpa using hne.symm
  have hfirst := restore_insert_prime ∅ (by simp) P hP hPnot w hzero hmul n
  have hsecond := restore_insert_prime {P} hSprime Q hQ hQnot w hzero hmul n
  have hthird := restore_insert_prime {P} hSprime Q hQ hQnot w hzero hmul
    (n / Ideal.absNorm P)
  simp only [Finset.insert_empty] at hfirst
  rw [hsecond, hthird] at hfirst
  exact hfirst

end FiniteSFactor

end

end OAI

end


