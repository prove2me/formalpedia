-- Prove2me | solution 1 for APFPaper5.K3.exists_noncommuting_of_rangesOver
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-13T18:22:21.799129+00:00
-- url     : https://prove2.me/submissions/d654bcfc-0db0-4596-a498-2164adfddce7

/-
APF Foundation Ledger — theorem node DRAFT (session EthanBrooke-01WrrBvu, 2026-11-12; not gated, not reviewed)
name: APFPaper5_K3_continuity_consequences
title: What the continuity hypothesis gives: reversible turns, and a pair that does not commute
inputs_revision: 2026-10-04.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: as Def_APFPaper5_K3_Continuity; Thm_APFPaper1_pair_number.
consumes_inputs: none. CONDITIONAL on the named hypothesis (its parts are hypotheses of each theorem).
statement: (turn_two_sided_inverse_of_loseNothing) if turns lose nothing, every admissible turn has an
 admissible turn that undoes it on both sides. (turn_bijective_of_loseNothing) so every admissible turn is a
 bijection. (exists_value_not_zero_or_one) if the relation number ranges over an interval, some held state has
 a number that is neither 0 nor 1. (exists_noncommuting_of_rangesOver) so, for repeatable nonzero marks in a
 real algebra whose pair relation is p * q * p = rel • p, some held state has marks that do not commute.
not_claimed: that any interface satisfies the hypothesis; that marks take values in a real algebra or that the
 pair relation holds; that a pair which does not commute is realised at an interface; anything about cost.
-/
import Definitions.Def_APFPaper5_K3_Continuity
import Theorems.Thm_APFPaper1_RecordBook_pair_number_zero_or_one_of_commute
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.NormNum

set_option autoImplicit false
namespace APFPaper5.K3

universe u uA
variable {S : Type u}

theorem turn_two_sided_inverse_of_loseNothing (Adm : Set (S → S)) (h : TurnsLoseNothing Adm)
    (f : S → S) (hf : f ∈ Adm) :
    ∃ g ∈ Adm, (∀ s : S, g (f s) = s) ∧ (∀ s : S, f (g s) = s) := by
  obtain ⟨g, hg, hgf⟩ := h f hf
  obtain ⟨k, _, hkg⟩ := h g hg
  refine ⟨g, hg, hgf, fun s => ?_⟩
  calc f (g s) = k (g (f (g s))) := (hkg (f (g s))).symm
    _ = k (g s) := by rw [hgf (g s)]
    _ = s := hkg s

theorem turn_bijective_of_loseNothing (Adm : Set (S → S)) (h : TurnsLoseNothing Adm)
    (f : S → S) (hf : f ∈ Adm) : Function.Bijective f := by
  obtain ⟨g, _, hgf, hfg⟩ := turn_two_sided_inverse_of_loseNothing Adm h f hf
  exact ⟨Function.LeftInverse.injective hgf, Function.RightInverse.surjective hfg⟩

theorem exists_value_not_zero_or_one (rel : S → ℝ) (lo hi : ℝ)
    (h : RangesOverInterval rel lo hi) : ∃ s : S, rel s ≠ 0 ∧ rel s ≠ 1 := by
  obtain ⟨hlt, hall⟩ := h
  by_cases hA : lo = 0
  · by_cases hB : hi < 1
    · obtain ⟨s, hs⟩ := hall hi hlt.le le_rfl
      refine ⟨s, ?_⟩
      rw [hs]
      constructor <;> intro hc <;> linarith
    · obtain ⟨s, hs⟩ := hall (1 / 2) (by linarith) (by linarith)
      refine ⟨s, ?_⟩
      rw [hs]
      constructor <;> norm_num
  · by_cases hC : lo = 1
    · obtain ⟨s, hs⟩ := hall hi hlt.le le_rfl
      refine ⟨s, ?_⟩
      rw [hs]
      constructor <;> intro hc <;> linarith
    · obtain ⟨s, hs⟩ := hall lo le_rfl hlt.le
      refine ⟨s, ?_⟩
      rw [hs]
      exact ⟨hA, hC⟩

theorem exists_noncommuting_of_rangesOver {A : Type uA} [Ring A] [Algebra ℝ A]
    (p q : S → A) (rel : S → ℝ) (lo hi : ℝ)
    (hp : ∀ s : S, p s * p s = p s) (hq : ∀ s : S, q s * q s = q s) (hp0 : ∀ s : S, p s ≠ 0)
    (hrel : ∀ s : S, p s * q s * p s = rel s • p s)
    (h : RangesOverInterval rel lo hi) : ∃ s : S, p s * q s ≠ q s * p s := by
  obtain ⟨s, h0, h1⟩ := exists_value_not_zero_or_one rel lo hi h
  refine ⟨s, fun hcomm => ?_⟩
  rcases APFPaper1.RecordBook.pair_number_zero_or_one_of_commute (p s) (q s) (rel s)
      (hp s) (hq s) hcomm (hrel s) (hp0 s) with hz | ho
  · exact h0 hz
  · exact h1 ho

end APFPaper5.K3


universe apfNative_u apfNative_uA
theorem solution :
∀ {S : Type apfNative_u} {A : Type apfNative_uA} [inst : Ring.{apfNative_uA} A]
  [inst_1 : @Algebra.{0, apfNative_uA} Real A Real.instCommSemiring (@Ring.toSemiring.{apfNative_uA} A inst)]
  (p q : S → A) (rel : S → Real) (lo hi : Real)
  (hp :
    ∀ (s : S),
      @Eq.{apfNative_uA + 1} A
        (@HMul.hMul.{apfNative_uA, apfNative_uA, apfNative_uA} A A A
          (@instHMul.{apfNative_uA} A
            (@Distrib.toMul.{apfNative_uA} A
              (@instDistribOfSemiring.{apfNative_uA} A (@Ring.toSemiring.{apfNative_uA} A inst))))
          (p s) (p s))
        (p s))
  (hq :
    ∀ (s : S),
      @Eq.{apfNative_uA + 1} A
        (@HMul.hMul.{apfNative_uA, apfNative_uA, apfNative_uA} A A A
          (@instHMul.{apfNative_uA} A
            (@Distrib.toMul.{apfNative_uA} A
              (@instDistribOfSemiring.{apfNative_uA} A (@Ring.toSemiring.{apfNative_uA} A inst))))
          (q s) (q s))
        (q s))
  (hp0 :
    ∀ (s : S),
      @Ne.{apfNative_uA + 1} A (p s)
        (@OfNat.ofNat.{apfNative_uA} A (nat_lit 0)
          (@Zero.toOfNat0.{apfNative_uA} A
            (@MulZeroClass.toZero.{apfNative_uA} A
              (@instMulZeroClassOfSemiring.{apfNative_uA} A (@Ring.toSemiring.{apfNative_uA} A inst))))))
  (hrel :
    ∀ (s : S),
      @Eq.{apfNative_uA + 1} A
        (@HMul.hMul.{apfNative_uA, apfNative_uA, apfNative_uA} A A A
          (@instHMul.{apfNative_uA} A
            (@Distrib.toMul.{apfNative_uA} A
              (@instDistribOfSemiring.{apfNative_uA} A (@Ring.toSemiring.{apfNative_uA} A inst))))
          (@HMul.hMul.{apfNative_uA, apfNative_uA, apfNative_uA} A A A
            (@instHMul.{apfNative_uA} A
              (@Distrib.toMul.{apfNative_uA} A
                (@instDistribOfSemiring.{apfNative_uA} A (@Ring.toSemiring.{apfNative_uA} A inst))))
            (p s) (q s))
          (p s))
        (@HSMul.hSMul.{0, apfNative_uA, apfNative_uA} Real A A
          (@instHSMul.{0, apfNative_uA} Real A
            (@Algebra.toSMul.{0, apfNative_uA} Real A Real.instCommSemiring (@Ring.toSemiring.{apfNative_uA} A inst)
              inst_1))
          (rel s) (p s)))
  (h : @APFPaper5.K3.RangesOverInterval.{apfNative_u} S rel lo hi),
  @Exists.{apfNative_u + 1} S fun (s : S) =>
    @Ne.{apfNative_uA + 1} A
      (@HMul.hMul.{apfNative_uA, apfNative_uA, apfNative_uA} A A A
        (@instHMul.{apfNative_uA} A
          (@Distrib.toMul.{apfNative_uA} A
            (@instDistribOfSemiring.{apfNative_uA} A (@Ring.toSemiring.{apfNative_uA} A inst))))
        (p s) (q s))
      (@HMul.hMul.{apfNative_uA, apfNative_uA, apfNative_uA} A A A
        (@instHMul.{apfNative_uA} A
          (@Distrib.toMul.{apfNative_uA} A
            (@instDistribOfSemiring.{apfNative_uA} A (@Ring.toSemiring.{apfNative_uA} A inst))))
        (q s) (p s)) := by
  exact @APFPaper5.K3.exists_noncommuting_of_rangesOver
