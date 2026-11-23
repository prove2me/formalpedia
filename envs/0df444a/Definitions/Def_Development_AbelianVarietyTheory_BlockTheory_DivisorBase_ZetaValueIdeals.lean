-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_ZetaValueIdeals
-- name    : Development_AbelianVarietyTheory_BlockTheory_DivisorBase_ZetaValueIdeals
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:41:51.834821+00:00
-- url     : https://prove2.me/theorems/a4a48e28-810e-45db-98d7-c593a91a38a6
-- title:
--   Zeta Value Ideals
-- statement:
--   Definitions and structural lemmas for Zeta Value Ideals, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/ZetaValueIdeals.lean

import Mathlib
import Definitions.Def_Formalism_PairingDivisors_StatementN
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Module
open scoped nonZeroDivisors
namespace GlobalTheory.IndefiniteRowSideFullHecke.ZetaValueIdeals
variable {F : Type} [Field F] [NumberField F]
abbrev IdealsIn (C : ClassGroup (𝓞 F)) : Type := {I : (Ideal (𝓞 F))⁰ // ClassGroup.mk0 I = C}
def IsClassZeta (C : ClassGroup (𝓞 F)) (Z : ℂ → ℂ) : Prop :=
  DifferentiableOn ℂ Z {1}ᶜ ∧ ∀ s : ℂ, 1 < s.re →
    HasSum (fun I : IdealsIn C => ((Ideal.absNorm (I.1 : Ideal (𝓞 F)) : ℕ) : ℂ) ^ (-s)) (Z s)
def IsZetaValues (k : ℕ) (z : ClassGroup (𝓞 F) → ℚ) : Prop :=
  ∀ C, ∃ Z : ℂ → ℂ, IsClassZeta C Z ∧ Z (1 - (k : ℂ)) = (z C : ℂ)
def denomExp (l : ℕ) (r : ℚ) : ℕ := (-padicValRat l r).toNat
def cE (z : ClassGroup (𝓞 F) → ℚ) (l : ℕ) : ℕ :=
  Finset.univ.sup fun C => denomExp l (z C / 2 ^ finrank ℚ F)
def mMin (l n : ℕ) : ℕ := sInf {m | ∃ a : ℕ, 2 ≤ a ∧ a.Coprime l ∧ m = padicValNat l (a ^ n - 1)}
def LocalBound (k : ℕ) (z : ClassGroup (𝓞 F) → ℚ) (l : ℕ) : Prop :=
  cE z l ≤ finrank ℚ F * padicValNat l 2 + mMin l (finrank ℚ F * k) ∧
  (l ≠ 2 → ¬ (l - 1) ∣ finrank ℚ F * k → mMin l (finrank ℚ F * k) = 0) ∧
  (l ≠ 2 → (l - 1) ∣ finrank ℚ F * k → mMin l (finrank ℚ F * k) = 1 + padicValNat l (finrank ℚ F * k)) ∧
  (l = 2 → mMin l (finrank ℚ F * k) = 2 + padicValNat 2 (finrank ℚ F * k))
def SumBound (k : ℕ) (z : ClassGroup (𝓞 F) → ℚ) : Prop :=
  (Function.support fun l : Nat.Primes => (cE z l : ℝ) * Real.log (l : ℕ)).Finite ∧
  ∑ᶠ l : Nat.Primes, (cE z l : ℝ) * Real.log (l : ℕ) ≤
    ((finrank ℚ F * k : ℕ) : ℝ) * Real.log (((finrank ℚ F * k : ℕ) : ℝ) + 1)
def DenomAt (F : Type) [Field F] [NumberField F] (k : ℕ) : Prop :=
  (∃ z : ClassGroup (𝓞 F) → ℚ, IsZetaValues k z) ∧
  ∀ z : ClassGroup (𝓞 F) → ℚ, IsZetaValues k z →
    (∀ l : ℕ, l.Prime → LocalBound k z l) ∧ (16 ≤ finrank ℚ F * k → SumBound k z)
def ZetaDenominators : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (s : ℕ), 1 ≤ s → DenomAt (maximalRealSubfield E) (2 * s)
def ZetaDenominatorsReal : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (s : ℕ), 1 ≤ s → DenomAt F (2 * s)
example : denomExp 2 (-1 / 24) = 3 ∧ denomExp 3 (-1 / 24) = 1 ∧ denomExp 2 0 = 0 := by
  have h2 : padicValNat 2 24 = 3 := by
    rw [show 24 = 2 ^ 3 * 3 by norm_num, padicValNat.mul (by norm_num) (by norm_num), padicValNat.prime_pow,
      padicValNat.eq_zero_of_not_dvd (by norm_num)]
  have h3 : padicValNat 3 24 = 1 := by
    rw [show 24 = 3 ^ 1 * 8 by norm_num, padicValNat.mul (by norm_num) (by norm_num), padicValNat.prime_pow,
      padicValNat.eq_zero_of_not_dvd (by norm_num)]
  have hn : (-1 / 24 : ℚ).num = -1 := by norm_num
  have hd : (-1 / 24 : ℚ).den = 24 := by norm_num
  refine ⟨?_, ?_, by simp [denomExp]⟩
  · simp only [denomExp, padicValRat, hn, hd, h2]; simp [padicValInt]
  · simp only [denomExp, padicValRat, hn, hd, h3]; simp [padicValInt]
theorem pir_rat : IsPrincipalIdealRing (𝓞 ℚ) :=
  IsPrincipalIdealRing.of_surjective Rat.ringOfIntegersEquiv.symm.toRingHom Rat.ringOfIntegersEquiv.symm.surjective
theorem absNorm_span_rat (n : ℕ) : Ideal.absNorm (Ideal.span {(n : 𝓞 ℚ)}) = n := by
  rw [Ideal.absNorm_span_singleton, show (n : 𝓞 ℚ) = algebraMap ℤ (𝓞 ℚ) (n : ℤ) by simp, Algebra.norm_algebraMap,
    RingOfIntegers.rank]
  simp
theorem exists_span_rat (I : Ideal (𝓞 ℚ)) : ∃ n : ℕ, I = Ideal.span {(n : 𝓞 ℚ)} := by
  haveI := pir_rat
  obtain ⟨a, rfl⟩ : ∃ a, I = Ideal.span {a} := ⟨_, (IsPrincipalIdealRing.principal I).span_singleton_generator.symm⟩
  obtain ⟨m, rfl⟩ : ∃ m : ℤ, a = (m : 𝓞 ℚ) := ⟨Rat.ringOfIntegersEquiv a, by
    apply Rat.ringOfIntegersEquiv.injective; simp⟩
  refine ⟨m.natAbs, ?_⟩
  rcases Int.natAbs_eq m with h | h
  · rw [h]; simp
  · conv_lhs => rw [h]
    rw [Int.cast_neg, Ideal.span_singleton_neg, Int.cast_natCast]
theorem isClassZeta_rat (C : ClassGroup (𝓞 ℚ)) : IsClassZeta C riemannZeta := by
  refine ⟨fun s hs => (differentiableAt_riemannZeta hs).differentiableWithinAt, fun s hs => ?_⟩
  have hs0 : s ≠ 0 := by rintro rfl; norm_num at hs
  haveI := pir_rat
  haveI : Subsingleton (ClassGroup (𝓞 ℚ)) :=
    (@Fintype.card_le_one_iff_subsingleton _ instFintypeClassGroupOfIsPrincipalIdealRing).1
      (card_classGroup_eq_one (R := 𝓞 ℚ)).le
  let g : IdealsIn C → ℕ := fun I => Ideal.absNorm (I.1 : Ideal (𝓞 ℚ))
  have hg : Function.Injective g := fun I J h => by
    obtain ⟨n, hn⟩ := exists_span_rat (I.1 : Ideal (𝓞 ℚ))
    obtain ⟨m, hm⟩ := exists_span_rat (J.1 : Ideal (𝓞 ℚ))
    simp only [g, hn, hm, absNorm_span_rat] at h
    exact Subtype.ext (Subtype.ext (by rw [hn, hm, h]))
  have hr : ∀ n ∉ Set.range g, (n : ℂ) ^ (-s) = 0 := fun n hn => by
    by_cases h0 : n = 0
    · simp [h0, hs0]
    · refine (hn ⟨⟨⟨Ideal.span {(n : 𝓞 ℚ)}, mem_nonZeroDivisors_of_ne_zero ?_⟩, Subsingleton.elim _ _⟩,
        absNorm_span_rat n⟩).elim
      simpa using h0
  refine (hg.hasSum_iff (f := fun n : ℕ => (n : ℂ) ^ (-s)) hr).2 ?_
  rw [zeta_eq_tsum_one_div_nat_cpow hs]
  simpa only [Complex.cpow_neg, one_div] using (Complex.summable_one_div_nat_cpow.2 hs).hasSum
example : IsZetaValues (F := ℚ) 2 (fun _ => -1 / 12) := fun C => ⟨_, isClassZeta_rat C, by
  have h := riemannZeta_neg_nat_eq_bernoulli 1
  have hb : bernoulli 2 = 1 / 6 := by rw [bernoulli_eq_bernoulli'_of_ne_one (by decide), bernoulli'_two]
  rw [show (1 + 1 : ℕ) = 2 from rfl, hb] at h
  rw [show (1 - ((2 : ℕ) : ℂ)) = -((1 : ℕ) : ℂ) by norm_num, h]
  norm_num⟩
end GlobalTheory.IndefiniteRowSideFullHecke.ZetaValueIdeals


