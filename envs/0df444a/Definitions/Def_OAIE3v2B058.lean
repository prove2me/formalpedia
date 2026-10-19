-- Prove2me | Definitions.Def_OAIE3v2B058
-- name    : OAIE3v2B058
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T10:12:38.176992+00:00
-- url     : https://prove2.me/theorems/d267d209-2af5-4c9b-b246-e8780d832c57
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 59 of 311
-- statement:
--   Definitions bundle 59 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B002`, `OAIE3v2B004`, `OAIE3v2B007`, `OAIE3v2B010`, `OAIE3v2B015`, `OAIE3v2B028` of this split.
--
--   Modules: `Dynamics/DetectedTranslationSeparationBudget.lean`, `Dynamics/ModeThresholdLogBudget.lean`, `Dynamics/TranslationMajorDecompositionBudget.lean`, `Dynamics/TranslationMajorDetectedPotentialBudget.lean`, `Dynamics/TranslationMajorSeparatedBudget.lean`, `Fourier/UniformScaledRetainedCharacters.lean`, `Geometry/DetectedTranslationCoordinateBudget.lean`, `Geometry/TranslationCoordinateBudget.lean`, `Lattices/AlgebraicMajorWeightedAffineTopPullback.lean`, `Polynomial/IntegerPolynomialDenominatorGrid.lean`, `Polynomial/LowTaggedPolynomialCoordinates.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B002
import Definitions.Def_OAIE3v2B004
import Definitions.Def_OAIE3v2B007
import Definitions.Def_OAIE3v2B010
import Definitions.Def_OAIE3v2B015
import Definitions.Def_OAIE3v2B028

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.DetectedTranslationSeparationBudget
namespace OAI

section

namespace Erdos3

theorem detectedTranslationSeparation_budget {p : ℝ} (hp : 0 ≤ p) :
    p ≤ (p + 3) ^ 5 ∧
      (p + 3) ^ 3 ≤ (p + 3) ^ 5 ∧
      (⌈Real.exp ((p + 2) ^ 4)⌉₊ : ℝ) ≤ Real.exp ((p + 3) ^ 5) := by
  have hbase : 1 ≤ p + 3 := by linarith
  have hlinear : p + 3 ≤ (p + 3) ^ 5 := by
    simpa only [pow_one] using pow_le_pow_right₀ hbase (by decide : 1 ≤ 5)
  refine ⟨(by linarith), pow_le_pow_right₀ hbase (by decide : 3 ≤ 5), ?_⟩
  apply (ceil_exp_le_exp_add_one (by positivity : 0 ≤ (p + 2) ^ 4)).trans
  apply Real.exp_le_exp.mpr
  have hfour : (p + 2) ^ 4 ≤ (p + 3) ^ 4 :=
    pow_le_pow_left₀ (by linarith) (by linarith) 4
  have hone : 1 ≤ (p + 3) ^ 4 := one_le_pow₀ hbase
  calc
    (p + 2) ^ 4 + 1 ≤ 2 * (p + 3) ^ 4 := by linarith
    _ ≤ (p + 3) * (p + 3) ^ 4 :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ = (p + 3) ^ 5 := by ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.ModeThresholdLogBudget
namespace OAI

section

namespace Erdos3

theorem algebraicMajor_mass_le_exp (d : ℕ) {p massF₀ massE massV Cbase : ℝ}
    (hp : 0 ≤ p) (_hF₀ : 0 ≤ massF₀) (_hE : 0 ≤ massE)
    (_hV : 0 ≤ massV) (hC : 0 ≤ Cbase)
    (hF₀p : massF₀ ≤ Real.exp p) (hEp : massE ≤ Real.exp p)
    (hVp : massV ≤ Real.exp p) (hCp : Cbase ≤ Real.exp p) :
    massF₀ + (massE + massV) * (1 + Cbase)^d ≤
      Real.exp (((d : ℝ) + 3) * (p + 2)) := by
  have hsum : massE + massV ≤ Real.exp (2*p + 1) := by
    simpa only [two_mul] using add_le_exp_add_one hp hp hEp hVp
  have hbase := one_add_le_exp_succ hp hCp
  have hterm : (massE + massV) * (1 + Cbase)^d ≤
      Real.exp (2*p + 1 + (d : ℝ)*(p + 1)) := by
    calc
      _ ≤ Real.exp (2*p + 1) * (Real.exp (p + 1))^d := by
        exact mul_le_mul hsum
          (pow_le_pow_left₀ (by positivity) hbase d) (by positivity) (by positivity)
      _ = _ := by rw [← Real.exp_nat_mul, ← Real.exp_add]
  have htotal := add_le_exp_add_one hp
    (by positivity : 0 ≤ 2*p + 1 + (d : ℝ)*(p + 1)) hF₀p hterm
  apply htotal.trans (Real.exp_le_exp.mpr ?_)
  nlinarith [Nat.cast_nonneg (α := ℝ) d]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.TranslationMajorDecompositionBudget
namespace OAI

section

namespace Erdos3

theorem exists_translationMajorDecomposition_budget (d a c : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p →
      let P := (p + a) ^ a
      let B := P + (P + c) ^ c + (2 * p + 2) ^ d + 1
      P ≤ (p + C) ^ C ∧
        (P + 2) ^ 4 ≤ (p + C) ^ C ∧
        (((d + 1 : ℕ) : ℝ) ^ 2 + 3) * (B + 2) ≤ (p + C) ^ C ∧
        2 * (((d + 1 : ℕ) : ℝ) ^ 2 + 1) * B ≤ (p + C) ^ C := by
  let P : Polynomial ℕ := (Polynomial.X + Polynomial.C a) ^ a
  let B : Polynomial ℕ := P + (P + Polynomial.C c) ^ c +
    (2 * Polynomial.X + 2) ^ d + 1
  let Q : Polynomial ℕ := (P + 2) ^ 4
  let R : Polynomial ℕ := Polynomial.C ((d + 1) ^ 2 + 3) * (B + 2)
  let S : Polynomial ℕ := Polynomial.C (2 * ((d + 1) ^ 2 + 1)) * B
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (P + Q + R + S)
  refine ⟨C, hC, ?_⟩
  intro p hp
  have hbound := hbudget p hp
  have hP := natPolynomial_eval_nonneg P hp
  have hQ := natPolynomial_eval_nonneg Q hp
  have hR := natPolynomial_eval_nonneg R hp
  have hS := natPolynomial_eval_nonneg S hp
  rw [Polynomial.eval₂_add, Polynomial.eval₂_add, Polynomial.eval₂_add] at hbound
  have hparts : P.eval₂ (Nat.castRingHom ℝ) p ≤ (p + C) ^ C ∧
      Q.eval₂ (Nat.castRingHom ℝ) p ≤ (p + C) ^ C ∧
      R.eval₂ (Nat.castRingHom ℝ) p ≤ (p + C) ^ C ∧
      S.eval₂ (Nat.castRingHom ℝ) p ≤ (p + C) ^ C :=
    ⟨by linarith, by linarith, by linarith, by linarith⟩
  simpa only [P, B, Q, R, S, Polynomial.eval₂_add, Polynomial.eval₂_mul,
    Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_C,
    Polynomial.eval₂_ofNat, Polynomial.eval₂_one, Nat.coe_castRingHom,
    Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one] using hparts

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.TranslationMajorDetectedPotentialBudget
namespace OAI

section

namespace Erdos3

theorem exists_translationMajor_detected_potential_budget (a c : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p →
      let q := (p + a) ^ a
      (q + (q + 2)^4 + 1 + c)^c ≤ (p + C)^C ∧ q ≤ (p + C)^C := by
  let Q : Polynomial ℕ := (Polynomial.X + Polynomial.C a)^a
  let R : Polynomial ℕ := (Q + (Q + 2)^4 + 1 + Polynomial.C c)^c
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget (Q + R)
  refine ⟨C, hC, fun p hp => ?_⟩
  let q : ℝ := (p + a)^a
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hR : 0 ≤ (q + (q + 2)^4 + 1 + c)^c := by positivity
  have hsum : q + (q + (q + 2)^4 + 1 + c)^c ≤ (p + C)^C := by
    simpa [Q, R, q, Polynomial.eval₂_pow] using hbound p hp
  exact ⟨(le_add_of_nonneg_left hq).trans hsum, (le_add_of_nonneg_right hR).trans hsum⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.TranslationMajorSeparatedBudget
namespace OAI

section

namespace Erdos3

theorem exists_translationMajorSeparated_budget (a c s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p →
      let p1 := (p + a) ^ a
      p1 ≤ (p + C) ^ C ∧
        (p1 + c) ^ c ≤ (p + C) ^ C ∧
        (p1 + s) ^ s ≤ (p + C) ^ C := by
  let P : Polynomial ℕ := (Polynomial.X + Polynomial.C a) ^ a
  let Q : Polynomial ℕ := (P + Polynomial.C c) ^ c
  let R : Polynomial ℕ := (P + Polynomial.C s) ^ s
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (P + Q + R)
  refine ⟨C, hC, ?_⟩
  intro p hp
  have htotal : (p + a) ^ a + ((p + a) ^ a + c) ^ c +
      ((p + a) ^ a + s) ^ s ≤ (p + C) ^ C := by
    simpa only [P, Q, R, Polynomial.eval₂_add, Polynomial.eval₂_pow,
      Polynomial.eval₂_X, Polynomial.eval₂_C, Nat.coe_castRingHom]
      using hbudget p hp
  have hP : 0 ≤ (p + a) ^ a := by positivity
  have hQ : 0 ≤ ((p + a) ^ a + c) ^ c := by positivity
  have hR : 0 ≤ ((p + a) ^ a + s) ^ s := by positivity
  dsimp only
  exact ⟨by linarith, by linarith, by linarith⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.UniformScaledRetainedCharacters
namespace OAI

section

namespace Erdos3

noncomputable def localizedMajorArcBudget (n : ℕ) (U ζ : ℝ) : ℝ :=
  multiaffineBiasBudget n (localizationThreshold U ζ (n + 1))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.DetectedTranslationCoordinateBudget
namespace OAI

section

namespace Erdos3

theorem detectedTranslationCoordinate_slow_factor_le_exp (k : ℕ) {p : ℝ}
    (hp : 0 ≤ p) (hk : (k : ℝ) ≤ p) :
    (k : ℝ) * (⌈Real.exp p⌉₊ : ℝ) * Real.exp p ≤ Real.exp ((p + 3) ^ 3) := by
  have hkexp : (k : ℝ) ≤ Real.exp p :=
    hk.trans ((le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp p))
  calc
    _ ≤ Real.exp p * Real.exp (p + 1) * Real.exp p :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul hkexp (ceil_exp_le_exp_add_one hp) (Nat.cast_nonneg _) (Real.exp_nonneg _))
        (Real.exp_nonneg _)
    _ = Real.exp (3 * p + 1) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith [sq_nonneg p, pow_nonneg hp 3])

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.TranslationCoordinateBudget
namespace OAI

section

namespace Erdos3

theorem exists_translationCoordinate_budget (d : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (n t q : ℕ) (p M B : ℝ),
      0 ≤ p → (n : ℝ) ≤ p → (t : ℝ) ≤ Real.exp p →
      0 ≤ M → M ≤ Real.exp p → 0 ≤ B → B ≤ Real.exp p →
      (q : ℝ) ≤ Real.exp p →
      ((d : ℝ) + 1) * ((t : ℝ) * M * B) *
          (1 + (n : ℝ) * d * ((t : ℝ) * M * B)) ^ d ≤
        Real.exp ((p + C) ^ C) ∧
      (d.factorial * q ^ (d + 1) : ℕ) ≤ Real.exp ((p + C) ^ C) := by
  let Q : Polynomial ℕ :=
    Polynomial.C (5 * d + 4) * Polynomial.X +
      Polynomial.C (d ^ 2 + 2 * d + 1 + d.factorial)
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget Q
  refine ⟨C, hC, ?_⟩
  intro n t q p M B hp hn ht hM hMp hB hBp hq
  have htotal : (5 * (d : ℝ) + 4) * p +
      ((d : ℝ) ^ 2 + 2 * d + 1 + d.factorial) ≤ (p + C) ^ C := by
    simpa [Q, Polynomial.eval₂_pow, Nat.cast_add, Nat.cast_mul, Nat.cast_pow] using hbudget p hp
  have hmasscost : (4 * (d : ℝ) + 3) * p + d ^ 2 + 2 * d + 1 ≤
      (p + C) ^ C := by
    have h := mul_nonneg ((show (0 : ℝ) ≤ d + 1 by positivity)) hp
    have hf : (0 : ℝ) ≤ d.factorial := Nat.cast_nonneg _
    nlinarith
  have hdenomcost : (d.factorial : ℝ) + ((d : ℝ) + 1) * p ≤ (p + C) ^ C := by
    have h := mul_nonneg ((show (0 : ℝ) ≤ 4 * d + 3 by positivity)) hp
    have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg _
    nlinarith [sq_nonneg (d : ℝ)]
  have hnp : (n : ℝ) ≤ Real.exp p := hn.trans (by linarith [Real.add_one_le_exp p])
  have hdp : (d : ℝ) ≤ Real.exp d := by linarith [Real.add_one_le_exp (d : ℝ)]
  have ha : (t : ℝ) * M * B ≤ Real.exp (3 * p) := by
    calc
      _ ≤ Real.exp p * Real.exp p * Real.exp p := by gcongr
      _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have hprod : (n : ℝ) * d * ((t : ℝ) * M * B) ≤ Real.exp (4 * p + d) := by
    calc
      _ ≤ Real.exp p * Real.exp d * Real.exp (3 * p) := by gcongr
      _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have hplus : 1 + (n : ℝ) * d * ((t : ℝ) * M * B) ≤
      Real.exp (4 * p + d + 1) := one_add_le_exp_succ (by positivity) hprod
  have hfactor : (d : ℝ) + 1 ≤ Real.exp ((d : ℝ) + 1) := by
    linarith [Real.add_one_le_exp ((d : ℝ) + 1)]
  constructor
  · calc
      _ ≤ Real.exp ((d : ℝ) + 1) * Real.exp (3 * p) *
          Real.exp (4 * p + d + 1) ^ d := by gcongr
      _ = Real.exp ((4 * (d : ℝ) + 3) * p + d ^ 2 + 2 * d + 1) := by
        rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      _ ≤ _ := Real.exp_le_exp.mpr hmasscost
  · have hf : (d.factorial : ℝ) ≤ Real.exp d.factorial := by
      linarith [Real.add_one_le_exp (d.factorial : ℝ)]
    push_cast
    calc
      (d.factorial : ℝ) * (q : ℝ) ^ (d + 1) ≤
          Real.exp d.factorial * (Real.exp p) ^ (d + 1) := by gcongr
      _ = Real.exp ((d.factorial : ℝ) + ((d : ℝ) + 1) * p) := by
        rw [← Real.exp_nat_mul, ← Real.exp_add]
        push_cast
        rfl
      _ ≤ _ := Real.exp_le_exp.mpr hdenomcost

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AlgebraicMajorWeightedAffineTopPullback
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial

variable {U B : Type*}

noncomputable def jointResidueAffinePolynomial (q : ℕ) (r : U → ℤ)
    (D : MvPolynomial (U ⊕ B) ℝ) : MvPolynomial (U ⊕ B) ℝ :=
  aeval (Sum.elim (fun i => C (r i : ℝ) + C (q : ℝ) * X (Sum.inl i))
    (fun j => X (Sum.inr j))) D

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.IntegerPolynomialDenominatorGrid
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial

variable {σ : Type*}

theorem add_integerPolynomial_coefficientGrid (R : MvPolynomial σ ℚ)
    (I : MvPolynomial σ ℤ) (q : ℕ)
    (hR : (fun α => R.coeff α) ∈ denominatorGrid q) :
    (fun α => (R + map (Int.castRingHom ℚ) I).coeff α) ∈ denominatorGrid q := by
  obtain ⟨z, hz⟩ := hR
  refine ⟨fun α => z α + (q : ℤ) * I.coeff α, fun α => ?_⟩
  change (q : ℚ) * (R + map (Int.castRingHom ℚ) I).coeff α = _
  have hα : (q : ℚ) * R.coeff α = (z α : ℚ) := hz α
  simp only [MvPolynomial.coeff_add, coeff_map, Int.cast_add,
    Int.cast_mul, Int.cast_natCast, mul_add, hα]
  rfl

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.LowTaggedPolynomialCoordinates
namespace OAI

section

namespace Erdos3.VectorPolynomial

open _root_.MvPolynomial
open scoped BigOperators

variable {m : ℕ} (J : Fin m → Type*) [∀ j, Fintype (J j)]

theorem lowTagged_sum (d : ℕ) {V : Type*} [AddCommMonoid V] (f : (Σ j, J j) → V) :
    (∑ i : Σ j, J j, if i.1.val + 1 ≤ d then f i else 0) =
      ∑ i : Fin (Fintype.card (LowTaggedIndex J d)), f (lowTaggedIndex J d i) := by
  classical
  calc
    _ = ∑ i : LowTaggedIndex J d, f i.val := by
      rw [← Finset.sum_filter]
      exact Finset.sum_subtype _ (by simp) f
    _ = _ := Fintype.sum_equiv (Fintype.equivFin (LowTaggedIndex J d)) _ _
      (fun i => by simp only [lowTaggedIndex, Equiv.symm_apply_apply])

end Erdos3.VectorPolynomial

end

end OAI
end


