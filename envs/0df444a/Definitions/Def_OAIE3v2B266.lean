-- Prove2me | Definitions.Def_OAIE3v2B266
-- name    : OAIE3v2B266
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-18T06:49:00.10799+00:00
-- url     : https://prove2.me/theorems/f7ae36d1-804b-4d32-a614-90c637623c10
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 275 of 311
-- statement:
--   Definitions bundle 275 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B255`, `OAIE3v2B256`, `OAIE3v2B303`, `OAIE3v2B259`, `OAIE3v2B260`, `OAIE3v2B261` of this split.
--
--   Modules: `Dynamics/AllocatedExternalCandidateResetSuccessor.lean`, `Dynamics/CanonicalZeroLayerBudgetedInitialization.lean`, `Estimates/AllocatedExternalCandidateGeneratedFreezingSuccessor.lean`, `Estimates/AllocatedExternalCandidateThresholdSuccessor.lean`, `Estimates/DiagonalRowTransfer.lean`, `Estimates/HigherResidualRowDifferences.lean`, `Estimates/PreparedCenteredModelMarginalData.lean`, `Estimates/PreparedCenteredStagedModelProductiveGood.lean`, `Estimates/PreparedReadyPaddedRelativeInitialization.lean`, `Estimates/PreparedRelativeEndpointNumericalBounds.lean`, `Estimates/PreparedRelativeFinalPower.lean`, `Estimates/QuadraticCyclicAntisymmetric.lean`, `Estimates/QuadraticPairCorrelator.lean`, `Estimates/QuadraticPairStepDrop.lean`, `Estimates/UnconditionedArbitraryFixedPatchFamily.lean`, `Geometry/QuadraticAntisymmetricBox.lean`, `Lattices/NativeCorrelatedAffineExistence.lean`, `Polynomial/AllocatedZeroLayerDegreeScalarConclusion.lean`, `Polynomial/CandidateNestedDegreeNetSchedule.lean`, `Polynomial/PreparedUniformDegreeDirectMasterBudget.lean`, `Sampling/AllocatedExternalCandidatePhysicalScore.lean`, `Sampling/ForecastLawPhysicalAmbientHaarComparison.lean`, `Sampling/PreparedRelativeEndpointForecastBudget.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B255
import Definitions.Def_OAIE3v2B256
import Definitions.Def_OAIE3v2B303
import Definitions.Def_OAIE3v2B259
import Definitions.Def_OAIE3v2B260
import Definitions.Def_OAIE3v2B261

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.QuadraticCyclicAntisymmetric
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem exists_quadratic_bounded_mixed_correlation :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ}, 0 ≤ p →
      ∀ f : ZMod N → ℂ, (∀ x, ‖f x‖ ≤ 1) → Real.exp (-p) ≤ gowersNorm 3 f →
      ∃ H : Finset (ZMod N), H.Nonempty ∧
        Real.exp (-((p + C) ^ C)) * N ≤ (H.card : ℝ) ∧
        ∃ F : NativeBoundedMultidegreeFamily (mixedCorrelationDegree 1) (Fin 1 × Unit) ((p + C) ^ C),
          ∀ h ∈ H, Real.exp (-((p + C) ^ C)) ≤
            ‖𝔼 n : ZMod N, multiplicativeDerivative f h n *
              star (F.eval (0, ()) (correlationInput (h.val : ℤ) (n.val : ℤ)))‖ := by
  obtain ⟨A, _, hfrequency⟩ := exists_quadratic_local_frequency
  obtain ⟨B, _, hfamily⟩ := exists_quadratic_bounded_family
  let X : Polynomial ℕ := Polynomial.X
  let Q : Polynomial ℕ := (X + Polynomial.C A) ^ A
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (Q + 1 + (Q + 1 + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro N _ p hp f hf hG
  let q := (p + A) ^ A
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have htotal : q + 1 + (q + 1 + B) ^ B ≤ (p + C) ^ C := by
    simpa [X, Q, q, Polynomial.eval₂_pow] using hbudget p hp
  have hqC : q + 1 ≤ (p + C) ^ C := by
    have : 0 ≤ (q + 1 + B) ^ B := by positivity
    linarith
  have hfamilyC : (q + 1 + B) ^ B ≤ (p + C) ^ C := by linarith
  obtain ⟨H, hH, hdense, r, u, c, b, a, h₀, hr, _, _, _, hcorr⟩ := hfrequency hp f hf hG
  obtain ⟨F, hF⟩ := hfamily (show 1 ≤ q + 1 by linarith) r (by linarith : (r : ℝ) ≤ q + 1)
    a b u c h₀
  refine ⟨H, hH, ?_, F.mono hfamilyC, ?_⟩
  · exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by linarith : -((p + C) ^ C) ≤ -q))
      (Nat.cast_nonneg _)).trans hdense
  · intro h hh
    obtain ⟨hsmall, hc⟩ := hcorr h hh
    have hvalue (n : ZMod N) : F.eval (0, ()) (correlationInput (h.val : ℤ) (n.val : ℤ)) =
        CircleFourier.character (((n.val : ℝ) *
          (a + ∑ i, affineCyclicTorusLocalLift u c h₀ h i * b i) : ℝ) : CircleFourier.Circle) / 2 := by
      simpa only [Int.cast_natCast] using
        hF h (fun i => (hsmall i).trans (by norm_num)) (n.val : ℤ)
    simp only [NativeBoundedMultidegreeFamily.mono_eval, hvalue, star_div₀, star_ofNat,
      ← mul_div_assoc, ← Finset.expect_div, norm_div, Complex.norm_ofNat]
    exact (Real.exp_le_exp.mpr (by linarith : -((p + C) ^ C) ≤ -q - 1)).trans
      ((exp_sub_one_le_half_exp (-q)).trans (div_le_div_of_nonneg_right hc (by norm_num : (0 : ℝ) ≤ 2)))

end Erdos3

end

section

namespace Erdos3

theorem exists_quadratic_native_mixed_correlation :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ}, 0 ≤ p →
      ∀ f : ZMod N → ℂ, (∀ x, ‖f x‖ ≤ 1) → Real.exp (-p) ≤ gowersNorm 3 f →
        Nonempty (NativeMixedCorrelation 1 N ((p + C) ^ C) f) := by
  obtain ⟨A, _, hbounded⟩ := exists_quadratic_bounded_mixed_correlation
  obtain ⟨B, _, hconvert⟩ := exists_native_mixed_of_bounded 1
  let X : Polynomial ℕ := Polynomial.X
  let Q : Polynomial ℕ := (X + Polynomial.C A) ^ A
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((Q + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro N _ p hp f hf hG
  let q := (p + A) ^ A
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hbound : (q + B) ^ B ≤ (p + C) ^ C := by
    simpa [X, Q, q, Polynomial.eval₂_pow] using hbudget p hp
  obtain ⟨H, hH, hdense, F, hcorr⟩ := hbounded hp f hf hG
  obtain ⟨W⟩ := hconvert hq f hf H hH hdense F (0, ()) hcorr
  exact ⟨W.mono hbound⟩

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_quadratic_fixed_mixed_correlation :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ}, 0 ≤ p →
      ∀ f : ZMod N → ℂ, (∀ x, ‖f x‖ ≤ 1) → Real.exp (-p) ≤ gowersNorm 3 f →
      ∃ H : Finset (ZMod N), H.Nonempty ∧ Real.exp (-((p + C) ^ C)) * N ≤ (H.card : ℝ) ∧
        ∃ M : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) ((p + C) ^ C),
          ∃ i : Fin M.outputDim, ∀ h ∈ H,
            Real.exp (-((p + C) ^ C)) ≤
              ‖𝔼 x, multiplicativeDerivative f h x * star (M.evalCyclic N i (correlationInput h x))‖ := by
  obtain ⟨A, _, hMixed⟩ := exists_quadratic_native_mixed_correlation
  let X : Polynomial ℕ := Polynomial.X
  let Q : Polynomial ℕ := (X + Polynomial.C A) ^ A
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (2 * Q)
  refine ⟨C, hC, ?_⟩
  intro N _ p hp f hf hG
  let q := (p + A) ^ A
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hbound : 2 * q ≤ (p + C) ^ C := by
    simpa [X, Q, q, Polynomial.eval₂_pow] using hbudget p hp
  have hqC : q ≤ (p + C) ^ C := by linarith
  obtain ⟨W⟩ := hMixed hp f hf hG
  obtain ⟨i, H, _, hH, hdense, hcorr⟩ := W.exists_fixed_quadratic_coordinate
  refine ⟨H, hH, ?_, W.mixed.mono hqC, i, ?_⟩
  · exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hbound))
      (Nat.cast_nonneg _)).trans hdense
  · intro h hh
    exact (Real.exp_le_exp.mpr (neg_le_neg hbound)).trans (hcorr h hh)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_quadratic_corner_model :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ}, 0 ≤ p →
      ∀ f : ZMod N → ℂ, (∀ x, ‖f x‖ ≤ 1) → Real.exp (-p) ≤ gowersNorm 3 f →
      ∃ H : Finset (ZMod N), H.Nonempty ∧
        Real.exp (-((p + C) ^ C)) * N ≤ (H.card : ℝ) ∧
        ∃ M : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) ((p + C) ^ C),
          ∃ i : Fin M.outputDim,
            (∀ h ∈ H, Real.exp (-((p + C) ^ C)) ≤
              ‖𝔼 n : ZMod N, multiplicativeDerivative f h n *
                star (M.evalCyclic N i (correlationInput h n))‖) ∧
            ∃ b₁ b₂ b₃ : ZMod N → ℂ,
              (∀ x, ‖b₁ x‖ ≤ 1) ∧ (∀ y, ‖b₂ y‖ ≤ 1) ∧ (∀ z, ‖b₃ z‖ ≤ 1) ∧
              Real.exp (-((p + C) ^ C)) ≤
                (𝔼 x : ZMod N, 𝔼 y : ZMod N,
                  M.evalCyclic N i (correlationInput y x) *
                    b₁ x * b₂ y * b₃ (x + y)).re := by
  obtain ⟨A, _, hfixed⟩ := exists_quadratic_fixed_mixed_correlation
  let X : Polynomial ℕ := Polynomial.X
  let P : Polynomial ℕ := (X + Polynomial.C A) ^ A
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (2 * P)
  refine ⟨C, hC, ?_⟩
  intro N _ p hp f hf hG
  classical
  let q := (p + A) ^ A
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have htotal : 2 * q ≤ (p + C) ^ C := by
    simpa [X, P, q, Polynomial.eval₂_pow] using hbudget p hp
  have hqC : q ≤ (p + C) ^ C := by linarith
  obtain ⟨H, hH, hdense, M, i, hcorr⟩ := hfixed hp f hf hG
  let g (h n : ZMod N) := M.evalCyclic N i (correlationInput h n)
  have hN : (0 : ℝ) < N := by exact_mod_cast NeZero.pos N
  have hindicator : (𝔼 h : ZMod N, if h ∈ H then Real.exp (-q) else 0) =
      (H.card : ℝ) * Real.exp (-q) / N := by
    rw [Fintype.expect_eq_sum_div_card]
    simp
  have hmean : Real.exp (-(2 * q)) ≤
      𝔼 h : ZMod N, ‖𝔼 n : ZMod N, multiplicativeDerivative f h n * star (g h n)‖ := by
    calc
      _ = Real.exp (-q) * Real.exp (-q) := by
        rw [← Real.exp_add]
        congr 1
        ring
      _ ≤ (H.card : ℝ) * Real.exp (-q) / N := by
        apply (le_div_iff₀ hN).mpr
        nlinarith [mul_le_mul_of_nonneg_right hdense (Real.exp_nonneg (-q))]
      _ = _ := hindicator.symm
      _ ≤ _ := by
        apply Finset.expect_le_expect
        intro h _
        split_ifs with hh
        · exact hcorr h hh
        · exact norm_nonneg _
  obtain ⟨b₁, b₂, b₃, hb₁, hb₂, hb₃, hcorner⟩ :=
    exists_correlated_corner f g hf hmean
  refine ⟨H, hH, ?_, M.mono hqC, i, ?_, b₁, b₂, b₃, hb₁, hb₂, hb₃, ?_⟩
  · exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hqC))
      (Nat.cast_nonneg _)).trans hdense
  · intro h hh
    exact (Real.exp_le_exp.mpr (neg_le_neg hqC)).trans (hcorr h hh)
  · exact (Real.exp_le_exp.mpr (neg_le_neg htotal)).trans hcorner

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_quadratic_reflected_model :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ}, 0 ≤ p →
      ∀ f : ZMod N → ℂ, (∀ x, ‖f x‖ ≤ 1) → Real.exp (-p) ≤ gowersNorm 3 f →
      ∃ H : Finset (ZMod N), H.Nonempty ∧
        Real.exp (-((p + C) ^ C)) * N ≤ (H.card : ℝ) ∧
        ∃ M : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) ((p + C) ^ C),
          ∃ i : Fin M.outputDim,
            (∀ h ∈ H, Real.exp (-((p + C) ^ C)) ≤
              ‖𝔼 n : ZMod N, multiplicativeDerivative f h n *
                star (M.evalCyclic N i (correlationInput h n))‖) ∧
            ∃ (n₀ : ZMod N) (b : ZMod N → ℂ), (∀ y, ‖b y‖ ≤ 1) ∧
              Real.exp (-((p + C) ^ C)) ≤
                (𝔼 y : ZMod N, 𝔼 y' : ZMod N,
                  M.evalCyclic N i (correlationInput y (n₀ - y - y')) *
                    star (M.evalCyclic N i (correlationInput y' (n₀ - y - y'))) *
                    b y * star (b y')).re := by
  obtain ⟨A, _, hcorner⟩ := exists_quadratic_corner_model
  let X : Polynomial ℕ := Polynomial.X
  let P : Polynomial ℕ := (X + Polynomial.C A) ^ A
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (2 * P)
  refine ⟨C, hC, ?_⟩
  intro N _ p hp f hf hG
  let q := (p + A) ^ A
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have htotal : 2 * q ≤ (p + C) ^ C := by
    simpa [X, P, q, Polynomial.eval₂_pow] using hbudget p hp
  have hqC : q ≤ (p + C) ^ C := by linarith
  obtain ⟨H, hH, hdense, M, i, hcorr, b₁, b₂, b₃, hb₁, hb₂, hb₃, hc⟩ := hcorner hp f hf hG
  obtain ⟨z, b, hb, hreflected⟩ := exists_reflected_corner_correlation
    (fun y x => M.evalCyclic N i (correlationInput y x))
    b₁ b₂ b₃ hb₁ hb₂ hb₃ (Real.exp_nonneg (-q)) hc
  have hpower : Real.exp (-q) ^ 2 = Real.exp (-(2 * q)) := by
    rw [← Real.exp_nat_mul]
    congr 1
    norm_num
  rw [hpower] at hreflected
  refine ⟨H, hH, ?_, M.mono hqC, i, ?_, z, b, hb, ?_⟩
  · exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hqC))
      (Nat.cast_nonneg _)).trans hdense
  · intro h hh
    exact (Real.exp_le_exp.mpr (neg_le_neg hqC)).trans (hcorr h hh)
  · exact (Real.exp_le_exp.mpr (neg_le_neg htotal)).trans hreflected

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_quadratic_cyclic_antisymmetric :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ}, 0 ≤ p →
      ∀ f : ZMod N → ℂ, (∀ x, ‖f x‖ ≤ 1) → Real.exp (-p) ≤ gowersNorm 3 f →
      ∃ H : Finset (ZMod N), H.Nonempty ∧
        Real.exp (-((p + C) ^ C)) * N ≤ (H.card : ℝ) ∧
        ∃ M : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) ((p + C) ^ C),
          ∃ i : Fin M.outputDim,
            (∀ h ∈ H, Real.exp (-((p + C) ^ C)) ≤
              ‖𝔼 n : ZMod N, multiplicativeDerivative f h n *
                star (M.evalCyclic N i (correlationInput h n))‖) ∧
            ∃ (i' j' : Fin M.outputDim) (a b : ZMod N → ℂ),
              (∀ x, ‖a x‖ ≤ 1) ∧ (∀ y, ‖b y‖ ≤ 1) ∧
              Real.exp (-((p + C) ^ C)) ≤
                ‖𝔼 x : ZMod N, 𝔼 y : ZMod N,
                  star (M.evalCyclic N i' (correlationInput x y)) *
                    M.evalCyclic N j' (correlationInput y x) * a x * b y‖ := by
  obtain ⟨A, _, hreflect⟩ := exists_quadratic_reflected_model
  obtain ⟨B, _, hanti⟩ := exists_integer_antisymmetric_correlation
  let X : Polynomial ℕ := Polynomial.X
  let Q := (X + Polynomial.C A) ^ A
  let R := 2 * Q + 10
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (R + (R + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro N _ p hp f hf hG
  let q := (p + A) ^ A
  let r := 2 * q + 10
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hqr : q ≤ r := by dsimp [r]; linarith
  have hcost : r + (r + B) ^ B ≤ (p + C) ^ C := by
    simpa [X, Q, R, q, r, Polynomial.eval₂_pow] using hbudget p hp
  have hr : 0 ≤ r := hq.trans hqr
  have hqC : q ≤ (p + C) ^ C := by have := pow_nonneg (by positivity : 0 ≤ r + B) B; linarith
  have hfinal : (r + B) ^ B ≤ (p + C) ^ C := by linarith
  obtain ⟨H, hH, hdense, M, i, hcorr, z, b, hb, hreflected⟩ := hreflect hp f hf hG
  have heval (k : Fin M.outputDim) (x n : ZMod N) :
      M.eval k (correlationInput (x.val : ℤ) (n.val : ℤ)) = M.evalCyclic N k (correlationInput x n) := by
    apply congrArg (M.eval k)
    funext j
    exact Fin.cases rfl (fun _ => rfl) j
  let F (x n : ℤ) := M.eval i (correlationInput x n)
  have hc : Real.exp (-q) ≤ ‖𝔼 x : ZMod N, 𝔼 y : ZMod N,
      F x.val (z - x - y).val * star (F y.val (z - x - y).val) * b x * star (b y)‖ := by
    simpa only [F, heval] using hreflected.trans (Complex.re_le_norm _)
  obtain ⟨k, a₀, b₀, ha₀, hb₀, hunwrapped⟩ := exists_unwrapped_reflected_correlation
    hq F F (fun _ _ => M.norm_eval i _) (fun _ _ => M.norm_eval i _) z b hb hc
  have hpairMean (g : ZMod N → ZMod N → ℂ) :
      (𝔼 u : ZMod N × ZMod N, g u.1 u.2) = 𝔼 x : ZMod N, 𝔼 y : ZMod N, g x y := by
    rw [← Finset.univ_product_univ, Finset.expect_product]
  obtain ⟨i', j', a₁, b₁, ha₁, hb₁, hantisymmetric⟩ := hanti (M.mono hqr)
    ((z.val : ℤ) + (k.val : ℤ) * N) i i (Finset.univ : Finset (ZMod N × ZMod N))
    Finset.univ_nonempty (fun u => (u.1.val : ℤ)) (fun u => (u.2.val : ℤ))
    a₀ b₀ ha₀ hb₀ (by
      simpa only [← Finset.univ_product_univ, Finset.expect_product,
        NativeMultidegreeNilcharacter.mono_eval, r, F] using hunwrapped)
  change Fin M.outputDim at i' j'
  change Real.exp (-((r + B) ^ B)) ≤
    ‖𝔼 u : ZMod N × ZMod N,
      star (M.eval i' (correlationInput (u.1.val : ℤ) (u.2.val : ℤ))) *
        M.eval j' (correlationInput (u.2.val : ℤ) (u.1.val : ℤ)) *
        a₁ u.1.val * b₁ u.2.val‖ at hantisymmetric
  rw [hpairMean (fun x y =>
    star (M.eval i' (correlationInput (x.val : ℤ) (y.val : ℤ))) *
      M.eval j' (correlationInput (y.val : ℤ) (x.val : ℤ)) *
      a₁ x.val * b₁ y.val)] at hantisymmetric
  simp_rw [heval] at hantisymmetric
  refine ⟨H, hH, ?_, M.mono hqC, i, ?_, i', j', (fun x => a₁ x.val), (fun y => b₁ y.val),
    (fun x => ha₁ _), (fun y => hb₁ _), ?_⟩
  · exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hqC))
      (Nat.cast_nonneg _)).trans hdense
  · intro h hh
    exact (Real.exp_le_exp.mpr (neg_le_neg hqC)).trans (hcorr h hh)
  · exact (Real.exp_le_exp.mpr (neg_le_neg hfinal)).trans hantisymmetric

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.QuadraticAntisymmetricBox
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem exists_quadratic_antisymmetric_box :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ}, 0 ≤ p →
      ∀ f : ZMod N → ℂ, (∀ x, ‖f x‖ ≤ 1) → Real.exp (-p) ≤ gowersNorm 3 f →
      ∃ H : Finset (ZMod N), H.Nonempty ∧
        Real.exp (-((p + C) ^ C)) * N ≤ (H.card : ℝ) ∧
        ∃ M : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) ((p + C) ^ C),
          ∃ i : Fin M.outputDim,
            (∀ h ∈ H, Real.exp (-((p + C) ^ C)) ≤
              ‖𝔼 n : ZMod N, multiplicativeDerivative f h n *
                star (M.evalCyclic N i (correlationInput h n))‖) ∧
            ∃ i' j' : Fin M.outputDim,
              Real.exp (-((p + C) ^ C)) ≤
                (finiteBoxCorrelation (fun x y : ZMod N =>
                  star (M.evalCyclic N i' (correlationInput x y)) *
                    M.evalCyclic N j' (correlationInput y x))).re := by
  obtain ⟨A, _, hanti⟩ := exists_quadratic_cyclic_antisymmetric
  let Q : Polynomial ℕ := (Polynomial.X + Polynomial.C A) ^ A
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (4 * Q)
  refine ⟨C, hC, ?_⟩
  intro N _ p hp f hf hG
  let q := (p + A) ^ A
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hcost : 4 * q ≤ (p + C) ^ C := by
    simpa [Q, q, Polynomial.eval₂_pow] using hbudget p hp
  have hqC : q ≤ (p + C) ^ C := by linarith
  obtain ⟨H, hH, hdense, M, i, hcorr, i', j', a, b, ha, hb, hpair⟩ := hanti hp f hf hG
  let K (x y : ZMod N) :=
    star (M.evalCyclic N i' (correlationInput x y)) * M.evalCyclic N j' (correlationInput y x)
  have hbox : Real.exp (-q) ^ 4 ≤ (finiteBoxCorrelation K).re :=
    (pow_le_pow_left₀ (Real.exp_nonneg _) hpair 4).trans
      (norm_weighted_pair_mean_pow_four_le_box K a b ha hb)
  have hpower : Real.exp (-q) ^ 4 = Real.exp (-(4 * q)) := by
    rw [← Real.exp_nat_mul]
    congr 1
    norm_num
  rw [hpower] at hbox
  refine ⟨H, hH, ?_, M.mono hqC, i, ?_, i', j', ?_⟩
  · exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hqC))
      (Nat.cast_nonneg _)).trans hdense
  · intro h hh
    exact (Real.exp_le_exp.mpr (neg_le_neg hqC)).trans (hcorr h hh)
  · exact (Real.exp_le_exp.mpr (neg_le_neg hcost)).trans hbox

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.QuadraticPairCorrelator
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem exists_quadratic_pair_correlator :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ}, 0 ≤ p →
      ∀ f : ZMod N → ℂ, (∀ x, ‖f x‖ ≤ 1) → Real.exp (-p) ≤ gowersNorm 3 f →
      ∃ q : ℝ, 0 ≤ q ∧ q ≤ (p + C) ^ C ∧
        ∃ H : Finset (ZMod N), H.Nonempty ∧ Real.exp (-q) * N ≤ (H.card : ℝ) ∧
          ∃ M : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) q,
            ∃ i : Fin M.outputDim,
              (∀ h ∈ H, Real.exp (-q) ≤
                ‖𝔼 n : ZMod N, multiplicativeDerivative f h n *
                  star (M.evalCyclic N i (correlationInput h n))‖) ∧
              ∃ i' j' : Fin M.outputDim,
                Nonempty (NativeSampleCorrelation (fun _ : Fin 2 => 1) 1 ((p + C) ^ C)
                  Finset.univ (fun z : Fin 2 → ZMod N => fun k => ((z k).val : ℤ))
                  (fun z => M.antisymmetricKernel i' j' ((z 0).val : ℤ) ((z 1).val : ℤ))) := by
  obtain ⟨A, _, hbox⟩ := exists_quadratic_antisymmetric_box
  obtain ⟨B, _, hpair⟩ := exists_antisymmetric_pair_correlation
  let X : Polynomial ℕ := Polynomial.X
  let Q := (X + Polynomial.C A) ^ A
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (Q + (Q + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro N _ p hp f hf hG
  let q := (p + A) ^ A
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hcost : q + (q + B) ^ B ≤ (p + C) ^ C := by
    simpa [X, Q, q, Polynomial.eval₂_pow] using hbudget p hp
  have hqC : q ≤ (p + C) ^ C := (le_add_of_nonneg_right (by positivity)).trans hcost
  have hBC : (q + B) ^ B ≤ (p + C) ^ C := (le_add_of_nonneg_left hq).trans hcost
  obtain ⟨H, hH, hdense, M, i, hcorr, i', j', hbias⟩ := hbox hp f hf hG
  obtain ⟨V⟩ := hpair hq M i' j' hbias
  exact ⟨q, hq, hqC, H, hH, hdense, M, i, hcorr, i', j', ⟨V.mono hBC⟩⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.QuadraticPairStepDrop
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem exists_quadratic_pair_step_drop :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ}, 0 ≤ p →
      Real.exp ((p + C) ^ C) ≤ (N : ℝ) →
      ∀ f : ZMod N → ℂ, (∀ x, ‖f x‖ ≤ 1) → Real.exp (-p) ≤ gowersNorm 3 f →
      ∃ q r : ℝ, 0 ≤ q ∧ q ≤ (p + C) ^ C ∧ 0 ≤ r ∧ r ≤ (p + C) ^ C ∧
        ∃ H : Finset (ZMod N), H.Nonempty ∧ Real.exp (-q) * N ≤ (H.card : ℝ) ∧
          ∃ M : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) q,
            ∃ i : Fin M.outputDim,
              (∀ h ∈ H, Real.exp (-q) ≤
                ‖𝔼 n : ZMod N, multiplicativeDerivative f h n *
                  star (M.evalCyclic N i (correlationInput h n))‖) ∧
              ∃ i' j' : Fin M.outputDim,
                ∃ V : NativeSampleCorrelation (fun _ : Fin 2 => 1) 1 r
                  Finset.univ (fun z : Fin 2 → ZMod N => fun k => ((z k).val : ℤ))
                  (fun z => M.antisymmetricKernel i' j' ((z 0).val : ℤ) ((z 1).val : ℤ)),
                  Nonempty (NativeAntisymmetricPairFactorization V ((p + C) ^ C)) := by
  obtain ⟨A, _, hcorr⟩ := exists_quadratic_pair_correlator
  obtain ⟨B, _, hdrop⟩ := exists_antisymmetric_pair_step_drop
  let X : Polynomial ℕ := Polynomial.X
  let T := (X + Polynomial.C A) ^ A
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (T + (2 * T + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro N _ p hp hN f hf hG
  let t := (p + A) ^ A
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hcost : t + (2 * t + B) ^ B ≤ (p + C) ^ C := by
    simpa [X, T, t, Polynomial.eval₂_pow] using hbudget p hp
  have htC : t ≤ (p + C) ^ C := (le_add_of_nonneg_right (by positivity)).trans hcost
  have hBC : (2 * t + B) ^ B ≤ (p + C) ^ C := (le_add_of_nonneg_left ht).trans hcost
  obtain ⟨q, hq, hqt, H, hH, hdense, M, i, hderiv, i', j', ⟨V⟩⟩ := hcorr hp f hf hG
  have hpair : (q + t + B) ^ B ≤ (p + C) ^ C := by
    apply le_trans _ hBC
    apply pow_le_pow_left₀ (by positivity)
    change q + t + B ≤ 2 * t + B
    linarith
  obtain ⟨F⟩ := hdrop V ((Real.exp_le_exp.mpr hpair).trans hN)
  exact ⟨q, t, hq, hqt.trans htC, ht, htC, H, hH, hdense, M, i, hderiv, i', j', V,
    ⟨F.mono hpair⟩⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.NativeCorrelatedAffineExistence
namespace OAI

section

namespace Erdos3

open Module RationalFilteredNilmanifold VectorPolynomial
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

theorem exists_native_correlated_comparison_budget (s : ℕ) (hs : 2 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p →
      let Z := (p + nativeSharedFreeRelationConstant s hs) ^ nativeSharedFreeRelationConstant s hs
      Z ≤ (p + C) ^ C ∧ ∀ A : ℝ, 0 ≤ A → A ≤ Z →
        sharedFreeCorrelationBudget s hs Z ≤ (p + C) ^ C ∧
        Z + (Z + sharedFreeAffineConstant s) ^ sharedFreeAffineConstant s +
          sharedFreeCorrelationBudget s hs Z ≤ (p + C) ^ C ∧
        ((sharedFreeCorrelationBudget s hs Z + sharedFreeComparisonBasisBudget A Z + 2) +
          nativePairModelConstant s) ^ nativePairModelConstant s ≤ (p + C) ^ C ∧
        nativeLowerPairModelBudget s
          (sharedFreeCorrelationBudget s hs Z + sharedFreeComparisonBasisBudget A Z + 2) ≤
          (p + C) ^ C := by
  let a := nativeSharedFreeRelationConstant s hs
  obtain ⟨b, _, hbound⟩ := exists_sharedFreeCorrelationBudget_bound s hs
  let Z₀ : Polynomial ℕ := (Polynomial.X + Polynomial.C a) ^ a
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (Z₀ + (Z₀ + Polynomial.C b) ^ b)
  refine ⟨C, hC, ?_⟩
  intro p hp Z
  have hZ : 0 ≤ Z := pow_nonneg (add_nonneg hp (Nat.cast_nonneg _)) _
  have hsum : Z + (Z + b) ^ b ≤ (p + C) ^ C := by
    change (p + a) ^ a + ((p + a) ^ a + b) ^ b ≤ (p + C) ^ C
    simpa [Z₀, Polynomial.eval₂_pow] using hbudget p hp
  have hZC : Z ≤ (p + C) ^ C :=
    (le_add_of_nonneg_right (pow_nonneg (add_nonneg hZ (Nat.cast_nonneg b)) b)).trans hsum
  have hbC : (Z + b) ^ b ≤ (p + C) ^ C := (le_add_of_nonneg_left hZ).trans hsum
  refine ⟨hZC, ?_⟩
  intro A hA hAZ
  obtain ⟨hmain, hpair, hlower⟩ := hbound A Z hA hAZ hZ
  have hΛ : 0 ≤ (Z + sharedFreeAffineConstant s) ^ sharedFreeAffineConstant s :=
    pow_nonneg (add_nonneg hZ (Nat.cast_nonneg _)) _
  have hcorrCost : sharedFreeCorrelationBudget s hs Z ≤ (p + C) ^ C :=
    (le_add_of_nonneg_left hΛ).trans (hmain.trans hbC)
  have htotal : Z + (Z + sharedFreeAffineConstant s) ^ sharedFreeAffineConstant s +
      sharedFreeCorrelationBudget s hs Z ≤ (p + C) ^ C := by
    linarith only [hmain, hsum]
  exact ⟨hcorrCost, htotal, hpair.trans hbC, hlower.trans hbC⟩

theorem exists_native_correlated_affine_comparison (s : ℕ) (hs : 2 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {r N : ℕ} [NeZero N] {p : ℝ} {f : ZMod N → ℂ}
      (W : NativeCorrelationStructure s (r + 1) N p f), (∀ x, ‖f x‖ ≤ 1) →
      Real.exp ((p + C) ^ C) ≤ (N : ℝ) → W.HasCorrelatedAffineComparison hs C := by
  obtain ⟨C, hC, hbudget⟩ := exists_native_correlated_comparison_budget s hs
  refine ⟨C, hC, ?_⟩
  intro r N _ p f W hf hN
  unfold NativeCorrelationStructure.HasCorrelatedAffineComparison
  intro Z
  have hp : 0 ≤ p := (Nat.cast_nonneg _).trans W.family.complexity.1.1
  obtain ⟨hZC, hcost⟩ := hbudget p hp
  have hZ : 0 ≤ Z := pow_nonneg (add_nonneg hp (Nat.cast_nonneg _)) _
  obtain ⟨A, hpA, hAZ, out, H, q, P, hHW, hH, hshort, hpq, hqP, hPA,
      R, D, B, E, T, hT, hTfil, hcentral, hframe, hdata⟩ :=
    (exists_native_shared_free_rank_relation s hs).choose_spec.2 W hf
      ((Real.exp_le_exp.mpr hZC).trans hN)
  let := moduleTopology ℝ (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra) :=
    IsModuleTopology.topologicalAddGroup ℝ _
  let := realification_moduleTopology_t2 E.basis
  obtain ⟨V, hfreq, ξ, hξ, hcommon, Hsource, _, hsourceW, hsource, _, hsourceDense,
      v, hv, hdep, hcorr, hnext⟩ := hdata
  obtain ⟨out', H', q', hsub, hH', hshort', hdense, hAq', hq'Z, R', ⟨D'⟩⟩ := hnext
  obtain ⟨F⟩ := hframe
  have hA : 0 ≤ A := hp.trans hpA
  obtain ⟨hcorrCost, htotal, hpair, hlower⟩ := hcost A hA hAZ
  have hmodel := B.has_correlated_affine_comparison D E T hpA hT F V (fun h => ξ * v h)
    (fun h => by rw [map_mul, hξ, hv h, one_mul]) D'
    hTfil hfreq hs (hA.trans hAq') hZ hAZ hq'Z hf
    Hsource hsource hsourceDense hsub hcorr ξ v (fun _ => rfl) hcommon hdep
    ((Real.exp_le_exp.mpr hcorrCost).trans hN)
  refine ⟨A, hpA, hAZ, out, H, q, P, hHW, hH, hshort, hpq, hqP, hPA,
    R, D, B, E, T, hT, hTfil, hcentral, ⟨F⟩, V, hfreq, ξ, hξ, hcommon,
    v, hv, hdep, out', H', q', (fun h hh => hsourceW (hsub hh)), hH', hshort',
    hdense, hAq', hq'Z, R', D', hmodel, htotal, hpair, hlower⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.DiagonalRowTransfer
namespace OAI

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff
  NativeSampleCorrelation.lie NativeSampleCorrelation.algebra
  NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd
  NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

theorem exists_quadratic_pair_orbit_factors :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ}, 0 ≤ p →
      Real.exp ((p + C) ^ C) ≤ (N : ℝ) →
      ∀ f : ZMod N → ℂ, (∀ x, ‖f x‖ ≤ 1) → Real.exp (-p) ≤ gowersNorm 3 f →
      ∃ q r : ℝ, 0 ≤ q ∧ q ≤ (p + C) ^ C ∧ 0 ≤ r ∧ r ≤ (p + C) ^ C ∧
        ∃ H : Finset (ZMod N), H.Nonempty ∧ Real.exp (-q) * N ≤ (H.card : ℝ) ∧
          ∃ M : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) q,
            ∃ i : Fin M.outputDim,
              (∀ h ∈ H, Real.exp (-q) ≤
                ‖𝔼 n : ZMod N, multiplicativeDerivative f h n *
                  star (M.evalCyclic N i (correlationInput h n))‖) ∧
              ∃ i' j' : Fin M.outputDim,
                ∃ V : NativeSampleCorrelation (fun _ : Fin 2 => 1) 1 r
                  Finset.univ (fun z : Fin 2 → ZMod N => fun k => ((z k).val : ℤ))
                  (fun z => M.antisymmetricKernel i' j' ((z 0).val : ℤ) ((z 1).val : ℤ)),
                  Nonempty (NativePolynomialOrbitFactors (pi V.antisymmetricPairModels)
                    V.antisymmetricPairPolynomial (piFrequency V.antisymmetricPairFrequencies)
                    (fun _ : Fin 2 => (N : ℝ)) ((p + C) ^ C)) := by
  obtain ⟨A, _, hdrop⟩ := exists_quadratic_pair_step_drop
  obtain ⟨B, _, horbit⟩ := exists_antisymmetric_pair_orbit_factors
  let X : Polynomial ℕ := Polynomial.X
  let T := (X + Polynomial.C A) ^ A
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (T + (3 * T + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro N _ p hp hN f hf hG
  let t := (p + A) ^ A
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hcost : t + (3 * t + B) ^ B ≤ (p + C) ^ C := by
    simpa [X, T, t, Polynomial.eval₂_pow] using hbudget p hp
  have htC : t ≤ (p + C) ^ C := (le_add_of_nonneg_right (by positivity)).trans hcost
  have hBC : (3 * t + B) ^ B ≤ (p + C) ^ C := (le_add_of_nonneg_left ht).trans hcost
  obtain ⟨q, r, hq, hqt, hr, hrt, H, hH, hdense, M, i, hderiv, i', j', V, ⟨F⟩⟩ :=
    hdrop hp ((Real.exp_le_exp.mpr htC).trans hN) f hf hG
  have hbound : (q + r + t + B) ^ B ≤ (p + C) ^ C := by
    apply le_trans _ hBC
    apply pow_le_pow_left₀ (by positivity)
    change q + r + t + B ≤ 3 * t + B
    linarith
  obtain ⟨R⟩ := horbit F ht ((Real.exp_le_exp.mpr hbound).trans hN)
  exact ⟨q, r, hq, hqt.trans htC, hr, hrt.trans htC, H, hH, hdense, M, i, hderiv, i', j', V,
    ⟨R.mono hbound (fun _ => by exact_mod_cast NeZero.pos N)⟩⟩

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_quadratic_global_exchange :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p e : ℝ}, 0 ≤ p → 0 ≤ e →
      Real.exp ((p + e + C) ^ C) ≤ (N : ℝ) →
      ∀ f : ZMod N → ℂ, (∀ x, ‖f x‖ ≤ 1) → Real.exp (-p) ≤ gowersNorm 3 f →
      ∃ q : ℝ, 0 ≤ q ∧ q ≤ (p + C) ^ C ∧
        ∃ H : Finset (ZMod N), H.Nonempty ∧ Real.exp (-q) * N ≤ (H.card : ℝ) ∧
          ∃ M : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) q,
            ∃ i : Fin M.outputDim,
              (∀ h ∈ H, Real.exp (-q) ≤
                ‖𝔼 n : ZMod N, multiplicativeDerivative f h n *
                  star (M.evalCyclic N i (correlationInput h n))‖) ∧
              ∃ G : Fin M.outputDim → Fin M.outputDim → (Fin 2 → ℤ) → ℂ,
                (∀ a b, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 1
                  ((p + e + C) ^ C) (G a b))) ∧
                (∀ a b (x : Fin 2 → ZMod N), ‖G a b (fun z => ((x z).val : ℤ))‖ ≤ 1) ∧
                (∀ a b, (𝔼 x : Fin 2 → ZMod N,
                  ‖M.antisymmetricKernel a b ((x 0).val : ℤ) ((x 1).val : ℤ) -
                    G a b (fun z => ((x z).val : ℤ))‖) ≤ Real.exp (-e)) := by
  obtain ⟨A, _, hpair⟩ := exists_quadratic_pair_orbit_factors
  obtain ⟨B, _, hcomparison⟩ := exists_precise_global_pair_comparison
  let X : Polynomial ℕ := Polynomial.X
  let T := (X + Polynomial.C A) ^ A
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (T + (3 * T + X + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro N _ p e hp he hN f hf hGowers
  let t := (p + e + A) ^ A
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hbase : (p + A) ^ A ≤ t := by
    apply pow_le_pow_left₀ (by positivity)
    linarith
  have hsum : t + (3 * t + (p + e) + B) ^ B ≤ (p + e + C) ^ C := by
    simpa [X, T, t, Polynomial.eval₂_pow] using hbudget (p + e) (add_nonneg hp he)
  have htC : t ≤ (p + e + C) ^ C :=
    (le_add_of_nonneg_right (by positivity)).trans hsum
  have hBC : (3 * t + (p + e) + B) ^ B ≤ (p + e + C) ^ C :=
    (le_add_of_nonneg_left ht).trans hsum
  have hbaseC : (p + A) ^ A ≤ (p + C) ^ C := by
    have hh : (p + A) ^ A + (3 * (p + A) ^ A + p + B) ^ B ≤ (p + C) ^ C := by
      simpa [X, T, Polynomial.eval₂_pow] using hbudget p hp
    exact (le_add_of_nonneg_right (by positivity)).trans hh
  obtain ⟨q, r, hq, hqt, hr, hrt, H, hH, hdense, M, i, hderiv, i', j', V, ⟨R⟩⟩ :=
    hpair hp ((Real.exp_le_exp.mpr (hbase.trans htC)).trans hN) f hf hGowers
  have hcost : (q + r + (p + A) ^ A + e + B) ^ B ≤ (p + e + C) ^ C := by
    apply le_trans _ hBC
    apply pow_le_pow_left₀ (by positivity)
    have hq' := hqt.trans hbase
    have hr' := hrt.trans hbase
    linarith
  obtain ⟨G, hG, hcap, herr⟩ := hcomparison R
    (by positivity : 0 ≤ (p + A) ^ A) he ((Real.exp_le_exp.mpr hcost).trans hN)
  refine ⟨q, hq, hqt.trans hbaseC, H, hH, hdense, M, i, hderiv, G, ?_, hcap, herr⟩
  intro a b
  exact ⟨(Classical.choice (hG a b)).mono hcost⟩

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

theorem exists_quadratic_original_integration :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p e : ℝ}, 0 ≤ p → 0 ≤ e →
      Real.exp ((p + e + C) ^ C) ≤ (N : ℝ) →
      ∀ f : ZMod N → ℂ, (∀ x, ‖f x‖ ≤ 1) → Real.exp (-p) ≤ gowersNorm 3 f →
      ∃ q : ℝ, 0 ≤ q ∧ q ≤ (p + C) ^ C ∧
        ∃ H : Finset (ZMod N), H.Nonempty ∧ Real.exp (-q) * N ≤ (H.card : ℝ) ∧
          ∃ M : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) q,
            ∃ i : Fin M.outputDim,
              (∀ h ∈ H, Real.exp (-q) ≤
                ‖𝔼 n : ZMod N, multiplicativeDerivative f h n *
                  star (M.evalCyclic N i (correlationInput h n))‖) ∧
              ∃ K : (Fin M.quadraticRoot.outputDim × Fin M.quadraticRoot.outputDim) →
                  Fin M.outputDim → Fin M.quadraticRoot.outputDim → (Fin 2 → ℤ) → ℂ,
                (∀ a j c, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 1
                  ((p + e + C) ^ C) (K a j c))) ∧
                (∀ a j c, (𝔼 x : Fin 2 → ZMod N,
                  ‖M.quadraticRoot.cyclicDiagonalDerivative a x *
                      (M.eval j (fun k => ((x k).val : ℤ)) *
                        M.quadraticRoot.eval c (fun _ => ((x 0).val : ℤ))) -
                    K a j c (fun k => ((x k).val : ℤ))‖) ≤ Real.exp (-e)) := by
  obtain ⟨A, _, hglobal⟩ := exists_quadratic_global_exchange
  obtain ⟨B, _, hroot⟩ := NativeMultidegreeNilcharacter.exists_rootCyclicCorrection_expansion
  obtain ⟨D, _, horiginal⟩ := NativeMultidegreeNilcharacter.exists_originalDiagonalCorrection_expansion
  let X : Polynomial ℕ := Polynomial.X
  let U := (X + Polynomial.C A) ^ A
  let T := (X + 12 * U + 40 + Polynomial.C A) ^ A
  let S := (U + T + X + 4 * U + 40 + Polynomial.C B) ^ B
  let R := (U + S + Polynomial.C D) ^ D
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (U + T + X + 4 * U + 40 + S + R)
  refine ⟨C, hC, ?_⟩
  intro N _ p e hp he hN f hf hGowers
  let v := p + e
  let u := (p + A) ^ A
  let umax := (v + A) ^ A
  let t := (p + (e + 12 * u + 40) + A) ^ A
  let tmax := (v + 12 * umax + 40 + A) ^ A
  let b := e + 4 * u + 40
  let smax := (umax + tmax + v + 4 * umax + 40 + B) ^ B
  let rmax := (umax + smax + D) ^ D
  let δ : ℝ≥0 := ⟨Real.exp (-b), (Real.exp_pos _).le⟩
  have hδval : (δ : ℝ) = Real.exp (-b) := rfl
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have humax : 0 ≤ umax := by dsimp [umax]; positivity
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have htmax : 0 ≤ tmax := by dsimp [tmax]; positivity
  have hsmax : 0 ≤ smax := by dsimp [smax]; positivity
  have hrmax : 0 ≤ rmax := by dsimp [rmax]; positivity
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hδ : 0 < δ := Real.exp_pos _
  have hinv : (δ : ℝ)⁻¹ ≤ Real.exp b := by rw [hδval, ← Real.exp_neg, neg_neg]
  have hsum : umax + tmax + v + 4 * umax + 40 + smax + rmax ≤ (p + e + C) ^ C := by
    simpa [X, U, T, S, R, umax, tmax, smax, rmax, v, Polynomial.eval₂_pow] using hbudget v hv
  have hum : u ≤ umax := by
    apply pow_le_pow_left₀ (by positivity)
    dsimp [v]
    linarith
  have htm : t ≤ tmax := by
    apply pow_le_pow_left₀ (by positivity)
    dsimp [v]
    linarith
  have htC : tmax ≤ (p + e + C) ^ C := by linarith
  have hsC : smax ≤ (p + e + C) ^ C := by linarith
  have hrC : rmax ≤ (p + e + C) ^ C := by linarith
  have hbC : b ≤ (p + e + C) ^ C := by dsimp [b, v] at *; linarith
  have huC : u ≤ (p + C) ^ C := by
    have hh : u + (p + 12 * u + 40 + A) ^ A + p + 4 * u + 40 +
        (u + (p + 12 * u + 40 + A) ^ A + p + 4 * u + 40 + B) ^ B +
        (u + (u + (p + 12 * u + 40 + A) ^ A + p + 4 * u + 40 + B) ^ B + D) ^ D ≤ (p + C) ^ C := by
      simpa [X, U, T, S, R, u, Polynomial.eval₂_pow] using hbudget p hp
    have h1 : 0 ≤ (p + 12 * u + 40 + A) ^ A := by positivity
    have h2 : 0 ≤ (u + (p + 12 * u + 40 + A) ^ A + p + 4 * u + 40 + B) ^ B := by positivity
    have h3 : 0 ≤ (u + (u + (p + 12 * u + 40 + A) ^ A + p + 4 * u + 40 + B) ^ B + D) ^ D := by positivity
    linarith
  obtain ⟨q, hq, hqu, H, hH, hdense, M, i, hderiv, G, hG, hcap, herr⟩ :=
    hglobal hp (by positivity : 0 ≤ e + 12 * u + 40)
      ((Real.exp_le_exp.mpr (htm.trans htC)).trans hN) f hf hGowers
  have hqmax := hqu.trans hum
  have hs : (q + t + b + B) ^ B ≤ smax := by
    apply pow_le_pow_left₀ (by positivity)
    dsimp [b, v]
    linarith
  have hF (a c) : Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 1 smax
      (M.rootCyclicCorrection N δ G a c)) :=
    ⟨(Classical.choice (hroot M N δ hδ ht hb hinv G hG a c)).mono hs⟩
  have hfinal : (q + smax + D) ^ D ≤ (p + e + C) ^ C := by
    apply le_trans _ hrC
    apply pow_le_pow_left₀ (by positivity)
    linarith
  have herror := quadratic_original_error_bound (Nat.cast_nonneg M.outputDim) hu
    (M.output_bound.trans (Real.exp_le_exp.mpr hqu)) ((Real.exp_le_exp.mpr hbC).trans hN)
  have hrootError := M.rootCyclicCorrection_mean_error δ hδ G hcap herr
  refine ⟨q, hq, hqu.trans huC, H, hH, hdense, M, i, hderiv,
    M.originalDiagonalCorrection (M.rootCyclicCorrection N δ G), ?_, ?_⟩
  · intro a j c
    exact ⟨(Classical.choice (horiginal M hsmax (M.rootCyclicCorrection N δ G) hF a j c)).mono hfinal⟩
  · intro a j c
    apply (M.originalDiagonalCorrection_mean_error (M.rootCyclicCorrection N δ G) hrootError a j c).trans
    have hdim : M.quadraticRoot.outputDim = M.outputDim ^ 2 := rfl
    simp only [hdim, Nat.cast_pow, hδval]
    dsimp [b] at *
    simpa only [← pow_mul, Nat.reduceMul] using herror

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.HigherResidualRowDifferences
namespace OAI

section

namespace Erdos3

open scoped BigOperators TensorProduct

attribute [local instance] NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff
  NativeCyclicModel.lie NativeCyclicModel.algebra NativeCyclicModel.topology
  NativeCyclicModel.topologicalAdd NativeCyclicModel.continuousSMul NativeCyclicModel.hausdorff

theorem exists_quadratic_primitive_correlation_large_modulus :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ}, 0 ≤ p →
      Real.exp ((p + C) ^ C) ≤ (N : ℝ) →
      ∀ f : ZMod N → ℂ, (∀ x, ‖f x‖ ≤ 1) → Real.exp (-p) ≤ gowersNorm 3 f →
      ∃ g ∈ nativeCyclicFunctions 2 N ((p + C) ^ C),
        Real.exp (-((p + C) ^ C)) ≤ ‖𝔼 n, f n * star (g n)‖ := by
  obtain ⟨A, _, hintegrate⟩ := exists_quadratic_original_integration
  obtain ⟨B, _, hfourier⟩ := exists_fourier_of_stepOne_cross_correlation
  obtain ⟨D, _, hprimitive⟩ :=
    NativeMultidegreeNilcharacter.exists_quadratic_primitive_niltest_budget
  let X : Polynomial ℕ := Polynomial.X
  let U := (X + Polynomial.C A) ^ A
  let R := 3 * (U + 1)
  let E := 2 * U + 3 * R + 4
  let T := (X + E + Polynomial.C A) ^ A
  let V := 2 * U + 2 + 3 * R + T
  let F := (V + Polynomial.C B) ^ B
  let G := (R + Polynomial.C D) ^ D
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (U + R + E + T + V + F + G)
  refine ⟨C, hC, ?_⟩
  intro N _ p hp hN f hf hGowers
  let u := (p + A) ^ A
  let r := 3 * (u + 1)
  let e := 2 * u + 3 * r + 4
  let t := (p + e + A) ^ A
  let v := 2 * u + 2 + 3 * r + t
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have he : 0 ≤ e := by dsimp [e]; positivity
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have hsum : u + r + e + t + v + (v + B) ^ B + (r + D) ^ D ≤ (p + C) ^ C := by
    simpa [X, U, R, E, T, V, F, G, u, r, e, t, v, Polynomial.eval₂_pow] using hbudget p hp
  have hF : 0 ≤ (v + B) ^ B := by positivity
  have hG : 0 ≤ (r + D) ^ D := by positivity
  have htC : t ≤ (p + C) ^ C := by linarith
  have hFC : (v + B) ^ B ≤ (p + C) ^ C := by linarith
  have hGC : (r + D) ^ D ≤ (p + C) ^ C := by linarith
  obtain ⟨q, hq, hqu, H, _hH, hdense, M, i, hderiv, K, hK, herr⟩ :=
    hintegrate hp he ((Real.exp_le_exp.mpr htC).trans hN) f hf hGowers
  let W := M.quadraticRoot
  have hroot : tensorPowerBudget 2 q ≤ r := by
    norm_num only [tensorPowerBudget, Nat.cast_ofNat, show (2 : ℝ) + 1 = 3 by norm_num]
    dsimp only [r]
    linarith
  have hroot0 : 0 ≤ tensorPowerBudget 2 q := by
    unfold tensorPowerBudget
    positivity
  have hdim : (W.outputDim : ℝ) ≤ Real.exp r :=
    W.output_bound.trans (Real.exp_le_exp.mpr hroot)
  have hdim3 : (W.outputDim : ℝ) ^ 3 ≤ Real.exp (3 * r) := by
    calc
      _ ≤ Real.exp r ^ 3 := pow_le_pow_left₀ (Nat.cast_nonneg _) hdim 3
      _ = _ := by rw [← Real.exp_nat_mul]; norm_num
  let J := (Fin W.outputDim × Fin W.outputDim) × Fin W.outputDim
  let z (ac : J) := 𝔼 h : ZMod N, ‖𝔼 n : ZMod N,
    multiplicativeDerivative f h n * W.cyclicDiagonalDerivative ac.1 ![h, n] *
      star (K ac.1 i ac.2 ![(h.val : ℤ), (n.val : ℤ)])‖
  have hcard : (Fintype.card J : ℝ) ≤ Real.exp (3 * r) := by
    have hcount : (Fintype.card J : ℝ) = (W.outputDim : ℝ) ^ 3 := by
      simp only [J, Fintype.card_prod, Fintype.card_fin, Nat.cast_mul]
      ring
    rw [hcount]
    exact hdim3
  have hmass : Real.exp (-(2 * u)) ≤ 𝔼 h : ZMod N,
      ‖𝔼 n : ZMod N, multiplicativeDerivative f h n *
        star (M.evalCyclic N i (correlationInput h n))‖ := by
    have hh := dense_set_mean_lower_bound H
      (fun h : ZMod N => ‖𝔼 n : ZMod N, multiplicativeDerivative f h n *
        star (M.evalCyclic N i (correlationInput h n))‖)
      (fun _ => norm_nonneg _) (Real.exp_nonneg (-q))
      (by simpa only [ZMod.card] using hdense) hderiv
    have heq : Real.exp (-q) * Real.exp (-q) = Real.exp (-(2 * q)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [heq] at hh
    exact (Real.exp_le_exp.mpr (by dsimp [u]; linarith)).trans hh
  have htransfer := M.original_diagonal_row_correlation_bound i f hf
    (fun a c => K a i c) (fun a c => herr a i c)
  change _ ≤ (∑ ac : J, z ac) + (W.outputDim : ℝ) ^ 3 * Real.exp (-e) at htransfer
  let δ := Real.exp (-(2 * u + 2))
  have hδ : 0 < δ := Real.exp_pos _
  have herror : (W.outputDim : ℝ) ^ 3 * Real.exp (-e) ≤ δ := by
    calc
      _ ≤ Real.exp (3 * r) * Real.exp (-e) :=
        mul_le_mul_of_nonneg_right hdim3 (Real.exp_nonneg _)
      _ = Real.exp (-(2 * u + 4)) := by rw [← Real.exp_add]; congr 1; dsimp [e]; ring
      _ ≤ δ := Real.exp_le_exp.mpr (by linarith)
  have htwo : 2 * δ ≤ Real.exp (-(2 * u)) := by
    calc
      _ ≤ Real.exp 2 * δ := mul_le_mul_of_nonneg_right
        (by linarith [Real.add_one_le_exp (2 : ℝ)]) hδ.le
      _ = _ := by dsimp [δ]; rw [← Real.exp_add]; congr 1; ring
  have hmass' : δ ≤ ∑ ac : J, z ac := by linarith
  obtain ⟨ac, hac⟩ := exists_large_nonnegative_weighted_term (fun _ : J => (1 : ℝ)) z
    (fun _ => by norm_num) (fun _ => Finset.expect_nonneg (fun _ _ => norm_nonneg _))
    hδ (Real.exp_pos _) (by simpa using hcard) (by simpa only [one_mul] using hmass')
  have hac' : Real.exp (-(2 * u + 2 + 3 * r)) ≤ z ac := by
    have heq : δ / Real.exp (3 * r) = Real.exp (-(2 * u + 2 + 3 * r)) := by
      dsimp [δ]
      rw [← Real.exp_sub]
      congr 1
      ring
    rwa [heq] at hac
  let expansion := Classical.choice (hK ac.1 i ac.2)
  obtain ⟨j, hj⟩ := expansion.select_mean_row_correlation
    (fun h n : ZMod N => ![(h.val : ℤ), (n.val : ℤ)])
    (fun h n : ZMod N => multiplicativeDerivative f h n *
      W.cyclicDiagonalDerivative ac.1 ![h, n]) (Real.exp_pos _) hac'
  let f₀ (n : ZMod N) := f n * W.eval ac.1.1 (fun _ => (n.val : ℤ))
  let f₁ (n : ZMod N) := f n * W.eval ac.1.2 (fun _ => (n.val : ℤ))
  have hf₀ (n : ZMod N) : ‖f₀ n‖ ≤ 1 := by
    dsimp only [f₀]
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hf n)).trans (W.norm_eval _ _)
  have hf₁ (n : ZMod N) : ‖f₁ n‖ ≤ 1 := by
    dsimp only [f₁]
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hf n)).trans (W.norm_eval _ _)
  have hid (h n : ZMod N) :
      multiplicativeDerivative f h n * W.cyclicDiagonalDerivative ac.1 ![h, n] =
        f₀ n * star (f₁ (n + h)) := by
    simp only [multiplicativeDerivative, NativeMultidegreeNilcharacter.cyclicDiagonalDerivative,
      Matrix.cons_val_zero, Matrix.cons_val_one, f₀, f₁, star_mul]
    rw [add_comm h n]
    ring
  have htest : Real.exp (-v) ≤ 𝔼 h : ZMod N,
      ‖𝔼 n : ZMod N, f₀ n * star (f₁ (n + h)) *
        star ((expansion.test j).eval ![(h.val : ℤ), (n.val : ℤ)])‖ := by
    have heq : Real.exp (-(2 * u + 2 + 3 * r)) / Real.exp t = Real.exp (-v) := by
      rw [← Real.exp_sub]
      congr 1
      dsimp [v]
      ring
    change Real.exp (-(2 * u + 2 + 3 * r)) / Real.exp t ≤ _ at hj
    simpa only [heq, hid] using hj
  obtain ⟨χ, hχ⟩ := hfourier (expansion.model j) hv (expansion.test j)
    ((expansion.complexity j).mono (by dsimp [v]; linarith)) f₀ f₁ hf₀ hf₁ htest
  let g (n : ZMod N) := star (W.eval ac.1.2 (fun _ => (n.val : ℤ))) * χ n
  have hg : g ∈ nativeCyclicFunctions 2 N ((p + C) ^ C) := by
    obtain ⟨model⟩ := hprimitive hroot0 W ac.1.2 χ
    have hcost : (tensorPowerBudget 2 q + D) ^ D ≤ (p + C) ^ C :=
      (pow_le_pow_left₀ (by positivity) (add_le_add hroot le_rfl) D).trans hGC
    exact ⟨{ model with complexity := model.complexity.mono hcost }⟩
  refine ⟨g, hg, (Real.exp_le_exp.mpr (neg_le_neg hFC)).trans ?_⟩
  have heq : finiteFourierCoeff f₁ χ = 𝔼 n, f n * star (g n) := by
    unfold finiteFourierCoeff
    apply Finset.expect_congr rfl
    intro n _
    simp only [f₁, g, star_mul, star_star]
    ring
  rwa [heq] at hχ

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators TensorProduct

attribute [local instance] NativeCyclicModel.lie NativeCyclicModel.algebra
  NativeCyclicModel.topology NativeCyclicModel.topologicalAdd
  NativeCyclicModel.continuousSMul NativeCyclicModel.hausdorff

theorem exists_cyclicNativeInverse_two : ∃ C : ℕ, 2 ≤ C ∧ CyclicNativeInverse 2 C := by
  obtain ⟨A, _, hlarge⟩ := exists_quadratic_primitive_correlation_large_modulus
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((X + Polynomial.C A) ^ A + 8 * X + 211)
  refine ⟨C, hC, ?_⟩
  intro N _ p hp f hf hGowers
  have hp0 : 0 ≤ p := by linarith
  let u := (p + A) ^ A
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hsum : u + 8 * p + 211 ≤ (p + C) ^ C := by
    simpa [X, u, Polynomial.eval₂_pow] using hbudget p hp0
  have huC : u ≤ (p + C) ^ C := by linarith
  by_cases hN : Real.exp u ≤ (N : ℝ)
  · obtain ⟨g, ⟨model⟩, hcorr⟩ := hlarge hp0 hN f hf hGowers
    exact ⟨g, ⟨{ model with complexity := model.complexity.mono huC }⟩,
      (Real.exp_le_exp.mpr (neg_le_neg huC)).trans hcorr⟩
  · obtain ⟨g, ⟨model⟩, hcorr⟩ :=
      exists_quadratic_small_modulus_correlation (not_le.mp hN).le f hf hGowers
    have h211 : (211 : ℝ) ≤ (p + C) ^ C := by linarith
    have hc : 8 * p + u ≤ (p + C) ^ C := by linarith
    exact ⟨g, ⟨{ model with complexity := model.complexity.mono h211 }⟩,
      (Real.exp_le_exp.mpr (neg_le_neg hc)).trans hcorr⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AllocatedExternalCandidatePhysicalScore
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I E J : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type*} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    (A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center)

variable {L M : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {r d t : ℕ}
    (D : RationalFilteredNilmanifold L r d) (Fmark : NilpotentLieFiltration M t)
    (φ : L →ₗ⁅ℚ⁆ M)
    (marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J))
    (observable : (X → ℤ) → D.Space → ℂ) (weight : (X → ℤ) → ℂ)

namespace AllocatedExternalCandidateProblem
variable {A D Fmark φ marked observable weight cost massThreshold scoreThreshold}
    (P : AllocatedExternalCandidateProblem (E := E) A D Fmark φ marked observable weight
      cost massThreshold scoreThreshold)

noncomputable def ambientPhysicalValue
    (ambient : D.filtration.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J))
    (x : X → ℤ) : D.Space :=
  QuotientGroup.mk (D.filtration.realification.polynomialOrbitEval
    (fullTaggedVariableWeight J) (P.physicalIntegerPoint x) ambient)

end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.AllocatedExternalCandidateResetSuccessor
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct

attribute [local irreducible] weightedAdaptedRealChartHom realPolynomialSymbolHom
  realChartSubstitute realPolynomialGroupMap associatedGradedMap gradedRefiltrationMap

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I E J : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type*} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    {A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center}
    {L M κ : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s d f : ℕ} {D : RationalFilteredNilmanifold L (s + 1) d}
    (Fmark : RationalFilteredNilmanifold M (s + 1) f)
    (φ : L →ₗ⁅ℚ⁆ M)
    (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ Fmark.filtration.layer j)
    {marked : Fmark.filtration.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}
    {cost massThreshold scoreThreshold : ℝ}
    (P : AllocatedExternalCandidateProblem (E := E) A D Fmark.filtration φ marked
      observable weight cost massThreshold scoreThreshold)
    (keep : LayerSamplerVariables G I n B → Prop)
    (hkeep : ∀ z : P.productive, (P.chart z).keep = keep)
    (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
    {c : Basis κ ℚ M} {ν : κ → ℕ}
    {hF : ∀ j, Fmark.filtration.layer j = span ℚ (c '' {i | j ≤ ν i})}
    {g : (Fmark.filtration.realification.adaptedPolynomialFiltration
      (fullTaggedVariableWeight (X := X) J)).Group}
    {EF RF : Fmark.filtration.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J)}
    (factors : GlobalMarkedNativeFactors Fmark.filtration c ν hF (fullTaggedVariableWeight J)
      (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ)) g EF RF)
    (slow : ℝ) (denominator : ℕ)

namespace AllocatedExternalGlobalNativeResetFamily

variable {Fmark φ hφ P keep hkeep W factors slow denominator}

noncomputable def rightMark
    (_reset : AllocatedExternalGlobalNativeResetFamily Fmark φ hφ P keep hkeep W factors slow denominator) :
    Fmark.filtration.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J) :=
  (Fmark.filtration.realification.polynomialOrbitCoordinates (fullTaggedVariableWeight J)).symm factors.right

variable (reset : AllocatedExternalGlobalNativeResetFamily
    Fmark φ hφ P keep hkeep W factors slow denominator)

theorem right_mark_values (z : (P.withKeep keep hkeep).productive) (u : {i // keep i} → ℤ) :
    Fmark.filtration.adaptedPolynomialRealValueHom (fun _ : {i // keep i} => 1)
      (fun i => (u i : ℝ))
      (Fmark.filtration.weightedAdaptedRealChartHom (fullTaggedVariableWeight J)
        (fun _ : {i // keep i} => 1)
        (integerSampledRealChart ((P.withKeep keep hkeep).chart z).integerChart)
        ((P.withKeep keep hkeep).chart z).integerChart_support factors.right) =
      Fmark.filtration.realification.polynomialOrbitRealEval (fullTaggedVariableWeight J)
        (fun i => (((P.withKeep keep hkeep).chart z).chartValues u i : ℝ)) reset.rightMark :=
  ((P.withKeep keep hkeep).chart z).globalOrbit_chart_values Fmark.filtration factors.right u

end AllocatedExternalGlobalNativeResetFamily
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ForecastLawPhysicalAmbientHaarComparison
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G : Type*} {X : Type} [Fintype G] [Fintype X] [DecidableEq X]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

variable (density : (((Σ _ : X, Unit ⊕ Empty) → ℝ) ×
  ((Σ _a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, Unit) → ℝ)) → ℝ)
variable {A : Type*} (selected : A → Σ j : Fin m, Fin (n j))
variable (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
variable (x : G → IntegerScalarCubeBox Empty S.value)
variable {Ω : Type*} [Fintype Ω] {Eout : Fin m → Type*} [∀ j, Fintype (Eout j)]
variable (active : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S) → FiniteProbabilityWeights Ω)
variable (Y : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S) → Ω →
  Sigma (AllocatedCongruenceRankOutput X Eout (allocatedShortAxis (I := I) U basis S.value)) → ℤ)
variable (N : ℕ) [NeZero N] (volume : ℝ)
variable (base : X → ℤ) (physicalN : X → ℕ) (τ : ℝ)

variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (hb : ∀ j, Submodule.span ℤ (Set.range (basis j)) =
  projectedIntegerLattice (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]

variable [hcompact : CompactSpace (EuclideanJetLayers U (fun _ : Fin m => Unit))]

noncomputable def nativeForecastAmbientExponent (m : ℕ) : ℕ :=
  Classical.choose (exists_nativeForecast_ambient_comparison m)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedCenteredModelMarginalData
namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct

noncomputable def preparedCenteredMarginalExponent (m : ℕ) : ℕ :=
  (exists_allocated_centered_narrow_prescribed_marginal.{0, 0, 0, 0, 0, 0} m).choose

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedRelativeFinalPower
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical NNReal

theorem exists_relative_finite_returned_fiber_normalization (s : ℕ) :
    ∃ E : ℕ, 2 ≤ E ∧ ∀ {Ω X : Type*}
      [Fintype Ω] [Nonempty Ω] [Fintype X] [DecidableEq X]
      (outer : FiniteProbabilityWeights Ω) (productive : Finset Ω),
      0 < outer.mass productive →
      ∀ (N : X → ℕ) (keep : X → Prop) [DecidablePred keep],
      (∀ i, 0 < N i) → ∀ (p : ℝ), 0 ≤ p →
      ∀ (target : ℝ), target ∈ Set.Icc (0 : ℝ) 1 →
      ∀ (rankBound : ℕ) (f : Ω → (X → ℤ) → ℝ),
      (∀ h x, x ∈ integerBox N → f h x ∈ Set.Icc (0 : ℝ) 1) →
      (∀ h ∈ productive, ∃ (fixed : {i // ¬keep i} → ℤ),
        (∀ i, 0 ≤ fixed i ∧ fixed i < (N i.val : ℤ)) ∧
        RelativePatchSliceConclusion s (fun i : {i // keep i} => N i.val)
          (fun u => f h (finiteSplitPoint keep u fixed)) target rankBound p) →
      let q := p + (Fintype.card X : ℝ) + 2
      let D := min rankBound ⌊p⌋₊
      ∃ (localLaw : Ω → FiniteProbabilityWeights (integerBox N))
        (d : ℕ) (w : Fin d → ℕ) (hw : Monotone w) (Ψ : PatchKernel d)
        (B : PolynomialSlots X d w) (localForm : Ω → PolynomialSlots X d w)
        (retained : Finset Ω),
        d ≤ D ∧ d ≤ rankBound ∧ (∀ i, 1 ≤ w i) ∧ (∀ i, w i ≤ s) ∧
        (Ψ.lip : ℝ) ≤ Real.exp ((q + 2) ^ E) ∧
        (∀ i, realPolynomialMass (B.center i) ≤ (q + 2) ^ E) ∧
        retained ⊆ productive ∧
        (outer.mass productive / ((D + 1) * (s + 1) ^ D : ℕ)) *
          Real.exp (-((q + 2) ^ E)) ≤ outer.mass retained ∧
        (∀ h ∈ retained, RelativeReturnedFiberLaw keep N p (localLaw h)) ∧
        ∀ h ∈ retained, Real.exp (-((q + 2) ^ E)) ≤ (localLaw h).mean
          (fun t => (f h t.val - target) * (B.shearTransformedSlots hw
            ((localForm h).loweringAt (fun i => (t.val i : ℝ)))).patchValue Ψ) := by
  obtain ⟨E, hE, hnormalize⟩ := exists_varying_rank_fixed_patch_function s
  refine ⟨E, hE, ?_⟩
  intro Ω X _ _ _ _ outer productive hmass N keep _ hN p hp target ht
    rankBound f hf hreturn q D
  have hdata (h : Ω) (hh : h ∈ productive) :
      ∃ (d : ℕ) (Q : PolynomialPatch X s d)
        (law : FiniteProbabilityWeights (integerBox N)),
        d ≤ D ∧ (Q.kernel.lip : ℝ) ≤ Real.exp p ∧
        Real.exp (-p) ≤ law.mean
          (fun x => (f h x.val - target) * Q.value (fun i => (x.val i : ℝ))) ∧
        RelativeReturnedFiberLaw keep N p law := by
    obtain ⟨fixed, hfixed, hslice⟩ := hreturn h hh
    obtain ⟨d, Q, law, hd, _, hlip, hscore, r, hr, S, hlen, hlength, hlaw⟩ :=
      hslice.tighten_rank.exists_fiber_law_with_slice fixed hfixed (fun i => hN i.val)
    exact ⟨d, Q, law, hd, hlip, hscore, fixed, hfixed, r, hr, S, hlen, hlength, hlaw⟩
  have hne : productive.Nonempty := Finset.nonempty_iff_ne_empty.mpr (by
    intro he
    simp only [he, FiniteProbabilityWeights.mass, Finset.sum_empty] at hmass
    linarith)
  obtain ⟨h₀, hh₀⟩ := hne
  obtain ⟨ddefault, Qdefault, lawdefault, hddefault, hlipdefault, _, _⟩ := hdata h₀ hh₀
  have hall (h : Ω) : ∃ (d : ℕ) (Q : PolynomialPatch X s d)
      (law : FiniteProbabilityWeights (integerBox N)),
      d ≤ D ∧ (Q.kernel.lip : ℝ) ≤ Real.exp p ∧
      (h ∈ productive → Real.exp (-p) ≤ law.mean
        (fun x => (f h x.val - target) * Q.value (fun i => (x.val i : ℝ)))) ∧
      (h ∈ productive → RelativeReturnedFiberLaw keep N p law) := by
    by_cases hh : h ∈ productive
    · obtain ⟨d, Q, law, hd, hlip, hscore, hslice⟩ := hdata h hh
      exact ⟨d, Q, law, hd, hlip, fun _ => hscore, fun _ => hslice⟩
    · exact ⟨ddefault, Qdefault, lawdefault, hddefault, hlipdefault,
        fun hmem => (hh hmem).elim, fun hmem => (hh hmem).elim⟩
  choose d patch localLaw hd hlip hpositive hslice using hall
  have hpq : p ≤ q := by dsimp only [q]; linarith [Nat.cast_nonneg (α := ℝ) (Fintype.card X)]
  have hq : 0 ≤ q := hp.trans hpq
  have hD : (D : ℝ) ≤ q :=
    (Nat.cast_le.mpr (Nat.min_le_right rankBound ⌊p⌋₊)).trans ((Nat.floor_le hp).trans hpq)
  have hX : (Fintype.card X : ℝ) ≤ q := by dsimp only [q]; linarith
  let point := fun (_ : Ω) (x : integerBox N) => x.val
  let score := fun h (x : integerBox N) => f h x.val - target
  have hscore (h) (x : integerBox N) : |score h x| ≤ 1 := by
    dsimp only [score]
    obtain ⟨hf0, hf1⟩ := hf h x.val x.property
    exact abs_le.mpr ⟨by linarith [ht.2], by linarith [ht.1]⟩
  obtain ⟨d', w, hw, Ψ, B, localForm, retained, hd', hpos, hws, hΨ, hB,
      hsub, hmass', hlocal⟩ :=
    hnormalize outer productive d patch D q hd hmass hq hD hX
      (fun h => (hlip h).trans (Real.exp_le_exp.mpr hpq)) localLaw point score hscore
      (fun h hh => (Real.exp_le_exp.mpr (neg_le_neg hpq)).trans (hpositive h hh))
  exact ⟨localLaw, d', w, hw, Ψ, B, localForm, retained, hd',
    hd'.trans (Nat.min_le_left _ _), hpos, hws, hΨ, hB, hsub, hmass',
    fun h hh => hslice h (hsub hh), hlocal⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.UnconditionedArbitraryFixedPatchFamily
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct

variable {m : ℕ} {G X : Type} [Fintype G] [Fintype X]
    {I E J : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    {A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center}

def AllocatedNormalizedCandidateConclusion
    (s : ℕ) (keep : LayerSamplerVariables G I n B → Prop)
    (centerLift : ∀ j, U j) (productive : Finset A.Path)
    (childCost cost : ℝ) (rankBound : ℕ) (f : (X → ℤ) → ℝ) (target : ℝ) : Prop :=
    let normalizationPower := (exists_relative_finite_returned_fiber_normalization.{0,0} s).choose
    let q := childCost + (Fintype.card (LayerSamplerVariables G I n B) : ℝ) + 2
    let D := min rankBound ⌊childCost⌋₊
    let normalizedBudget := (q + 2) ^ normalizationPower
    let retainedMass := (A.law.mass productive / ((D + 1) * (s + 1) ^ D : ℕ)) *
      Real.exp (-normalizedBudget)
    ∃ (d : ℕ) (patch : PolynomialPatch (LayerSamplerVariables G I n B) s d),
      d ≤ D ∧ d ≤ rankBound ∧
      (patch.kernel.lip : ℝ) ≤ Real.exp normalizedBudget ∧
      (∀ i, realPolynomialMass (patch.form.center i) ≤ normalizedBudget) ∧
      let := polynomialShearIndexFintype patch.weight (fun i => patch.weight_pos i)
      ∃ P : AllocatedExternalCandidateProblem (E := E) A
        (polynomialShearNilmanifold patch.weight s patch.weight_le)
        (RationalTorus.trivialFiltration s) 0 1
        (fun _ y => (patch.shearObservable y : ℂ))
        (fun x => ((f x - target : ℝ) : ℂ)) cost retainedMass (Real.exp (-normalizedBudget)),
        P.productive ⊆ productive ∧ P.centerLift = centerLift ∧
          ∀ z, (P.chart z).keep = keep

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.AllocatedZeroLayerDegreeScalarConclusion
namespace OAI

section

namespace Erdos3

open scoped NNReal TensorProduct Classical

theorem exists_polynomialPatch_external_observable_budget (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {V : Type*} {d : ℕ} (P : PolynomialPatch V s d)
      [Fintype (PolynomialShearIndex P.weight)]
      [TopologicalSpace (ℝ ⊗[ℚ] PolynomialShearLieAlgebra P.weight ℚ)]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] PolynomialShearLieAlgebra P.weight ℚ)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] PolynomialShearLieAlgebra P.weight ℚ)]
      [T2Space (ℝ ⊗[ℚ] PolynomialShearLieAlgebra P.weight ℚ)]
      (p : ℝ) (hp : 0 ≤ p), (d : ℝ) ≤ p →
      (∀ i, realPolynomialMass (P.form.center i) ≤ p) →
      (P.kernel.lip : ℝ) ≤ Real.exp p →
      P.ExternalObservableRegularity ⟨p, hp⟩ ((p + 2) ^ C) := by
  obtain ⟨C, hC, hbudget⟩ := exists_mass_bounded_patch_niltest_budget s
  refine ⟨C, hC, ?_⟩
  intro V d P _ _ _ _ _ p hp hd hcenters hLip
  let M : ℝ≥0 := ⟨p, hp⟩
  have hM : ∀ i, realPolynomialMass (P.form.center i) ≤ M := hcenters
  exact P.externalObservableRegularity_of_niltest_complexity M hM
    (hbudget P M hM p hp hd le_rfl hLip)

end Erdos3

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct NNReal

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I E J : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type*} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    (A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center)

namespace AllocatedExternalCandidateSampler

theorem degreeGlobalizationAt_zero (weight : (X → ℤ) → ℂ)
    (netExponent : ℕ) (p : ℝ) : A.DegreeGlobalizationAt (E := E) weight 0 netExponent p p := by
  intro L M _ _ _ _ _ _ _ _ d f D Fmark φ hφ hsurj hD hF hmap
    marked observable ℓ hℓ hLip hpositive hnet hweight P
  exact P.conclusion_stepZero A D Fmark.filtration φ marked observable weight

theorem DegreeGlobalizationAt.mono_output
    {weight : (X → ℤ) → ℂ} {degree netExponent : ℕ} {p outputCost largerCost : ℝ}
    (rule : A.DegreeGlobalizationAt (E := E) weight degree netExponent p outputCost)
    (hcost : outputCost ≤ largerCost) :
    A.DegreeGlobalizationAt (E := E) weight degree netExponent p largerCost := by
  intro L M _ _ _ _ _ _ _ _ d f D Fmark φ hφ hsurj hD hF hmap
    marked observable ℓ hℓ hLip hpositive hnet hweight P
  obtain ⟨out⟩ := rule D Fmark φ hφ hsurj hD hF hmap marked observable ℓ
    hℓ hLip hpositive hnet hweight P
  exact ⟨out.mono hcost (Real.exp_le_exp.mpr (neg_le_neg hcost))
    (Real.exp_le_exp.mpr (neg_le_neg hcost))⟩

end AllocatedExternalCandidateSampler
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct NNReal

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I E J : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type*} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    (A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center)

namespace AllocatedExternalCandidateSampler

theorem DegreeGlobalizationAt.mono_input
    {weight : (X → ℤ) → ℂ} {degree netExponent : ℕ} {p q outputCost : ℝ}
    (rule : A.DegreeGlobalizationAt (E := E) weight degree netExponent q outputCost)
    (hp : 0 ≤ p) (hpq : p ≤ q) :
    A.DegreeGlobalizationAt (E := E) weight degree netExponent p outputCost := by
  intro L M _ _ _ _ _ _ _ _ d f D Fmark φ hφ hsurj hD hF hmap
    marked observable ℓ hℓ hLip hpositive hnet hweight P
  have hexp : Real.exp p ≤ Real.exp q := Real.exp_le_exp.mpr hpq
  have hneg : Real.exp (-q) ≤ Real.exp (-p) := Real.exp_le_exp.mpr (neg_le_neg hpq)
  let ref := P.budgetRefinement hpq hneg hneg
  have hnet' : ∀ η : ℝ, 0 < η → η ≤ 1 → ∃ n : ℕ,
      (n : ℝ) ≤ Real.exp ((q + Real.log (1 / η) + netExponent) ^ netExponent) ∧
      ∃ oc : Fin n → {x : X → ℤ // x ∈ integerBox N},
        ∀ x ∈ integerBox N, ∃ i, ∀ y, ‖observable x y - observable (oc i).val y‖ ≤ η := by
    intro η hη hηone
    obtain ⟨n, hn, oc, hoc⟩ := hnet η hη hηone
    have hlog : 0 ≤ Real.log (1 / η) := Real.log_nonneg ((one_le_div hη).mpr hηone)
    refine ⟨n, hn.trans (Real.exp_le_exp.mpr ?_), oc, hoc⟩
    exact pow_le_pow_left₀ (by positivity) (by linarith only [hpq]) netExponent
  obtain ⟨out⟩ := rule D Fmark φ hφ hsurj
    (RationalFilteredNilmanifold.GeometryComplexityLE.mono D hD hpq)
    (RationalFilteredNilmanifold.GeometryComplexityLE.mono Fmark hF hpq)
    (fun i j => (hmap i j).trans hpq) marked observable ℓ (hℓ.trans hexp)
    hLip hpositive hnet' (fun x => (hweight x).trans hexp) ref.problem
  exact ⟨ref.conclusion out⟩

end AllocatedExternalCandidateSampler
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct NNReal

variable {m : ℕ} {G X : Type} [Fintype G] [Fintype X]
    {I E J : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    {A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center}

namespace AllocatedExternalCandidateProblem

variable {V : Type*} {s d : ℕ} (patch : PolynomialPatch V s d)
    [Fintype (PolynomialShearIndex patch.weight)]
    [TopologicalSpace (ℝ ⊗[ℚ] PolynomialShearLieAlgebra patch.weight ℚ)]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] PolynomialShearLieAlgebra patch.weight ℚ)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] PolynomialShearLieAlgebra patch.weight ℚ)]
    [T2Space (ℝ ⊗[ℚ] PolynomialShearLieAlgebra patch.weight ℚ)]
    {f : (X → ℤ) → ℝ} {lam cost mass score : ℝ}
    (P : AllocatedExternalCandidateProblem (E := E) A
      (polynomialShearNilmanifold patch.weight s patch.weight_le)
      (RationalTorus.trivialFiltration s) 0 1
      (fun _ y => (patch.shearObservable y : ℂ))
      (fun x => ((f x - lam : ℝ) : ℂ)) cost mass score)

theorem conclusion_of_shearDegreeGlobalization
    {M : ℝ≥0} {p outputCost : ℝ} {netExponent : ℕ}
    (hregularity : patch.ExternalObservableRegularity M p)
    (hp : 0 ≤ p) (hcost : cost ≤ p)
    (hmass : Real.exp (-p) ≤ mass) (hscore : Real.exp (-p) ≤ score)
    (hf : ∀ x, f x ∈ Set.Icc (0 : ℝ) 1) (hlam : lam ∈ Set.Icc (0 : ℝ) 1)
    (rule : A.DegreeGlobalizationAt (E := E)
      (fun x => ((f x - lam : ℝ) : ℂ)) s netExponent p outputCost) :
    Nonempty (P.Conclusion outputCost (Real.exp (-outputCost)) (Real.exp (-outputCost))) := by
  let refinement := P.budgetRefinement hcost hmass hscore
  have hweight (x : X → ℤ) : ‖((f x - lam : ℝ) : ℂ)‖ ≤ Real.exp p := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact (abs_le.mpr ⟨by linarith [(hf x).1, hlam.2],
      by linarith [(hf x).2, hlam.1]⟩).trans (Real.one_le_exp hp)
  obtain ⟨out⟩ := rule
    (polynomialShearNilmanifold patch.weight s patch.weight_le)
    (RationalTorus.trivialNilmanifold s) 0
    (fun _ _ _ => Submodule.zero_mem _)
    (fun j y _ => ⟨0, Submodule.zero_mem _, Subsingleton.elim _ _⟩)
    hregularity.geometry (RationalTorus.trivialNilmanifold_geometry s hp)
    (fun _ j => Fin.elim0 j) 1 (fun _ y => (patch.shearObservable y : ℂ))
    (patch.shearObservableLipBound M) hregularity.lip_bound
    (fun _ => hregularity.lipschitz) (fun _ => hregularity.positive)
    (patch.shearObservable_memberNets N A.size_pos hp netExponent)
    hweight refinement.problem
  exact ⟨refinement.conclusion out⟩

end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct NNReal

noncomputable def allocatedNormalizedShearObservableExponent (s : ℕ) : ℕ :=
  (exists_polynomialPatch_external_observable_budget.{0} s).choose

variable {m : ℕ} {G X : Type} [Fintype G] [Fintype X]
    {I E J : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    {A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center}

namespace AllocatedExternalCandidateProblem

variable {V : Type} {s d : ℕ} (patch : PolynomialPatch V s d)
    [Fintype (PolynomialShearIndex patch.weight)]
    {f : (X → ℤ) → ℝ} {target cost childCost normBudget : ℝ}
    {rankBound : ℕ} {productive : Finset A.Path}
    (P : AllocatedExternalCandidateProblem (E := E) A
      (polynomialShearNilmanifold patch.weight s patch.weight_le)
      (RationalTorus.trivialFiltration s) 0 1
      (fun _ y => (patch.shearObservable y : ℂ))
      (fun x => ((f x - target : ℝ) : ℂ)) cost
      ((A.law.mass productive /
        ((min rankBound ⌊childCost⌋₊ + 1) * (s + 1) ^ min rankBound ⌊childCost⌋₊ : ℕ)) *
        Real.exp (-normBudget)) (Real.exp (-normBudget)))

theorem exists_normalizedShearDegreeConclusion
    {gainLog gain pGlobal outputCost : ℝ} {netExponent : ℕ}
    (hchild : 0 ≤ childCost) (hd : d ≤ min rankBound ⌊childCost⌋₊)
    (hchildBudget : childCost ≤ normBudget)
    (hcenters : ∀ i, realPolynomialMass (patch.form.center i) ≤ normBudget)
    (hLip : (patch.kernel.lip : ℝ) ≤ Real.exp normBudget)
    (hgain : Real.exp (-gainLog) ≤ gain)
    (hReady : gain / 16 < A.law.mass productive)
    (hregularityBudget : (normBudget + 2) ^ allocatedNormalizedShearObservableExponent s ≤ pGlobal)
    (hpGlobal : 0 ≤ pGlobal) (hcost : cost ≤ pGlobal)
    (hscoreBudget : normBudget ≤ pGlobal)
    (hmassBudget : gainLog + 16 + ((s : ℝ) + 1) * childCost + normBudget ≤ pGlobal)
    (hf : ∀ x, f x ∈ Set.Icc (0 : ℝ) 1)
    (htarget : target ∈ Set.Icc (0 : ℝ) 1)
    (rule : A.DegreeGlobalizationAt (E := E)
      (fun x => ((f x - target : ℝ) : ℂ)) s netExponent pGlobal outputCost) :
    Nonempty (P.Conclusion outputCost (Real.exp (-outputCost)) (Real.exp (-outputCost))) := by
  let := moduleTopology ℝ (ℝ ⊗[ℚ] PolynomialShearLieAlgebra patch.weight ℚ)
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] PolynomialShearLieAlgebra patch.weight ℚ) :=
    IsModuleTopology.topologicalAddGroup ℝ _
  let := realification_moduleTopology_t2
    (polynomialShearNilmanifold patch.weight s patch.weight_le).basis
  have hnorm : 0 ≤ normBudget := hchild.trans hchildBudget
  have hdBudget : (d : ℝ) ≤ normBudget :=
    (Nat.cast_le.mpr (hd.trans (min_le_right _ _))).trans
      ((Nat.floor_le hchild).trans hchildBudget)
  have regularity := PolynomialPatch.ExternalObservableRegularity.mono patch
    ((exists_polynomialPatch_external_observable_budget s).choose_spec.2
      patch normBudget hnorm hdBudget hcenters hLip) hregularityBudget
  have hmass := (Real.exp_le_exp.mpr (neg_le_neg hmassBudget)).trans
    (preparedReady_capped_normalized_mass_lower rankBound s hchild hgain hReady
      (normBudget := normBudget))
  exact P.conclusion_of_shearDegreeGlobalization patch regularity hpGlobal hcost hmass
    (Real.exp_le_exp.mpr (neg_le_neg hscoreBudget)) hf htarget rule

noncomputable def normalizedShearDegreeConclusion
    {gainLog gain pGlobal outputCost : ℝ} {netExponent : ℕ}
    (hchild : 0 ≤ childCost) (hd : d ≤ min rankBound ⌊childCost⌋₊)
    (hchildBudget : childCost ≤ normBudget)
    (hcenters : ∀ i, realPolynomialMass (patch.form.center i) ≤ normBudget)
    (hLip : (patch.kernel.lip : ℝ) ≤ Real.exp normBudget)
    (hgain : Real.exp (-gainLog) ≤ gain)
    (hReady : gain / 16 < A.law.mass productive)
    (hregularityBudget : (normBudget + 2) ^ allocatedNormalizedShearObservableExponent s ≤ pGlobal)
    (hpGlobal : 0 ≤ pGlobal) (hcost : cost ≤ pGlobal)
    (hscoreBudget : normBudget ≤ pGlobal)
    (hmassBudget : gainLog + 16 + ((s : ℝ) + 1) * childCost + normBudget ≤ pGlobal)
    (hf : ∀ x, f x ∈ Set.Icc (0 : ℝ) 1)
    (htarget : target ∈ Set.Icc (0 : ℝ) 1)
    (rule : A.DegreeGlobalizationAt (E := E)
      (fun x => ((f x - target : ℝ) : ℂ)) s netExponent pGlobal outputCost) :
    P.Conclusion outputCost (Real.exp (-outputCost)) (Real.exp (-outputCost)) :=
  Classical.choice (P.exists_normalizedShearDegreeConclusion patch
    hchild hd hchildBudget hcenters hLip hgain hReady hregularityBudget
    hpGlobal hcost hscoreBudget hmassBudget hf htarget rule)

end AllocatedExternalCandidateProblem

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.CanonicalZeroLayerBudgetedInitialization
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct NNReal

namespace CanonicalEmptyLayerGeometry

noncomputable def zeroLayerScale (G : Type) [Fintype G] (side : ℕ) (hside : 0 < side) :
    LayerSamplerScale (G := G) (B 0) (U 0) (b 0) (fun _ => 1) (fun _ => 1) :=
  emptyLayerSamplerScale (B 0) (U 0) (b 0) side hside (fun j => Fin.elim0 j)

@[simp] theorem zeroLayerScale_value (G : Type) [Fintype G] (side : ℕ) (hside : 0 < side) :
    (zeroLayerScale G side hside).value = side := rfl

end CanonicalEmptyLayerGeometry

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedExternalCandidateGeneratedFreezingSuccessor
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration
open scoped BigOperators Classical TensorProduct

variable {m : ℕ} {G X : Type} [Fintype G] [Fintype X]
    {I E J : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    {A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center}
    {L M : Type} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s d t : ℕ} {D : RationalFilteredNilmanifold L s d}
    {Fmark : NilpotentLieFiltration M t} {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}

namespace AllocatedExternalCandidateProblem

variable {cost massThreshold scoreThreshold : ℝ}
    (P : AllocatedExternalCandidateProblem (E := E) A D Fmark φ marked observable weight
      cost massThreshold scoreThreshold)

theorem frozenMarkedPhysical_bounds
    {κ : Type} [Fintype κ] [DecidableEq κ] (cF : Basis κ ℚ M)
    (sectionMap : M →ₗ[ℚ] L)
    (hSection : ∀ j, ∀ y ∈ Fmark.layer j, sectionMap y ∈ D.filtration.layer j) :
    let C := frozenMarkedPhysicalExponent s
    ∀ (H HS : ℕ) (p : ℝ), 0 ≤ p →
        (Fintype.card (Fin d) : ℝ) ≤ p → (Fintype.card κ : ℝ) ≤ p →
        (H : ℝ) ≤ Real.exp p → (HS : ℝ) ≤ Real.exp p →
        (∀ i j k, RationalHeightLE (lieStructureConstants D.basis i j k) H) →
        (∀ i j, RationalHeightLE (LinearMap.toMatrix cF D.basis sectionMap i j) HS) →
        ∀ q r : ℕ, 0 < q → 0 < r →
          ((matrixDenominator (LinearMap.toMatrix cF D.basis sectionMap) * q * r : ℕ) : ℝ) ≤
            Real.exp p →
          ∃ mFull : ℕ, 0 < mFull ∧ (mFull : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
            matrixDenominator (LinearMap.toMatrix cF D.basis sectionMap) * q * r ∣ mFull ∧
            ∀ leftMark rightMark : Fmark.realification.PolynomialOrbit
                (fullTaggedVariableWeight (X := X) J),
              (∀ x ∈ integerBox N, ∀ i, |(cF.baseChange ℝ).repr
                (Fmark.realification.polynomialOrbitEval (fullTaggedVariableWeight J)
                  (P.physicalIntegerPoint x) leftMark).coord i| ≤ Real.exp p) →
              CoefficientGrid (cF.baseChange ℝ) q rightMark.log →
              ∀ leftCenter rightCenter : D.filtration.realification.Group,
                (∀ i, |(D.basis.baseChange ℝ).repr leftCenter.coord i| ≤ Real.exp p) →
                (D.basis.baseChange ℝ).equivFun rightCenter.coord ∈ realDenominatorGrid r →
                (∀ x ∈ integerBox N, ∀ i, |(D.basis.baseChange ℝ).repr
                  (D.filtration.realification.polynomialOrbitEval (fullTaggedVariableWeight J)
                    (P.physicalIntegerPoint x)
                    (D.filtration.frozenMarkedLeftOrbit Fmark (fullTaggedVariableWeight J)
                      sectionMap hSection leftMark leftCenter)).coord i| ≤ Real.exp ((p + C) ^ C)) ∧
                (∀ x ∈ integerBox N, (D.basis.baseChange ℝ).equivFun
                  (D.filtration.realification.polynomialOrbitEval (fullTaggedVariableWeight J)
                    (P.physicalIntegerPoint x)
                    (D.filtration.frozenMarkedRightOrbit Fmark (fullTaggedVariableWeight J)
                      sectionMap hSection rightMark rightCenter)).coord ∈ realDenominatorGrid mFull) := by
  intro C H HS p hp hdim hdimF hH hHS hlie hsection q r hq hr hqr
  obtain ⟨mFull, hm, hmp, hdiv, hgrid⟩ :=
    exists_frozenMarkedPhysical_right_grid D.filtration Fmark D.basis cF
      (fullTaggedVariableWeight (X := X) J) sectionMap hSection
      H p hp hdim hH hlie q r hq hr hqr
  refine ⟨mFull, hm, hmp, hdiv, ?_⟩
  intro leftMark rightMark hleftMark hrightMark leftCenter rightCenter hleftCenter hrightCenter
  constructor
  · intro x hx i
    exact frozenMarkedPhysical_left_bound D.filtration Fmark D.basis cF
      (fullTaggedVariableWeight J) sectionMap hSection H HS p
      hp hdim hdimF hH hHS hlie hsection leftMark leftCenter
      (P.physicalIntegerPoint x) (hleftMark x hx) hleftCenter i
  · intro x _
    exact hgrid rightMark hrightMark rightCenter hrightCenter (P.physicalIntegerPoint x)

end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedExternalCandidateThresholdSuccessor
namespace OAI

section

namespace Erdos3.VectorPolynomial
open NilpotentLieFiltration RationalFilteredNilmanifold

theorem candidatePrimitiveFreezingCutoff_le_geometry (s a : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    candidatePrimitiveFreezingCutoff s a p ≤
      candidatePrimitivePhysicalGeometryParameter s a p := by
  let Cfree := nativeMarkedFreezingExponent (s + 1) a
  let outerExponent := candidateFreezingOuterExponent s a
  let B := frozenMarkedPhysicalExponent (s + 1)
  let R := allocatedRightDictionaryExponent (s + 1)
  let outer := candidateCoveredOuterParameter outerExponent p
  let right := candidateCoveredRightParameter outerExponent B p
  let dict := candidateCoveredDictionaryParameter outerExponent B R p
  have houter : nativeMarkedFreezingPhysicalParameter p Cfree ≤ outer :=
    candidatePrimitivePhysicalOuterParameter_bound s a hp
  have houter0 : 0 ≤ outer := by dsimp [outer, candidateCoveredOuterParameter]; positivity
  have hdict0 : 0 ≤ dict := by
    dsimp [dict, candidateCoveredDictionaryParameter, candidateCoveredRightParameter,
      candidateCoveredOuterParameter]
    positivity
  have hB : 2 ≤ B := frozenMarkedPhysicalExponent_ge_two (s + 1)
  have hright : outer ≤ right := by
    apply (le_power_budget houter0 (by omega : 1 ≤ B)).trans
    dsimp [right, candidateCoveredRightParameter]
    exact pow_le_pow_left₀ (by positivity)
      (add_le_add le_rfl (by exact_mod_cast hB : (2 : ℝ) ≤ B)) B
  have hlarge : 1 ≤ (p + 3) ^ 36 := one_le_pow₀ (by linarith)
  have hblog : (p + Cfree) ^ Cfree + 1 ≤ outer := by
    dsimp [nativeMarkedFreezingPhysicalParameter] at houter
    linarith
  change p + 2 * (p + Cfree) ^ Cfree + 2 ≤ p + outer + right + dict + 1
  linarith

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedCenteredStagedModelProductiveGood
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal

def PreparedCenteredFiniteProductiveGoodConclusion
    {m nX M : ℕ} {X₀ J₀ : Type}
    (prep : RankPreparationFamily X₀ J₀ m)
    (U : ∀ j : Fin m, Submodule ℝ (RankPreparationLayer.Coord (prep j) → ℝ))
    (b : ∀ j, Basis (Fin (preparedSamplerTransverse prep j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ}
    (S : LayerSamplerScale (G := EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (I := PreparedSamplerContinuous prep) (n := preparedSamplerTransverse prep)
      (J := fun j : Fin m => RankPreparationLayer.Coord (prep j)) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b R σ)
    {E : Fin m → Type} [∀ j, Fintype (E j)]
    (bW : ∀ j, Basis (E j) ℤ
      (latticeSection (standardEuclideanLattice (RankPreparationLayer.Coord (prep j))) (euclideanSubspace (U j))))
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (PreparedSamplerContinuous prep j) ℝ (euclideanSubspace (U j)))
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U)]
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U))
    (poly : ∀ j, VectorPolynomial (Fin nX) ℝ (RankPreparationLayer.Coord (prep j) → ℝ))
    (hm : ∀ j ex, coefficients (poly j) ex ∈ U j)
    (stride : Fin nX → ℕ)
    (width : Option (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) × Fin nX → ℝ)
    (bases : Finset (Fin nX → ℤ))
    (gainLog gain : ℝ) (Q : ℕ)
    (e : Fin 2 × Fin nX ↪ EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
    (law : (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U) → FiniteProbabilityWeights (bases × rectangularWeightIndices 0 width 1))
    (N : Fin nX → ℕ) (test : (Fin nX → ℝ) → ℝ) : Prop :=
    ∃ (c : CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U → ∀ j, U j), Measurable c ∧
      (∀ center, coefficientConstantCenter U center =
        -(QuotientAddGroup.mk' (coefficientIntegerLattice U)
          (constantCoefficientArray U (fun s => c center s.1)))) ∧
    ∃ (sample : CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U → (Fin nX → ℤ) → (Option (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) × Fin nX → ℤ) →
          CoefficientSamplerArrays (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep))
      (read : CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U → (Fin nX → ℤ) → (Option (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) × Fin nX → ℤ) → AllocatedActualCoefficientIndex (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (Fin nX) (PreparedSamplerContinuous prep) E (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) → ℤ),
      (∀ center a, AllocatedCenteredRecoveredSampleReadAt (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U bW b hb o S hR hσ poly hm (allocatedShortAxis (I := PreparedSamplerContinuous prep) U b S.value) (preparedInitialRankSpatialEmbedding (m := m) nX M) (preparedInitialRankKernelEmbedding (m := m) nX M) (preparedInitialRankPrincipalEmbedding prep nX M (allocatedShortAxis (I := PreparedSamplerContinuous prep) U b S.value)) (modularInitialRankStrength m (nX + m * M) : ℝ) center (c center) a (sample center a) (read center a)) ∧
      ∀ (primes : Finset ℕ) (hprime : ∀ p ∈ primes, p.Prime),
        letI : ∀ p : primes, NeZero p.val := fun p => ⟨(hprime p.val p.property).ne_zero⟩
        ∀ (depth : ℕ → ℕ), (∀ p ∈ primes, p ^ depth p ≤ Q) →
        ∀ (residual : Set (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U × (bases × rectangularWeightIndices 0 width 1))),
          MeasurableSet residual → (centeredFiniteProbabilityMeasure μ law).real residual ≤ gain / 32 →
        ∀ (Extra : CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U × (bases × rectangularWeightIndices 0 width 1) → Prop),
          (∀ᵐ z ∂centeredFiniteProbabilityMeasure μ law, Extra z) →
        ∃ (center : CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U) (F : Finset (bases × rectangularWeightIndices 0 width 1)),
          gain / 16 < (law center).mass F ∧
          ∀ z ∈ F, 0 < (law center).weight z ∧ (center,z) ∉ residual ∧ Extra (center,z) ∧
            AllocatedPathProductivity (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b S N width bases test gain z ∧
            (∃ c₀ : ∀ j, U j, coefficientConstantCenter U center =
              -(QuotientAddGroup.mk' (coefficientIntegerLattice U)
                (constantCoefficientArray U (fun s => c₀ s.1))) ∧
              allocatedAffineDensity (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b hb o hR hσ S poly hm c₀
                (fun k v => (jointIntegerFrame (z.1.val,z.2.val) k v : ℝ)) ≠ 0) ∧
            AllocatedCenteredFramedRecoveredSampleAt (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b hb o S hR hσ poly hm
              (c center) z.1.val z.2.val (sample center z.1.val z.2.val) (allocatedJointFrameRead z.1.val (read center z.1.val z.2.val)) ∧
            (∏ p ∈ primes, p ^ largestTestedBadDepth depth (allocatedActualPrimeBad (allocatedShortAxis (I := PreparedSamplerContinuous prep) U b S.value) (preparedInitialRankSpatialEmbedding (m := m) nX M) (preparedInitialRankKernelEmbedding (m := m) nX M) (preparedInitialRankPrincipalEmbedding prep nX M (allocatedShortAxis (I := PreparedSamplerContinuous prep) U b S.value)) primes (modularInitialRankStrength m (nX + m * M) : ℝ)) p (allocatedJointFrameRead z.1.val (read center z.1.val z.2.val))) ≤ (∏ x, stride x) ^ 2 * (smallPrimePowerCorrection (modularCoefficientPrimeThreshold m) * quantitativeBadPrimeRadius (gainLog + 8)) ∧
            ∀ t : Fin 2, spatialMatrixBlockThreshold nX (jointSpatialError gainLog) / 2 <
              |Matrix.det (fun i j : Fin nX =>
                spatialMatrixNormalizedEntries e width z.2.val (t,j,i))|

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal

def PreparedCenteredProductiveGoodCenterConclusion
    {m nX M : ℕ} {X₀ J₀ : Type}
    (prep : RankPreparationFamily X₀ J₀ m)
    (U : ∀ j : Fin m, Submodule ℝ (RankPreparationLayer.Coord (prep j) → ℝ))
    (b : ∀ j, Basis (Fin (preparedSamplerTransverse prep j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ}
    (S : LayerSamplerScale (G := EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (I := PreparedSamplerContinuous prep) (n := preparedSamplerTransverse prep)
      (J := fun j : Fin m => RankPreparationLayer.Coord (prep j)) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b R σ)
    {E : Fin m → Type} [∀ j, Fintype (E j)]
    (bW : ∀ j, Basis (E j) ℤ
      (latticeSection (standardEuclideanLattice (RankPreparationLayer.Coord (prep j))) (euclideanSubspace (U j))))
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (PreparedSamplerContinuous prep j) ℝ (euclideanSubspace (U j)))
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U)]
    (_μ : Measure (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U))
    (poly : ∀ j, VectorPolynomial (Fin nX) ℝ (RankPreparationLayer.Coord (prep j) → ℝ))
    (hm : ∀ j ex, coefficients (poly j) ex ∈ U j)
    (stride : Fin nX → ℕ)
    (width : Option (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) × Fin nX → ℝ)
    (bases : Finset (Fin nX → ℤ))
    (gainLog gain : ℝ) (Q : ℕ)
    (e : Fin 2 × Fin nX ↪ EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
    (law : (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U) → FiniteProbabilityWeights (bases × rectangularWeightIndices 0 width 1))
    (N : Fin nX → ℕ) (test : (Fin nX → ℝ) → ℝ) : Prop :=
    ∃ (c : CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U → ∀ j, U j), Measurable c ∧
      (∀ center, coefficientConstantCenter U center =
        -(QuotientAddGroup.mk' (coefficientIntegerLattice U)
          (constantCoefficientArray U (fun s => c center s.1)))) ∧
    ∃ (sample : CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U → (Fin nX → ℤ) → (Option (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) × Fin nX → ℤ) →
          CoefficientSamplerArrays (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep))
      (read : CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U → (Fin nX → ℤ) → (Option (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) × Fin nX → ℤ) → AllocatedActualCoefficientIndex (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (Fin nX) (PreparedSamplerContinuous prep) E (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) → ℤ),
      (∀ center a, AllocatedCenteredRecoveredSampleReadAt (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U bW b hb o S hR hσ poly hm (allocatedShortAxis (I := PreparedSamplerContinuous prep) U b S.value) (preparedInitialRankSpatialEmbedding (m := m) nX M) (preparedInitialRankKernelEmbedding (m := m) nX M) (preparedInitialRankPrincipalEmbedding prep nX M (allocatedShortAxis (I := PreparedSamplerContinuous prep) U b S.value)) (modularInitialRankStrength m (nX + m * M) : ℝ) center (c center) a (sample center a) (read center a)) ∧
      ∀ (primes : Finset ℕ) (hprime : ∀ p ∈ primes, p.Prime),
        letI : ∀ p : primes, NeZero p.val := fun p => ⟨(hprime p.val p.property).ne_zero⟩
        ∀ (depth : ℕ → ℕ), (∀ p ∈ primes, p ^ depth p ≤ Q) →
        ∃ (center : CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U) (F : Finset (bases × rectangularWeightIndices 0 width 1)),
          gain / 16 < (law center).mass F ∧
          ∀ z ∈ F, 0 < (law center).weight z ∧
            AllocatedPathProductivity (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b S N width bases test gain z ∧
            (∃ c₀ : ∀ j, U j, coefficientConstantCenter U center =
              -(QuotientAddGroup.mk' (coefficientIntegerLattice U)
                (constantCoefficientArray U (fun s => c₀ s.1))) ∧
              allocatedAffineDensity (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b hb o hR hσ S poly hm c₀
                (fun k v => (jointIntegerFrame (z.1.val,z.2.val) k v : ℝ)) ≠ 0) ∧
            AllocatedCenteredFramedRecoveredSampleAt (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b hb o S hR hσ poly hm
              (c center) z.1.val z.2.val (sample center z.1.val z.2.val) (allocatedJointFrameRead z.1.val (read center z.1.val z.2.val)) ∧
            (∏ p ∈ primes, p ^ largestTestedBadDepth depth (allocatedActualPrimeBad (allocatedShortAxis (I := PreparedSamplerContinuous prep) U b S.value) (preparedInitialRankSpatialEmbedding (m := m) nX M) (preparedInitialRankKernelEmbedding (m := m) nX M) (preparedInitialRankPrincipalEmbedding prep nX M (allocatedShortAxis (I := PreparedSamplerContinuous prep) U b S.value)) primes (modularInitialRankStrength m (nX + m * M) : ℝ)) p (allocatedJointFrameRead z.1.val (read center z.1.val z.2.val))) ≤ (∏ x, stride x) ^ 2 * (smallPrimePowerCorrection (modularCoefficientPrimeThreshold m) * quantitativeBadPrimeRadius (gainLog + 8)) ∧
            ∀ t : Fin 2, spatialMatrixBlockThreshold nX (jointSpatialError gainLog) / 2 <
              |Matrix.det (fun i j : Fin nX =>
                spatialMatrixNormalizedEntries e width z.2.val (t,j,i))|

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedReadyPaddedRelativeInitialization
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal

def PreparedCenteredProductiveGoodCenterReadyConclusion
    {m nX M : ℕ} {X₀ J₀ : Type}
    (prep : RankPreparationFamily X₀ J₀ m)
    (U : ∀ j : Fin m, Submodule ℝ (RankPreparationLayer.Coord (prep j) → ℝ))
    (b : ∀ j, Basis (Fin (preparedSamplerTransverse prep j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ}
    (S : LayerSamplerScale (G := EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (I := PreparedSamplerContinuous prep) (n := preparedSamplerTransverse prep)
      (J := fun j : Fin m => RankPreparationLayer.Coord (prep j)) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b R σ)
    {E : Fin m → Type} [∀ j, Fintype (E j)]
    (bW : ∀ j, Basis (E j) ℤ
      (latticeSection (standardEuclideanLattice (RankPreparationLayer.Coord (prep j))) (euclideanSubspace (U j))))
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (PreparedSamplerContinuous prep j) ℝ (euclideanSubspace (U j)))
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U)]
    (_μ : Measure (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U))
    (poly : ∀ j, VectorPolynomial (Fin nX) ℝ (RankPreparationLayer.Coord (prep j) → ℝ))
    (hm : ∀ j ex, coefficients (poly j) ex ∈ U j)
    (stride : Fin nX → ℕ)
    (width : Option (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) × Fin nX → ℝ)
    (bases : Finset (Fin nX → ℤ))
    (gainLog gain : ℝ) (Q : ℕ)
    (e : Fin 2 × Fin nX ↪ EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
    (law : (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U) → FiniteProbabilityWeights (bases × rectangularWeightIndices 0 width 1))
    (N : Fin nX → ℕ) (test : (Fin nX → ℝ) → ℝ)
    (Ready : CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U → Prop) : Prop :=
    ∃ (c : CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U → ∀ j, U j), Measurable c ∧
      (∀ center, coefficientConstantCenter U center =
        -(QuotientAddGroup.mk' (coefficientIntegerLattice U)
          (constantCoefficientArray U (fun s => c center s.1)))) ∧
    ∃ (sample : CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U → (Fin nX → ℤ) → (Option (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) × Fin nX → ℤ) →
          CoefficientSamplerArrays (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep))
      (read : CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U → (Fin nX → ℤ) → (Option (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) × Fin nX → ℤ) → AllocatedActualCoefficientIndex (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (Fin nX) (PreparedSamplerContinuous prep) E (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) → ℤ),
      (∀ center a, AllocatedCenteredRecoveredSampleReadAt (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U bW b hb o S hR hσ poly hm (allocatedShortAxis (I := PreparedSamplerContinuous prep) U b S.value) (preparedInitialRankSpatialEmbedding (m := m) nX M) (preparedInitialRankKernelEmbedding (m := m) nX M) (preparedInitialRankPrincipalEmbedding prep nX M (allocatedShortAxis (I := PreparedSamplerContinuous prep) U b S.value)) (modularInitialRankStrength m (nX + m * M) : ℝ) center (c center) a (sample center a) (read center a)) ∧
      ∀ (primes : Finset ℕ) (hprime : ∀ p ∈ primes, p.Prime),
        letI : ∀ p : primes, NeZero p.val := fun p => ⟨(hprime p.val p.property).ne_zero⟩
        ∀ (depth : ℕ → ℕ), (∀ p ∈ primes, p ^ depth p ≤ Q) →
        ∃ (center : CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U) (F : Finset (bases × rectangularWeightIndices 0 width 1)),
          Ready center ∧ gain / 16 < (law center).mass F ∧
          ∀ z ∈ F, 0 < (law center).weight z ∧
            AllocatedPathProductivity (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b S N width bases test gain z ∧
            (∃ c₀ : ∀ j, U j, coefficientConstantCenter U center =
              -(QuotientAddGroup.mk' (coefficientIntegerLattice U)
                (constantCoefficientArray U (fun s => c₀ s.1))) ∧
              allocatedAffineDensity (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b hb o hR hσ S poly hm c₀
                (fun k v => (jointIntegerFrame (z.1.val,z.2.val) k v : ℝ)) ≠ 0) ∧
            AllocatedCenteredFramedRecoveredSampleAt (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b hb o S hR hσ poly hm
              (c center) z.1.val z.2.val (sample center z.1.val z.2.val) (allocatedJointFrameRead z.1.val (read center z.1.val z.2.val)) ∧
            (∏ p ∈ primes, p ^ largestTestedBadDepth depth (allocatedActualPrimeBad (allocatedShortAxis (I := PreparedSamplerContinuous prep) U b S.value) (preparedInitialRankSpatialEmbedding (m := m) nX M) (preparedInitialRankKernelEmbedding (m := m) nX M) (preparedInitialRankPrincipalEmbedding prep nX M (allocatedShortAxis (I := PreparedSamplerContinuous prep) U b S.value)) primes (modularInitialRankStrength m (nX + m * M) : ℝ)) p (allocatedJointFrameRead z.1.val (read center z.1.val z.2.val))) ≤ (∏ x, stride x) ^ 2 * (smallPrimePowerCorrection (modularCoefficientPrimeThreshold m) * quantitativeBadPrimeRadius (gainLog + 8)) ∧
            ∀ t : Fin 2, spatialMatrixBlockThreshold nX (jointSpatialError gainLog) / 2 <
              |Matrix.det (fun i j : Fin nX =>
                spatialMatrixNormalizedEntries e width z.2.val (t,j,i))|

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal

def PreparedCenteredProductiveGoodCenterEnhancedConclusion
    {m nX M : ℕ} {X₀ J₀ : Type}
    (prep : RankPreparationFamily X₀ J₀ m)
    (U : ∀ j : Fin m, Submodule ℝ (RankPreparationLayer.Coord (prep j) → ℝ))
    (b : ∀ j, Basis (Fin (preparedSamplerTransverse prep j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ}
    (S : LayerSamplerScale (G := EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (I := PreparedSamplerContinuous prep) (n := preparedSamplerTransverse prep)
      (J := fun j : Fin m => RankPreparationLayer.Coord (prep j)) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b R σ)
    {E : Fin m → Type} [∀ j, Fintype (E j)]
    (bW : ∀ j, Basis (E j) ℤ
      (latticeSection (standardEuclideanLattice (RankPreparationLayer.Coord (prep j))) (euclideanSubspace (U j))))
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (PreparedSamplerContinuous prep j) ℝ (euclideanSubspace (U j)))
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U)]
    (_μ : Measure (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U))
    (poly : ∀ j, VectorPolynomial (Fin nX) ℝ (RankPreparationLayer.Coord (prep j) → ℝ))
    (hm : ∀ j ex, coefficients (poly j) ex ∈ U j)
    (stride : Fin nX → ℕ)
    (width : Option (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) × Fin nX → ℝ)
    (bases : Finset (Fin nX → ℤ))
    (gainLog gain : ℝ) (Q : ℕ)
    (e : Fin 2 × Fin nX ↪ EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
    (law : (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U) → FiniteProbabilityWeights (bases × rectangularWeightIndices 0 width 1))
    (N : Fin nX → ℕ) (test : (Fin nX → ℝ) → ℝ)
    (Ready : CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U → Prop)
    (Extra : CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U →
      (∀ j, U j) → Finset (bases × rectangularWeightIndices 0 width 1) → Prop) : Prop :=
    ∃ (c : CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U → ∀ j, U j), Measurable c ∧
      (∀ center, coefficientConstantCenter U center =
        -(QuotientAddGroup.mk' (coefficientIntegerLattice U)
          (constantCoefficientArray U (fun s => c center s.1)))) ∧
    ∃ (sample : CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U → (Fin nX → ℤ) → (Option (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) × Fin nX → ℤ) →
          CoefficientSamplerArrays (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep))
      (read : CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U → (Fin nX → ℤ) → (Option (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) × Fin nX → ℤ) → AllocatedActualCoefficientIndex (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (Fin nX) (PreparedSamplerContinuous prep) E (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) → ℤ),
      (∀ center a, AllocatedCenteredRecoveredSampleReadAt (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U bW b hb o S hR hσ poly hm (allocatedShortAxis (I := PreparedSamplerContinuous prep) U b S.value) (preparedInitialRankSpatialEmbedding (m := m) nX M) (preparedInitialRankKernelEmbedding (m := m) nX M) (preparedInitialRankPrincipalEmbedding prep nX M (allocatedShortAxis (I := PreparedSamplerContinuous prep) U b S.value)) (modularInitialRankStrength m (nX + m * M) : ℝ) center (c center) a (sample center a) (read center a)) ∧
      ∀ (primes : Finset ℕ) (hprime : ∀ p ∈ primes, p.Prime),
        letI : ∀ p : primes, NeZero p.val := fun p => ⟨(hprime p.val p.property).ne_zero⟩
        ∀ (depth : ℕ → ℕ), (∀ p ∈ primes, p ^ depth p ≤ Q) →
        ∃ (center : CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U) (F : Finset (bases × rectangularWeightIndices 0 width 1)),
          Ready center ∧ gain / 16 < (law center).mass F ∧
          (∀ z ∈ F, 0 < (law center).weight z ∧
            AllocatedPathProductivity (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b S N width bases test gain z ∧
            (∃ c₀ : ∀ j, U j, coefficientConstantCenter U center =
              -(QuotientAddGroup.mk' (coefficientIntegerLattice U)
                (constantCoefficientArray U (fun s => c₀ s.1))) ∧
              allocatedAffineDensity (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b hb o hR hσ S poly hm c₀
                (fun k v => (jointIntegerFrame (z.1.val,z.2.val) k v : ℝ)) ≠ 0) ∧
            AllocatedCenteredFramedRecoveredSampleAt (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b hb o S hR hσ poly hm
              (c center) z.1.val z.2.val (sample center z.1.val z.2.val) (allocatedJointFrameRead z.1.val (read center z.1.val z.2.val)) ∧
            (∏ p ∈ primes, p ^ largestTestedBadDepth depth (allocatedActualPrimeBad (allocatedShortAxis (I := PreparedSamplerContinuous prep) U b S.value) (preparedInitialRankSpatialEmbedding (m := m) nX M) (preparedInitialRankKernelEmbedding (m := m) nX M) (preparedInitialRankPrincipalEmbedding prep nX M (allocatedShortAxis (I := PreparedSamplerContinuous prep) U b S.value)) primes (modularInitialRankStrength m (nX + m * M) : ℝ)) p (allocatedJointFrameRead z.1.val (read center z.1.val z.2.val))) ≤ (∏ x, stride x) ^ 2 * (smallPrimePowerCorrection (modularCoefficientPrimeThreshold m) * quantitativeBadPrimeRadius (gainLog + 8)) ∧
            ∀ t : Fin 2, spatialMatrixBlockThreshold nX (jointSpatialError gainLog) / 2 <
              |Matrix.det (fun i j : Fin nX =>
                spatialMatrixNormalizedEntries e width z.2.val (t,j,i))|) ∧
          Extra center (c center) F

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PreparedUniformDegreeDirectMasterBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule
open scoped Classical BigOperators NNReal

def PreparedUniformDegreeGeometryAt
    {m : ℕ} {G : Type} [Fintype G] [DecidableEq G]
    {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
    {J : Fin m → Type} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
    (s Cdetect nX : ℕ)
    (Bstruct Pscale D target Pk Prho Qstride pDetect pRadius aDetect gainLog : ℝ) : Prop :=
    Nonempty (AllocatedEarlyNativeSourceGeometryGeneral (B := B) (U := U)
      (basis := basis) (S := S) (s := s) (nX := nX)
      Bstruct Pscale D target Pk Prho Qstride pDetect
      (Real.toNNReal (Real.exp pRadius))) ∧
    ∀ α : ℝ, Real.exp (-aDetect) ≤ α →
      let gain := (Real.exp (-((5 * pDetect + 20) *
          Fintype.card (LayerSamplerVariables G I n B) + pDetect + 2)) * (α / 2)) *
        Real.exp (-((pDetect + Cdetect) ^ Cdetect)) ^ (2 ^ (s + 1))
      Real.exp (-gainLog) ≤ gain ∧
        (scalarKernelCutoff (Fin (s + 1)) G 1 ⌈Real.exp (pDetect + 1)⌉₊ (gain / 2) : ℝ) ≤
          Real.exp Pk ∧
        scalarKernelCutoff (Fin (s + 1)) G 1 ⌈Real.exp (pDetect + 1)⌉₊ (gain / 2) ≤ S.value

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.PreparedRelativeEndpointForecastBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

theorem exists_preparedRelativeEndpointForecast_budget (m : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (M nX Jalloc : ℕ)
      {t Pdim cost pRadius gainLog Qstride PF Pchart childLog u p budget Pspatial : ℝ},
      0 ≤ t →
      allocatedComparisonDimension m
        (enlargedPreparedCommonSamplerDimension m M Jalloc : ℝ) ≤ t →
      ((nX + m * M : ℕ) : ℝ) ≤ t →
      Pdim ∈ Set.Icc 0 t → cost ∈ Set.Icc 0 t → pRadius ∈ Set.Icc 0 t →
      gainLog ∈ Set.Icc 0 t → Qstride ∈ Set.Icc 0 t → PF ∈ Set.Icc 0 t →
      Pchart ∈ Set.Icc 0 t → childLog ∈ Set.Icc 0 t →
      u ∈ Set.Icc 0 t → p ∈ Set.Icc 0 t → budget ∈ Set.Icc 0 t →
      Pspatial ∈ Set.Icc 0 t →
      let Eearly := 2 * u + 4 * p + 12
      let nativeEarly := preparedConcreteSlicedForecastNativeLog m M nX Jalloc
        Pdim cost pRadius gainLog Qstride PF Pchart childLog Eearly
      let massEarly := preparedConcreteSlicedForecastMassLog m M nX Jalloc
        Pdim cost pRadius gainLog Qstride Pchart childLog Eearly
      let Ptest := max budget (3 * nativeEarly + 3)
      let Ecompare := max Ptest (2 * u + 4 * p + max 0 massEarly + 20) + 2 + cost + cost + 8
      let nativeLate := preparedConcreteSlicedForecastNativeLog m M nX Jalloc
        Pdim cost pRadius gainLog Qstride PF Pchart childLog (Ecompare + 8)
      let massLate := preparedConcreteSlicedForecastMassLog m M nX Jalloc
        Pdim cost pRadius gainLog Qstride Pchart childLog (Ecompare + 8)
      let ambient := (max (max Pspatial (2 * max Ptest (3 * nativeLate + 3) + 1))
        (massLate + Ecompare + 8) + nativeForecastAmbientExponent m) ^
          nativeForecastAmbientExponent m
      Ptest ∈ Set.Icc 0 ((t + C) ^ C) ∧
      Ecompare ∈ Set.Icc 0 ((t + C) ^ C) ∧
      nativeEarly ∈ Set.Icc 0 ((t + C) ^ C) ∧
      massEarly ∈ Set.Icc 0 ((t + C) ^ C) ∧
      nativeLate ∈ Set.Icc 0 ((t + C) ^ C) ∧
      massLate ∈ Set.Icc 0 ((t + C) ^ C) ∧
      actualForecastDataModelRequired budget nativeEarly massEarly u p ∈
        Set.Icc 0 ((t + C) ^ C) ∧ ambient ∈ Set.Icc 0 ((t + C) ^ C) := by
  obtain ⟨Cearly, _, hearly⟩ := exists_preparedConcreteSlicedForecastLocalModel_budget m 1
  obtain ⟨Clate, _, hlate⟩ := exists_preparedConcreteSlicedForecastPacketLog_budget m
  let Ca := nativeForecastAmbientExponent m
  let X : Polynomial ℕ := Polynomial.X
  let W : Polynomial ℕ := (X + Polynomial.C Cearly) ^ Cearly
  let R : Polynomial ℕ := W + 3 * X + 20
  let Z : Polynomial ℕ := (R + Polynomial.C Clate) ^ Clate
  let F : Polynomial ℕ := W + R + Z +
    (X + 3 * W + 7 * Z + R + 16 + Polynomial.C Ca) ^ Ca
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget F
  refine ⟨C, hC, ?_⟩
  intro M nX Jalloc t Pdim cost pRadius gainLog Qstride PF Pchart childLog u p budget Pspatial
    ht hD hdim hPdim hcost hRadius hGain hStride hPF hChart hChild hu hp hbudget hSpatial
    Eearly nativeEarly massEarly Ptest Ecompare nativeLate massLate ambient
  let w : ℝ := (t + Cearly) ^ Cearly
  let r : ℝ := w + 3 * t + 20
  let z : ℝ := (r + Clate) ^ Clate
  have hw : 0 ≤ w := by dsimp only [w]; positivity
  have hr : 0 ≤ r := by dsimp only [r]; positivity
  have hz : 0 ≤ z := by dsimp only [z]; positivity
  have htr : t ≤ r := by dsimp only [r]; linarith only [hw, ht]
  have hb : budget ∈ Set.Icc 0 ((t + (1 : ℕ)) ^ (1 : ℕ)) := by
    simpa only [Nat.cast_one, pow_one] using
      (show budget ∈ Set.Icc 0 (t + 1) from ⟨hbudget.1, by linarith only [hbudget.2]⟩)
  obtain ⟨_, hnEarly, hmEarly, hTest, hQ, _, _, hRequired⟩ :=
    hearly M nX Jalloc ht hD hdim hPdim hcost hRadius hGain hStride hPF hChart
      hChild hu hp hb
  change nativeEarly ∈ Set.Icc 0 w at hnEarly
  change massEarly ∈ Set.Icc 0 w at hmEarly
  change Ptest ∈ Set.Icc 0 w at hTest
  change max Ptest (2 * u + 4 * p + max 0 massEarly + 20) ∈ Set.Icc 0 w at hQ
  change actualForecastDataModelRequired budget nativeEarly massEarly u p ∈ Set.Icc 0 w at hRequired
  have hE0 : 0 ≤ Ecompare := by
    dsimp only [Ecompare]
    linarith only [hQ.1, hcost.1]
  have hE : Ecompare + 8 ≤ r := by
    dsimp only [Ecompare, r]
    linarith only [hQ.2, hcost.2, ht]
  have lift {a : ℝ} (ha : a ∈ Set.Icc 0 t) : a ∈ Set.Icc 0 r :=
    ⟨ha.1, ha.2.trans htr⟩
  obtain ⟨_, hnLate, hmLate⟩ := hlate M nX Jalloc hr (hD.trans htr) (hdim.trans htr)
    (lift hPdim) (lift hcost) (lift hRadius) (lift hGain) (lift hStride) (lift hPF)
    (lift hChart) (lift hChild) (show Ecompare + 8 ∈ Set.Icc 0 r from
      ⟨by linarith only [hE0], hE⟩)
  change nativeLate ∈ Set.Icc 0 z at hnLate
  change massLate ∈ Set.Icc 0 z at hmLate
  let a : ℝ := t + 3 * w + 7 * z + r + 16 + Ca
  have ha : 0 ≤ a := by dsimp only [a]; positivity
  have hmaxTest : max Ptest (3 * nativeLate + 3) ≤ w + 3 * z + 3 := by
    apply max_le
    · linarith only [hTest.2, hz]
    · linarith only [hnLate.2, hw]
  have hmax : max (max Pspatial (2 * max Ptest (3 * nativeLate + 3) + 1))
      (massLate + Ecompare + 8) + Ca ≤ a := by
    have hleft : max Pspatial (2 * max Ptest (3 * nativeLate + 3) + 1) ≤
        t + 3 * w + 7 * z + r + 16 := by
      apply max_le
      · linarith only [hSpatial.2, hw, hz, hr]
      · linarith only [hmaxTest, ht, hw, hz, hr]
    have hright : massLate + Ecompare + 8 ≤ t + 3 * w + 7 * z + r + 16 := by
      linarith only [hmLate.2, hE, ht, hw, hz]
    dsimp only [a]
    exact add_le_add (max_le hleft hright) (le_refl (Ca : ℝ))
  have hbase0 : 0 ≤ max (max Pspatial (2 * max Ptest (3 * nativeLate + 3) + 1))
      (massLate + Ecompare + 8) + Ca := by
    have h0 : 0 ≤ max (max Pspatial (2 * max Ptest (3 * nativeLate + 3) + 1))
        (massLate + Ecompare + 8) :=
      hSpatial.1.trans ((le_max_left _ _).trans (le_max_left _ _))
    exact add_nonneg h0 (Nat.cast_nonneg _)
  have hAmb0 : 0 ≤ ambient := pow_nonneg hbase0 _
  have hAmb : ambient ≤ a ^ Ca := pow_le_pow_left₀ hbase0 hmax _
  have hpower : 0 ≤ a ^ Ca := pow_nonneg ha _
  have hfinal : w + r + z + a ^ Ca ≤ (t + C) ^ C := by
    simpa [F, W, R, Z, X, w, r, z, a, Polynomial.eval₂_pow] using hbound t ht
  have hwFinal : w ≤ (t + C) ^ C := by linarith only [hfinal, hr, hz, hpower]
  have hrFinal : r ≤ (t + C) ^ C := by linarith only [hfinal, hw, hz, hpower]
  have hzFinal : z ≤ (t + C) ^ C := by linarith only [hfinal, hw, hr, hpower]
  refine ⟨⟨hTest.1, hTest.2.trans hwFinal⟩,
    ⟨hE0, (by linarith only [hE] : Ecompare ≤ r).trans hrFinal⟩,
    ⟨hnEarly.1, hnEarly.2.trans hwFinal⟩, ⟨hmEarly.1, hmEarly.2.trans hwFinal⟩,
    ⟨hnLate.1, hnLate.2.trans hzFinal⟩, ⟨hmLate.1, hmLate.2.trans hzFinal⟩,
    ⟨hRequired.1, hRequired.2.trans hwFinal⟩, hAmb0, ?_⟩
  linarith only [hAmb, hfinal, hw, hr, hz]

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedRelativeEndpointNumericalBounds
namespace OAI

section

namespace Erdos3.VectorPolynomial

noncomputable def preparedRelativeEndpointForecastExponent (m : ℕ) : ℕ :=
  (exists_preparedRelativeEndpointForecast_budget m).choose

noncomputable def preparedRelativeEndpointGeometryScale (m : ℕ) (t : ℝ) : ℝ :=
  t + (t + preparedRelativeEndpointForecastExponent m) ^
    preparedRelativeEndpointForecastExponent m + 1

noncomputable def preparedRelativeEndpointUniformKnob (m : ℕ) (t : ℝ) : ℝ :=
  let T := preparedRelativeEndpointGeometryScale m t
  4 * T + (T + preparedRelativeEndpointPerturbationExponent m) ^
    preparedRelativeEndpointPerturbationExponent m + (T + 10) ^ (2 * m + 20) + 20

theorem preparedRelativeEndpointGeometryScale_bounds (m : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    1 ≤ preparedRelativeEndpointGeometryScale m t ∧
    t ≤ preparedRelativeEndpointGeometryScale m t ∧
    (t + preparedRelativeEndpointForecastExponent m) ^
      preparedRelativeEndpointForecastExponent m ≤ preparedRelativeEndpointGeometryScale m t := by
  have hw : 0 ≤ (t + preparedRelativeEndpointForecastExponent m) ^
      preparedRelativeEndpointForecastExponent m := by positivity
  unfold preparedRelativeEndpointGeometryScale
  exact ⟨by linarith only [ht, hw], by linarith only [hw], by linarith only [ht]⟩

theorem exists_preparedRelativeEndpointUniformKnob_power_budget (m inputPower : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {x t : ℝ}, 0 ≤ x → t ∈ Set.Icc 0 ((x + 2) ^ inputPower) →
      preparedRelativeEndpointUniformKnob m t ≤ (x + 2) ^ C := by
  let Cf := preparedRelativeEndpointForecastExponent m
  let Cs := preparedRelativeEndpointPerturbationExponent m
  let X : Polynomial ℕ := Polynomial.X
  let P : Polynomial ℕ := (X + 2) ^ inputPower
  let T : Polynomial ℕ := P + (P + Polynomial.C Cf) ^ Cf + 1
  let K : Polynomial ℕ := 4 * T + (T + Polynomial.C Cs) ^ Cs +
    (T + 10) ^ (2 * m + 20) + 20
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_fixed_power_budget K
  refine ⟨C, hC, ?_⟩
  intro x t hx ht
  let p := (x + 2) ^ inputPower
  let b := p + (p + Cf) ^ Cf + 1
  have hp0 : 0 ≤ p := by dsimp only [p]; positivity
  have hT0 := zero_le_one.trans (preparedRelativeEndpointGeometryScale_bounds m ht.1).1
  have hT : preparedRelativeEndpointGeometryScale m t ≤ b := by
    unfold preparedRelativeEndpointGeometryScale
    exact add_le_add (add_le_add ht.2
      (pow_le_pow_left₀ (add_nonneg ht.1 (Nat.cast_nonneg _))
        (add_le_add ht.2 le_rfl) _)) le_rfl
  have hB : preparedRelativeEndpointUniformKnob m t ≤
      4 * b + (b + Cs) ^ Cs + (b + 10) ^ (2 * m + 20) + 20 := by
    unfold preparedRelativeEndpointUniformKnob
    exact add_le_add (add_le_add
      (add_le_add (mul_le_mul_of_nonneg_left hT (by norm_num))
        (pow_le_pow_left₀ (add_nonneg hT0 (Nat.cast_nonneg _))
          (add_le_add hT le_rfl) _))
      (pow_le_pow_left₀ (by linarith only [hT0]) (add_le_add hT le_rfl) _)) le_rfl
  apply hB.trans
  simpa [K, T, P, X, p, b, Polynomial.eval₂_pow] using hbound x hx

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

theorem exists_preparedRelativeEndpointInputScale_power_budget (m earlyPower : ℕ) :
    ∃ inputPower : ℕ, 2 ≤ inputPower ∧ ∀ {B : ℝ}, 0 ≤ B →
      preparedRelativeEndpointUniformKnob m (preparedRelativeEndpointInputScale m earlyPower B) ≤
        (B + 2) ^ inputPower := by
  let Cp := preparedRelativeEndpointPrimitiveExponent m
  let X : Polynomial ℕ := Polynomial.X
  let a : Polynomial ℕ := (X + 2) ^ earlyPower + X + 1
  let t : Polynomial ℕ := a + (a + Polynomial.C Cp) ^ Cp + 1
  obtain ⟨Cscale, _, hscale⟩ := exists_natPolynomial_fixed_power_budget t
  obtain ⟨C, hC, hknob⟩ := exists_preparedRelativeEndpointUniformKnob_power_budget m Cscale
  refine ⟨C, hC, ?_⟩
  intro B hB
  apply hknob hB
  constructor
  · exact zero_le_one.trans (preparedRelativeEndpointInputScale_bounds m earlyPower hB).1
  · simpa [t, a, X, preparedRelativeEndpointInputScale, preparedRelativeEndpointInputBase,
      Cp, Polynomial.eval₂_pow] using hscale B hB

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.CandidateNestedDegreeNetSchedule
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators

noncomputable def candidateNestedDegreeNetExponent (total initial : ℕ) : ℕ → ℕ
  | 0 => initial
  | j + 1 => RationalFilteredNilmanifold.refilteredQuotientNetExponent.{0, 0, 0}
      (total - (j + 1)) 1 (candidateNestedDegreeNetExponent total initial j) + 2

@[simp] theorem candidateNestedDegreeNetExponent_zero (total initial : ℕ) :
    candidateNestedDegreeNetExponent total initial 0 = initial := rfl

@[simp] theorem candidateNestedDegreeNetExponent_succ (total initial j : ℕ) :
    candidateNestedDegreeNetExponent total initial (j + 1) =
      RationalFilteredNilmanifold.refilteredQuotientNetExponent.{0, 0, 0}
        (total - (j + 1)) 1 (candidateNestedDegreeNetExponent total initial j) + 2 := rfl

noncomputable def candidateNestedDegreeConstantBound (total initial : ℕ)
    (requirement : ℕ → ℕ → ℕ) : ℕ :=
  ∑ j ∈ Finset.range (total + 1),
    requirement (total - j) (candidateNestedDegreeNetExponent total initial j)

theorem candidateNestedDegreeConstant_le_bound (total initial : ℕ)
    (requirement : ℕ → ℕ → ℕ) {j : ℕ} (hj : j ≤ total) :
    requirement (total - j) (candidateNestedDegreeNetExponent total initial j) ≤
      candidateNestedDegreeConstantBound total initial requirement := by
  unfold candidateNestedDegreeConstantBound
  exact Finset.single_le_sum (f := fun j =>
    requirement (total - j) (candidateNestedDegreeNetExponent total initial j))
    (fun _ _ => Nat.zero_le _)
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))

noncomputable def candidateNestedDegreeNetBound (total initial : ℕ) : ℕ :=
  candidateNestedDegreeConstantBound total initial (fun _ e => e)

theorem candidateNestedDegreeNetExponent_le_bound (total initial : ℕ)
    {j : ℕ} (hj : j ≤ total) :
    candidateNestedDegreeNetExponent total initial j ≤ candidateNestedDegreeNetBound total initial :=
  candidateNestedDegreeConstant_le_bound total initial (fun _ e => e) hj

end Erdos3.VectorPolynomial

end

end OAI
end


