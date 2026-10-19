-- Prove2me | Definitions.Def_OAIE3v2B246
-- name    : OAIE3v2B246
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-18T05:15:38.020486+00:00
-- url     : https://prove2.me/theorems/38f2fb52-6741-4104-a506-81fda6308387
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 251 of 311
-- statement:
--   Definitions bundle 251 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B301`, `OAIE3v2B223`, `OAIE3v2B225`, `OAIE3v2B226`, `OAIE3v2B230`, `OAIE3v2B231`, `OAIE3v2B232`, `OAIE3v2B233`, `OAIE3v2B234`, `OAIE3v2B235` of this split.
--
--   Modules: `Dynamics/SharedFreeCorrelationBudget.lean`, `Estimates/AllocatedAnchoredRecoveredSource.lean`, `Estimates/AllocatedCenteredNarrowPrescribedMarginal.lean`, `Estimates/AllocatedRecoveredPreparedFreeze.lean`, `Estimates/MixedPairComparison.lean`, `Estimates/MixedPreciseSampledExchange.lean`, `Estimates/NativeFrozenComparison.lean`, `Estimates/NativeProductVerticalization.lean`, `Estimates/PreparedCanonicalRelativeEndpointBounds.lean`, `Estimates/PreparedEnlargedModularAllocation.lean`, `Estimates/PreparedUniformEarlyRadiusWithCutoff.lean`, `Estimates/QuadraticAntisymmetricCorrelation.lean`, `Estimates/QuadraticPairStepDrop.lean`, `Geometry/AllocatedProductChartRadius.lean`, `Geometry/CertifiedFullChartFrozenTerminal.lean`, `Geometry/SharedWidthAllocatedDetectedSpatialNativeSourceGeneral.lean`, `Lattices/AllocatedCenteredBadPrimeSurrogate.lean`, `Lattices/AllocatedModularRankAffineFullWitness.lean`, `Lattices/AllocatedModularRankAffineProbability.lean`, `Linear/AllocatedCenteredMeasurableFramedBadTail.lean`, `Linear/AllocatedModularRankActualRead.lean`, `Linear/AllocatedModularRankBadProduct.lean`, `Linear/AllocatedModularRankCongruenceOutput.lean`, `Linear/AllocatedModularRankMixedUniform.lean`, `Linear/AllocatedModularRankPreparedBlocks.lean`, `Linear/AllocatedShortRankWitnessWidth.lean`, `Polynomial/AllocatedModularRankTaggedPolynomials.lean`, `Sampling/AllocatedRetainedActualForecastFactory.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B301
import Definitions.Def_OAIE3v2B223
import Definitions.Def_OAIE3v2B225
import Definitions.Def_OAIE3v2B226
import Definitions.Def_OAIE3v2B230
import Definitions.Def_OAIE3v2B231
import Definitions.Def_OAIE3v2B232
import Definitions.Def_OAIE3v2B233
import Definitions.Def_OAIE3v2B234
import Definitions.Def_OAIE3v2B235

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.SharedFreeCorrelationBudget
namespace OAI

section

namespace Erdos3

theorem exists_sharedFreeCorrelationBudget_bound (s : ℕ) (hs : 2 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ q p : ℝ, 0 ≤ q → q ≤ p → 0 ≤ p →
      let B := sharedFreeCorrelationBudget s hs p
      let Q := B + sharedFreeComparisonBasisBudget q p + 2
      (p + sharedFreeAffineConstant s) ^ sharedFreeAffineConstant s + B ≤ (p + C) ^ C ∧
      (Q + nativePairModelConstant s) ^ nativePairModelConstant s ≤ (p + C) ^ C ∧
      nativeLowerPairModelBudget s Q ≤ (p + C) ^ C := by
  obtain ⟨b, _, hb⟩ := exists_sharedFreeComparisonBasisBudget_bound
  obtain ⟨c, _, hc⟩ := exists_nativeLowerPairModelBudget_bound s
  let a := (exists_sharedFreeFullOrbitBudget_bound s).choose
  let d := sharedFreeFactorFreezingConstant s
  let e := sharedFactorCorrelationConstant s hs
  let f := sharedFreeAffineConstant s
  let T : Polynomial ℕ := Polynomial.X + (Polynomial.X + Polynomial.C a) ^ a +
    (Polynomial.X + Polynomial.C d) ^ d + 2
  let B : Polynomial ℕ := (T + Polynomial.C e) ^ e
  let Q : Polynomial ℕ := B + (Polynomial.X + Polynomial.C b) ^ b + 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((Polynomial.X + Polynomial.C f) ^ f + B + (Q + Polynomial.C c) ^ c)
  refine ⟨C, hC, ?_⟩
  intro q p hq hqp hp B₀ Q₀
  have hB₀ : 0 ≤ B₀ := by
    apply le_trans (show 0 ≤ sharedFreeCorrelationInput s p from
      (by linarith [(sharedFreeCorrelationInput_bounds s hq hqp hp).1]))
    exact sharedFreeCorrelationInput_le_budget s hs hp
  have hQ₀ : 0 ≤ Q₀ := by
    have := sharedFreeComparisonBasisBudget_nonneg hq hp
    dsimp only [Q₀]
    positivity
  let v := B₀ + (p + b) ^ b + 2
  have hQv : Q₀ ≤ v := by
    dsimp only [Q₀, v]
    linarith [hb q p hq hqp hp]
  have hv : 0 ≤ v := hQ₀.trans hQv
  have hΛ : 0 ≤ (p + f) ^ f := by positivity
  have hsum : (p + f) ^ f + B₀ + (v + c) ^ c ≤ (p + C) ^ C := by
    change (p + f) ^ f + (p + (p + a) ^ a + (p + d) ^ d + 2 + e) ^ e +
      ((p + (p + a) ^ a + (p + d) ^ d + 2 + e) ^ e + (p + b) ^ b + 2 + c) ^ c ≤ _
    simpa [T, B, Q, Polynomial.eval₂_pow] using hbudget p hp
  have htail : (v + c) ^ c ≤ (p + C) ^ C := by linarith
  have hfirst : (p + f) ^ f + B₀ ≤ (p + C) ^ C := by
    linarith [show 0 ≤ (v + c) ^ c by positivity]
  have hpow : (Q₀ + c) ^ c ≤ (v + c) ^ c :=
    pow_le_pow_left₀ (by positivity) (by linarith) c
  exact ⟨hfirst, (hc Q₀ hQ₀).1.trans (hpow.trans htail),
    (hc Q₀ hQ₀).2.trans (hpow.trans htail)⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeProductVerticalization
namespace OAI

section

namespace Erdos3

open scoped TensorProduct BigOperators

attribute [local instance] NativeBoundedMultidegreeFamily.lie NativeBoundedMultidegreeFamily.algebra
  NativeBoundedMultidegreeFamily.topology NativeBoundedMultidegreeFamily.topologicalAdd
  NativeBoundedMultidegreeFamily.continuousSMul NativeBoundedMultidegreeFamily.hausdorff

theorem exists_native_mixed_of_bounded (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {I : Type*} {N : ℕ} [NeZero N] {p : ℝ}, 0 ≤ p →
      ∀ (f : ZMod N → ℂ), (∀ x, ‖f x‖ ≤ 1) →
      ∀ H : Finset (ZMod N), H.Nonempty → Real.exp (-p) * N ≤ (H.card : ℝ) →
      ∀ (F : NativeBoundedMultidegreeFamily (mixedCorrelationDegree s) I p) (i : I),
      (∀ h ∈ H, Real.exp (-p) ≤ ‖𝔼 n : ZMod N, multiplicativeDerivative f h n *
        star (F.eval i (correlationInput (h.val : ℤ) (n.val : ℤ)))‖) →
      Nonempty (NativeMixedCorrelation s N ((p + C) ^ C) f) := by
  obtain ⟨A, _, hselect⟩ := RationalFilteredNilmanifold.exists_common_unit_vertical_correlators
    (∑ j, mixedCorrelationDegree s j)
  let X : Polynomial ℕ := Polynomial.X
  let Q : Polynomial ℕ := (X + Polynomial.C A) ^ A
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (X + Q + 2)
  refine ⟨C, hC, ?_⟩
  intro I N _ p hp f hf H hH hdense F i hcorr
  let q := (p + A) ^ A
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have htotal : p + q + 2 ≤ (p + C) ^ C := by
    simpa [X, Q, q, Polynomial.eval₂_pow] using hbudget p hp
  have hpR : p ≤ (p + C) ^ C := by linarith
  have hqR : q ≤ (p + C) ^ C := by linarith
  have htwo : 2 ≤ (p + C) ^ C := by linarith
  let T (h : ZMod N) := F.slice i (h.val : ℤ)
  have hweight (h x : ZMod N) : ‖multiplicativeDerivative f h x‖ ≤ 1 := by
    simp only [multiplicativeDerivative, norm_mul, norm_star]
    exact (mul_le_mul (hf x) (hf (x + h)) (norm_nonneg _) (by norm_num)).trans_eq (one_mul 1)
  have hTcorr (h : ZMod N) (hh : h ∈ H) : Real.exp (-p) ≤
      ‖𝔼 x : ZMod N, multiplicativeDerivative f h x * star ((T h).evalCyclic N (fun _ => x))‖ := by
    simpa only [T, RationalFilteredNilmanifold.Niltest.evalCyclic, NativeBoundedMultidegreeFamily.slice_eval]
      using hcorr h hh
  obtain ⟨J, hJH, hJ, hJdense, n, _, hn, V, hVcorr⟩ :=
    hselect F.model T H hH hp (fun h _ => F.slice_complexity i h.val)
      (fun h _ => (F.slice_norm i h.val).le)
      (fun h k => (F.slice_observable i h.val).trans (F.slice_observable i k.val).symm)
      (multiplicativeDerivative f) (fun h _ x => hweight h x) hTcorr
  have hnR : (n + 1 : ℝ) ≤ Real.exp ((p + C) ^ C) := hn.trans (Real.exp_le_exp.mpr hqR)
  let M := F.toNilcharacter hpR hnR (V.mono hqR)
  have hMeval (h x : ZMod N) : M.evalCyclic N (0 : Fin (n + 1)) (correlationInput h x) =
      V.observable 0 (QuotientGroup.mk (F.model.filtration.realification.polynomialOrbitEval
        (fun _ : Unit => 1) (fun _ => (x.val : ℤ)) (T h).orbit)) := by
    have hinput : (fun j => ((correlationInput h x j).val : ℤ)) =
        correlationInput (h.val : ℤ) (x.val : ℤ) := by
      funext j
      exact Fin.cases rfl (fun _ => rfl) j
    change M.eval (0 : Fin (n + 1)) (fun j => ((correlationInput h x j).val : ℤ)) = _
    rw [hinput]
    change V.observable 0 (QuotientGroup.mk (F.multi.filtration.realification.polynomialOrbitEval
      (correlationInput (h.val : ℤ) (x.val : ℤ)) F.orbit)) = _
    rw [F.slice_orbit_eval i (h.val : ℤ)]
  refine ⟨{ shifts := J, nonempty := hJ, density := ?_, mixed := M, correlation := ?_ }⟩
  · simp only [ZMod.card]
    calc
      Real.exp (-((p + C) ^ C)) * N ≤ Real.exp (-(p + q)) * N :=
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by linarith)) (Nat.cast_nonneg _)
      _ = Real.exp (-q) * (Real.exp (-p) * N) := by
        rw [← mul_assoc, ← Real.exp_add]
        congr 2
        ring
      _ ≤ Real.exp (-q) * H.card := mul_le_mul_of_nonneg_left hdense (Real.exp_nonneg _)
      _ ≤ J.card := hJdense
  · intro h hh
    apply NativeVectorCorrelation.exists_of_mean (s - 1) N (nativeMixedResidual f M h) htwo
    refine ⟨(0 : Fin (n + 1)), ?_⟩
    change Real.exp (-((p + C) ^ C)) ≤
      ‖𝔼 x : ZMod N, multiplicativeDerivative f h x *
        star (M.evalCyclic N (0 : Fin (n + 1)) (correlationInput h x))‖
    simp only [hMeval]
    exact (Real.exp_le_exp.mpr (neg_le_neg hqR)).trans (hVcorr h hh)

end Erdos3

end

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

attribute [local instance] NativeUnitRankFamily.lie NativeUnitRankFamily.algebra
  NativeUnitRankFamily.topology NativeUnitRankFamily.topologicalAdd
  NativeUnitRankFamily.continuousSMul NativeUnitRankFamily.hausdorff
  NativeBoundedMultidegreeFamily.lie NativeBoundedMultidegreeFamily.algebra
  NativeBoundedMultidegreeFamily.topology NativeBoundedMultidegreeFamily.topologicalAdd
  NativeBoundedMultidegreeFamily.continuousSMul NativeBoundedMultidegreeFamily.hausdorff

theorem exists_native_fixed_product_unit_data (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {I K : Type} [Fintype I] {r N : ℕ} [NeZero N]
      {p : ℝ} {f : ZMod N → ℂ} (J : Finset (ZMod N))
      (F : NativeUnitRankFamily (fun _ : Unit => 1) s r {h // h ∈ J} I p)
      (M : NativeBoundedMultidegreeFamily (mixedCorrelationDegree s) K p)
      (iF : I) (iM : K) (H : Finset {h // h ∈ J}), H.Nonempty →
      0 ≤ p → (∀ x, ‖f x‖ ≤ 1) →
      (∀ h ∈ H, Nonempty (NativeVectorCorrelation (s - 1) N p (fun _ : Unit => fun x =>
        multiplicativeDerivative f h.val x * star (M.eval iM
          (correlationInput (h.val.val : ℤ) (x.val : ℤ))) *
          star (F.eval h iF (fun _ => (x.val : ℤ)))))) →
      ∃ H' : Finset {h // h ∈ J}, H' ⊆ H ∧ H'.Nonempty ∧
        Real.exp (-((p + C) ^ C)) * H.card ≤ (H'.card : ℝ) ∧
        ∃ n₁ : ℕ, 0 < n₁ ∧ (n₁ + 1 : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
          ∃ V₁ : F.model.UnitVerticalObservable (F.model.filtration.realification.subgroup s)
              (Fin (n₁ + 1)) ((p + C) ^ C),
            ∃ n₂ : ℕ, 0 < n₂ ∧ (n₂ + 1 : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
              ∃ V₂ : M.model.UnitVerticalObservable
                  (M.model.filtration.realification.subgroup (∑ i, mixedCorrelationDegree s i))
                  (Fin (n₂ + 1)) ((p + C) ^ C),
                ∀ h ∈ H', Nonempty (NativeVectorCorrelation (s - 1) N ((p + C) ^ C)
                  (fun _ : Unit => fun x => multiplicativeDerivative f h.val x *
                    star (V₂.observable 0 (QuotientGroup.mk
                      (M.model.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1)
                        (fun _ => (x.val : ℤ)) (M.slice iM (h.val.val : ℤ)).orbit))) *
                    star (V₁.observable 0 (QuotientGroup.mk
                      (F.model.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1)
                        (fun _ => (x.val : ℤ)) ((F.test iF).withOrbit (F.orbit h)).orbit))))) := by
  obtain ⟨C, hC, hselect⟩ := exists_native_two_factor_unit_replacement s
    (∑ i, mixedCorrelationDegree s i) (s - 1)
  refine ⟨C, hC, ?_⟩
  intro I K _ r N _ p f J F M iF iM H hH hp hf hcorr
  let T (h : {h // h ∈ J}) := (F.test iF).withOrbit (F.orbit h)
  let S (h : {h // h ∈ J}) := M.slice iM (h.val.val : ℤ)
  have hmodels := by
    as_aux_lemma =>
      exact hselect (G := {h // h ∈ J}) F.model M.model
  have htests := by
    as_aux_lemma =>
      exact hmodels T S H hH hp
  have hbounded := by
    as_aux_lemma =>
      exact htests
        (fun h _ => ((F.test iF).withOrbit_complexity (F.orbit h) p).mpr (F.test_complexity iF))
        (fun h _ => M.slice_complexity iM (h.val.val : ℤ))
        (fun _ _ => (F.test_norm iF).le) (fun h _ => (M.slice_norm iM (h.val.val : ℤ)).le)
  have hcommon := by
    as_aux_lemma =>
      exact hbounded (N := N)
        (fun h k => (F.withOrbit_observable iF h).trans (F.withOrbit_observable iF k).symm)
        (fun h k => (M.slice_observable iM (h.val.val : ℤ)).trans
          (M.slice_observable iM (k.val.val : ℤ)).symm)
  have hweights := by
    as_aux_lemma =>
      exact hcommon (fun h x => multiplicativeDerivative f h.val x)
        (fun h _ x => multiplicativeDerivative_norm_le_one f hf h.val x)
  apply hweights
  intro h hh
  exact exists_native_sliced_product_correlation F M iF iM h (hcorr h hh)

theorem exists_native_fixed_product_verticalization (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {I K : Type} [Fintype I] {r N : ℕ} [NeZero N]
      {p : ℝ} {f : ZMod N → ℂ} (J : Finset (ZMod N))
      (F : NativeUnitRankFamily (fun _ : Unit => 1) s r {h // h ∈ J} I p)
      (M : NativeBoundedMultidegreeFamily (mixedCorrelationDegree s) K p)
      (iF : I) (iM : K) (H : Finset {h // h ∈ J}), H.Nonempty →
      0 ≤ p → (∀ x, ‖f x‖ ≤ 1) → Real.exp (-p) * N ≤ (H.card : ℝ) →
      (∀ h ∈ H, Nonempty (NativeVectorCorrelation (s - 1) N p (fun _ : Unit => fun x =>
        multiplicativeDerivative f h.val x * star (M.eval iM
          (correlationInput (h.val.val : ℤ) (x.val : ℤ))) *
          star (F.eval h iF (fun _ => (x.val : ℤ)))))) →
      Nonempty (NativeCorrelationStructure s r N ((p + C) ^ C) f) := by
  obtain ⟨a, _, hselect⟩ := exists_native_fixed_product_unit_data s
  let X : Polynomial ℕ := Polynomial.X
  let Q : Polynomial ℕ := (X + Polynomial.C a) ^ a
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (X + Q + 2)
  refine ⟨C, hC, ?_⟩
  intro I K _ r N _ p f J F M iF iM H hH hp hf hdense hcorr
  obtain ⟨H₁, _, hH₁, hdense₁, n₁, _, hcount₁, V₁, n₂, _, hcount₂, V₂, hunit⟩ :=
    hselect J F M iF iM H hH hp hf hcorr
  let q := (p + a) ^ a
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have htotal : p + q + 2 ≤ (p + C) ^ C := by
    simpa [X, Q, q, Polynomial.eval₂_pow] using hbudget p hp
  have hpC : p ≤ (p + C) ^ C := by linarith
  have hqC : q ≤ (p + C) ^ C := by linarith
  have hfinaldensity : Real.exp (-((p + C) ^ C)) * N ≤ (H₁.card : ℝ) := by
    calc
      _ ≤ Real.exp (-(p + q)) * N :=
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by linarith)) (Nat.cast_nonneg _)
      _ = Real.exp (-q) * (Real.exp (-p) * N) := by
        rw [← mul_assoc, ← Real.exp_add]
        congr 2
        ring
      _ ≤ Real.exp (-q) * H.card := mul_le_mul_of_nonneg_left hdense (Real.exp_nonneg _)
      _ ≤ _ := hdense₁
  exact exists_native_correlation_of_sliced_unit_products J F M iM H₁ hH₁
    hfinaldensity hpC hqC hcount₁ hcount₂ V₁ V₂ hunit

end Erdos3

end

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

attribute [local instance] NativeUnitRankFamily.lie NativeUnitRankFamily.algebra
  NativeUnitRankFamily.topology NativeUnitRankFamily.topologicalAdd
  NativeUnitRankFamily.continuousSMul NativeUnitRankFamily.hausdorff
  NativeBoundedMultidegreeFamily.lie NativeBoundedMultidegreeFamily.algebra
  NativeBoundedMultidegreeFamily.topology NativeBoundedMultidegreeFamily.topologicalAdd
  NativeBoundedMultidegreeFamily.continuousSMul NativeBoundedMultidegreeFamily.hausdorff

theorem exists_native_product_verticalization (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {I : Type} [Fintype I] {r N : ℕ} [NeZero N]
      {p : ℝ} {f : ZMod N → ℂ} (J : Finset (ZMod N)) (mixedDim : ℕ),
      0 ≤ p → (∀ x, ‖f x‖ ≤ 1) → J.Nonempty →
      Real.exp (-p) * N ≤ (J.card : ℝ) →
      (mixedDim : ℝ) ≤ Real.exp p → (Fintype.card I : ℝ) ≤ Real.exp p →
      HasBoundedProductCorrelation (I := I) (s := s) (r := r) (degree := s - 1)
        (fun h : {h // h ∈ J} => h.val) (fun h x => multiplicativeDerivative f h.val x)
        mixedDim p p p →
      Nonempty (NativeCorrelationStructure s r N ((p + C) ^ C) f) := by
  obtain ⟨a, _, hselect⟩ := exists_native_fixed_product_verticalization s
  let X : Polynomial ℕ := Polynomial.X
  let Q : Polynomial ℕ := (7 * X + 2 + Polynomial.C a) ^ a
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget Q
  refine ⟨C, hC, ?_⟩
  intro I _ r N _ p f J mixedDim hp hf hJ hdense hmixed hI hproduct
  classical
  obtain ⟨k, hk, hkB, F, M, hcorr⟩ := hproduct
  let G := {h // h ∈ J}
  have hG : (Finset.univ : Finset G).Nonempty := by
    obtain ⟨h, hh⟩ := hJ
    exact ⟨⟨h, hh⟩, Finset.mem_univ _⟩
  have hlabels : (Fintype.card ((Fin mixedDim × Fin k) × ((I × I) × (I × Fin k))) : ℝ) ≤
      Real.exp (6 * p) := by
    simp only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul]
    calc
      _ ≤ (Real.exp p * Real.exp p) *
          ((Real.exp p * Real.exp p) * (Real.exp p * Real.exp p)) := by gcongr
      _ = Real.exp (6 * p) := by
        repeat rw [← Real.exp_add]
        congr 1
        ring
  obtain ⟨ij, H₀, _, hH₀, hdense₀, hfixed⟩ := NativeVectorCorrelation.exists_fixed_coordinate
    (p := p + 1) (Finset.univ : Finset G) hG _ hlabels (fun h _ => hcorr h)
  rcases ij with ⟨iM, iF⟩
  let P := 7 * p + 2
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hpP : p ≤ P := by dsimp [P]; linarith
  have hp₁P : p + 1 ≤ P := by dsimp [P]; linarith
  have hfinal : (P + a) ^ a ≤ (p + C) ^ C := by
    simpa [X, Q, P, Polynomial.eval₂_pow] using hbudget p hp
  have hfiber : Real.exp (-(6 * p)) * J.card ≤ (H₀.card : ℝ) := by
    simpa only [G, Finset.card_univ, Fintype.card_coe] using hdense₀
  have hfixeddensity : Real.exp (-P) * N ≤ (H₀.card : ℝ) := by
    calc
      _ ≤ Real.exp (-(7 * p)) * N :=
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by dsimp [P]; linarith))
          (Nat.cast_nonneg _)
      _ = Real.exp (-(6 * p)) * (Real.exp (-p) * N) := by
        rw [← mul_assoc, ← Real.exp_add]
        congr 2
        ring
      _ ≤ Real.exp (-(6 * p)) * J.card :=
        mul_le_mul_of_nonneg_left hdense (Real.exp_nonneg _)
      _ ≤ _ := hfiber
  have hselected := hselect J (F.mono hpP) (M.mono hpP) iF iM H₀ hH₀ hP hf hfixeddensity
  have hselected' : Nonempty (NativeCorrelationStructure s r N ((P + a) ^ a) f) := by
    apply hselected
    intro h hh
    obtain ⟨Wh⟩ := hfixed h hh
    exact ⟨Wh.mono hp₁P⟩
  obtain ⟨W⟩ := hselected'
  exact ⟨W.mono hfinal⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.QuadraticAntisymmetricCorrelation
namespace OAI

section

namespace Erdos3

open scoped TensorProduct BigOperators

attribute [local instance] NativeTwoVariableSplit.lie NativeTwoVariableSplit.algebra
  NativeTwoVariableSplit.topology NativeTwoVariableSplit.topologicalAdd
  NativeTwoVariableSplit.continuousSMul NativeTwoVariableSplit.hausdorff

theorem exists_linear_separated_approximation :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L : Type} [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {d : ℕ} {D : RationalFilteredNilmanifold L 1 d} {p : ℝ}
      (T : D.Niltest (fun _ : Fin 2 => 1)), T.ComplexityLE p → T.normBound ≤ 1 →
      ∀ epsilon : ℝ, 0 < epsilon → 1 / epsilon ≤ Real.exp ((p + 2) ^ 2) →
      ∃ r : ℕ, 0 < r ∧ (r : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∃ A B : Fin r → ℤ → ℂ,
          (∀ j x, ‖A j x‖ ≤ 1) ∧ (∀ j y, ‖B j y‖ ≤ 1) ∧
          ∀ x y, ‖T.eval ![x, y] - ∑ j, A j x * B j y‖ ≤ epsilon := by
  obtain ⟨C, hC, hsplit⟩ := exists_totalDegree_niltest_splitting 1 2
  refine ⟨C, hC, ?_⟩
  intro L _ _ _ _ _ _ d D p T hT hnorm epsilon hepsilon hscale
  obtain ⟨R⟩ := hsplit T hT hnorm epsilon hepsilon hscale
  let A (j : Fin R.count) (x : ℤ) := (R.test true j).eval ![x, 0]
  let B (j : Fin R.count) (y : ℤ) := (R.test false j).eval ![0, y]
  refine ⟨R.count, R.count_pos, R.count_bound, A, B, ?_, ?_, ?_⟩
  · intro j x
    exact ((R.test true j).norm_eval_le _).trans
      (show ((R.test true j).normBound : ℝ) ≤ 1 from R.test_norm true j)
  · intro j y
    exact ((R.test false j).norm_eval_le _).trans
      (show ((R.test false j).normBound : ℝ) ≤ 1 from R.test_norm false j)
  · intro x y
    have heq (j : Fin R.count) :
        (R.test false j).eval ![x, y] * (R.test true j).eval ![x, y] = A j x * B j y := by
      rw [R.first_eval_eq j ![x, y] ![0, y] rfl,
        R.second_eval_eq_degree_one j ![x, y] ![x, 0] rfl]
      exact mul_comm _ _
    simpa only [heq] using R.approximation ![x, y]

theorem exists_absorb_linear_error :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L : Type} [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {d : ℕ} {D : RationalFilteredNilmanifold L 1 d} {p : ℝ}
      (T : D.Niltest (fun _ : Fin 2 => 1)), T.ComplexityLE p →
      ∀ {X : Type*} (S : Finset X), S.Nonempty → ∀ (x y : X → ℤ) (F : X → ℂ),
        (∀ u ∈ S, ‖F u‖ ≤ 1) →
        Real.exp (-p) ≤ ‖𝔼 u ∈ S, F u * T.eval ![x u, y u]‖ →
        ∃ A B : ℤ → ℂ, (∀ x, ‖A x‖ ≤ 1) ∧ (∀ y, ‖B y‖ ≤ 1) ∧
          Real.exp (-((p + C) ^ C)) ≤ ‖𝔼 u ∈ S, F u * A (x u) * B (y u)‖ := by
  obtain ⟨a, _, hsplit⟩ := exists_linear_separated_approximation
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (2 * X + (X + Polynomial.C a) ^ a + 1)
  refine ⟨C, hC, ?_⟩
  intro L _ _ _ _ _ _ d D p T hT Ω S hS x y F hF hcorr
  have hp : 0 ≤ p := (Nat.cast_nonneg d).trans hT.1.1
  let U := T.conjugate.expNormalize p
  let epsilon := Real.exp (-(2 * p + 1))
  have hscale : 1 / epsilon ≤ Real.exp ((p + 2) ^ 2) := by
    dsimp [epsilon]
    rw [one_div, ← Real.exp_neg]
    apply Real.exp_le_exp.mpr
    nlinarith [sq_nonneg p]
  obtain ⟨r, _, hr, A, B, hA, hB, happ⟩ := hsplit U
    (T.conjugate.expNormalize_complexity hT) (T.conjugate.expNormalize_norm hT)
    epsilon (Real.exp_pos _) hscale
  have hmean : (𝔼 u ∈ S, F u * star (U.eval ![x u, y u])) =
      (Real.exp (-p) : ℂ) * (𝔼 u ∈ S, F u * T.eval ![x u, y u]) := by
    rw [Finset.mul_expect]
    apply Finset.expect_congr rfl
    intro u _
    simp only [U, RationalFilteredNilmanifold.Niltest.expNormalize_eval,
      RationalFilteredNilmanifold.Niltest.eval_conjugate, star_mul,
      Complex.star_def, Complex.conj_ofReal, Complex.conj_conj]
    ring
  have hnorm : Real.exp (-(2 * p)) ≤ ‖𝔼 u ∈ S, F u * star (U.eval ![x u, y u])‖ := by
    rw [hmean, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_nonneg _)]
    calc
      _ = Real.exp (-p) * Real.exp (-p) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hcorr (Real.exp_nonneg _)
  have hepsilon : epsilon ≤ Real.exp (-(2 * p)) / 2 := by
    simpa only [epsilon, show -(2 * p + 1) = -(2 * p) - 1 by ring] using
      exp_sub_one_le_half_exp (-(2 * p))
  obtain ⟨j, hj⟩ := exists_correlating_summand hS F (fun u => U.eval ![x u, y u])
    (fun j u => A j (x u) * B j (y u)) (Real.exp_pos (-(2 * p)))
    (Real.exp_pos ((p + a) ^ a)) (by simpa only [Fintype.card_fin] using hr) hF
    (fun u _ => by rw [norm_sub_rev]; exact (happ (x u) (y u)).trans hepsilon) hnorm
  have hcost : 2 * p + (p + a) ^ a + 1 ≤ (p + C) ^ C := by
    simpa [X, Polynomial.eval₂_pow] using hbudget p hp
  have hsmall : Real.exp (-((p + C) ^ C)) ≤
      Real.exp (-(2 * p)) / (2 * Real.exp ((p + a) ^ a)) := by
    calc
      _ ≤ Real.exp (-(2 * p + (p + a) ^ a) - 1) := Real.exp_le_exp.mpr (by linarith)
      _ ≤ Real.exp (-(2 * p + (p + a) ^ a)) / 2 := exp_sub_one_le_half_exp _
      _ = _ := by rw [show -(2 * p + (p + a) ^ a) = -(2 * p) - (p + a) ^ a by ring,
        Real.exp_sub]; ring
  refine ⟨(fun x => star (A j x)), (fun y => star (B j y)), ?_, ?_, ?_⟩
  · intro x
    simpa only [norm_star] using hA j x
  · intro y
    simpa only [norm_star] using hB j y
  · simpa only [finiteCorrelation, star_mul, mul_assoc, mul_comm, mul_left_comm] using hsmall.trans hj

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

attribute [local instance] NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

theorem exists_integer_antisymmetric_correlation :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p) (z : ℤ)
      (i j : Fin W.outputDim) {Ω : Type*} (S : Finset Ω), S.Nonempty →
      ∀ (x y : Ω → ℤ) (a b : ℤ → ℂ), (∀ n, ‖a n‖ ≤ 1) → (∀ n, ‖b n‖ ≤ 1) →
      Real.exp (-p) ≤ ‖𝔼 u ∈ S,
        W.eval i (correlationInput (x u) (z - x u - y u)) *
          star (W.eval j (correlationInput (y u) (z - x u - y u))) * a (x u) * b (y u)‖ →
      ∃ (i' j' : Fin W.outputDim) (A B : ℤ → ℂ),
        (∀ n, ‖A n‖ ≤ 1) ∧ (∀ n, ‖B n‖ ≤ 1) ∧
        Real.exp (-((p + C) ^ C)) ≤ ‖𝔼 u ∈ S,
          star (W.eval i' (correlationInput (x u) (y u))) *
            W.eval j' (correlationInput (y u) (x u)) * A (x u) * B (y u)‖ := by
  obtain ⟨c, _, hcompare⟩ := NativeMultidegreeNilcharacter.exists_reflected_pair_equivalence
  obtain ⟨d, _, habsorb⟩ := exists_absorb_linear_error
  let X : Polynomial ℕ := Polynomial.X
  let Q := (X + Polynomial.C c) ^ c
  let R := X + 2 * Q + 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((R + Polynomial.C d) ^ d)
  refine ⟨C, hC, ?_⟩
  intro p W z i j Ω S hS x y a b ha hb hcorr
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  let q := (p + c) ^ c
  let r := p + 2 * q + 2
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hqr : q ≤ r := by dsimp [r]; linarith
  have hpr : p + 2 * q ≤ r := by dsimp [r]; linarith
  let E := (hcompare W z).conjugate
  have hunit (u : Ω) : (∑ k : (Fin W.outputDim × Fin W.outputDim) ×
      (Fin W.outputDim × Fin W.outputDim), ‖star (W.eval k.1.1 (correlationInput (x u) (z - x u)) *
      star (W.eval k.2.1 (correlationInput (y u) (z - y u))) *
      star (W.eval k.1.2 (correlationInput (x u) (y u))) *
      W.eval k.2.2 (correlationInput (y u) (x u)))‖ ^ 2) = 1 := by
    simpa only [norm_star] using W.reflected_pair_target_unit z (x u) (y u)
  obtain ⟨k, l, htransfer⟩ := E.transfer_sample_correlation S (fun u => ![x u, y u])
    (i, j) (fun u => a (x u) * b (y u)) (fun u _ => hunit u)
    (by simpa only [star_star, Matrix.cons_val_zero, Matrix.cons_val_one,
      mul_assoc, mul_comm, mul_left_comm] using hcorr)
  let T := (E.selectedExpansion (i, j) k).test l
  let a₀ (n : ℤ) := W.eval k.1.1 (correlationInput n (z - n)) * a n
  let b₀ (n : ℤ) := star (W.eval k.2.1 (correlationInput n (z - n))) * b n
  let F (u : Ω) := (star (W.eval k.1.2 (correlationInput (x u) (y u))) *
    W.eval k.2.2 (correlationInput (y u) (x u))) * a₀ (x u) * b₀ (y u)
  have ha₀ (n : ℤ) : ‖a₀ n‖ ≤ 1 := by
    rw [show a₀ n = W.eval k.1.1 (correlationInput n (z - n)) * a n from rfl, norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (W.norm_eval _ _)).trans (ha n)
  have hb₀ (n : ℤ) : ‖b₀ n‖ ≤ 1 := by
    simp only [b₀, norm_mul, norm_star]
    exact (mul_le_of_le_one_left (norm_nonneg _) (W.norm_eval _ _)).trans (hb n)
  have hF (u : Ω) : ‖F u‖ ≤ 1 := by
    simp only [F, norm_mul, norm_star]
    refine (mul_le_of_le_one_left (norm_nonneg _) ?_).trans (hb₀ _)
    refine (mul_le_of_le_one_left (norm_nonneg _) ?_).trans (ha₀ _)
    exact (mul_le_of_le_one_left (norm_nonneg _) (W.norm_eval _ _)).trans (W.norm_eval _ _)
  have hT : T.conjugate.ComplexityLE r := ((E.selectedExpansion (i, j) k).complexity l).mono hqr
  have hFcorr : Real.exp (-r) ≤ ‖𝔼 u ∈ S, F u * T.conjugate.eval ![x u, y u]‖ := by
    have hlarge := (Real.exp_le_exp.mpr (neg_le_neg hpr)).trans htransfer
    simpa only [F, a₀, b₀, T, E, RationalFilteredNilmanifold.Niltest.eval_conjugate,
      Matrix.cons_val_zero, Matrix.cons_val_one, star_star,
      mul_assoc, mul_comm, mul_left_comm] using hlarge
  obtain ⟨A, B, hA, hB, hAB⟩ := habsorb T.conjugate hT S hS x y F (fun u _ => hF u) hFcorr
  have hcost : (r + d) ^ d ≤ (p + C) ^ C := by
    simpa [X, Q, R, q, r, Polynomial.eval₂_pow] using hbudget p hp
  refine ⟨k.1.2, k.2.2, (fun n => a₀ n * A n), (fun n => b₀ n * B n), ?_, ?_, ?_⟩
  · intro n
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (ha₀ n)).trans (hA n)
  · intro n
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hb₀ n)).trans (hB n)
  · simpa only [F, mul_assoc, mul_comm, mul_left_comm] using
      (Real.exp_le_exp.mpr (neg_le_neg hcost)).trans hAB

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.QuadraticPairStepDrop
namespace OAI

section

namespace Erdos3

open Module RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff
  NativeSampleCorrelation.lie NativeSampleCorrelation.algebra
  NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd
  NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

theorem exists_antisymmetric_pair_orbit_factors :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q r : ℝ}
      {W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p}
      {N : ℕ} [NeZero N] {i j : Fin W.outputDim}
      {V : NativeSampleCorrelation (fun _ : Fin 2 => 1) 1 q
        Finset.univ (fun z : Fin 2 → ZMod N => fun k => ((z k).val : ℤ))
        (fun z => W.antisymmetricKernel i j ((z 0).val : ℤ) ((z 1).val : ℤ))}
      (_F : NativeAntisymmetricPairFactorization V r), 0 ≤ r →
      Real.exp ((p + q + r + C) ^ C) ≤ (N : ℝ) →
      Nonempty (NativePolynomialOrbitFactors (pi V.antisymmetricPairModels)
        V.antisymmetricPairPolynomial (piFrequency V.antisymmetricPairFrequencies)
        (fun _ : Fin 2 => (N : ℝ)) ((p + q + r + C) ^ C)) := by
  obtain ⟨a, _, hconstruct⟩ := exists_native_polynomial_orbit_factors
    (∑ k, mixedCorrelationDegree 1 k)
  let X : Polynomial ℕ := Polynomial.X
  let B := X + (X + (X + 2) ^ 2 + 3) + 4
  let T := (B + 2) ^ 2 + B + (B + (B ^ 2 + B + 3) ^ 2) + B ^ 2 + 4 + X + 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((T + Polynomial.C a) ^ a)
  refine ⟨C, hC, ?_⟩
  intro p q r W N _ i j V F hr hN
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  have hq : 0 ≤ q := (Nat.cast_nonneg V.dim).trans V.complexity.1.1
  let u := p + q + r
  let b := u + raisedNiltestBudget u + 4
  let t := productNiltestBudget b + u + 2
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hpqu : p + q ≤ u := le_add_of_nonneg_right hr
  have hb : 0 ≤ b := by dsimp [b, raisedNiltestBudget]; positivity
  have hprod : 0 ≤ productNiltestBudget b := by
    unfold productNiltestBudget productObservableLipBudget
    positivity
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hrt : r ≤ t := by dsimp [t, u]; linarith
  have h2t : 2 ≤ t := by dsimp [t]; linarith
  have hBt : antisymmetricPairBudget p q ≤ b := by
    dsimp [antisymmetricPairBudget, b, raisedNiltestBudget]
    gcongr
  have hB0 : 0 ≤ antisymmetricPairBudget p q :=
    (by norm_num : (0 : ℝ) ≤ 4).trans V.antisymmetricPairBudget_four_le
  have hprodmono : productNiltestBudget (antisymmetricPairBudget p q) ≤ productNiltestBudget b := by
    unfold productNiltestBudget productObservableLipBudget
    gcongr
  have htest : productNiltestBudget (antisymmetricPairBudget p q) ≤ t :=
    hprodmono.trans (by dsimp [t]; linarith)
  have hcost : (t + a) ^ a ≤ (p + q + r + C) ^ C := by
    simpa [X, B, T, t, b, u, raisedNiltestBudget, productNiltestBudget,
      productObservableLipBudget, Polynomial.eval₂_pow] using hbudget u hu
  let := F.topology
  let := F.topologicalAdd
  let := F.continuousSMul
  let := F.hausdorff
  let D := pi V.antisymmetricPairModels
  have hfactor : D.filtration.ControlledSymbolFactorization F.basis F.weight F.adapted
      (piFrequency V.antisymmetricPairFrequencies) (fun _ : Fin 2 => (N : ℝ))
      (D.filtration.realPolynomialSymbolHom F.basis F.weight F.adapted
        (fun _ => 1) V.antisymmetricPairPolynomial) t := by
    have h := F.factorization
    rw [V.antisymmetricPairNiltest_symbol] at h
    exact NilpotentLieFiltration.ControlledSymbolFactorization.mono
      D.filtration F.basis F.weight F.adapted h hrt (fun _ => by exact_mod_cast NeZero.pos N)
  obtain ⟨R⟩ := hconstruct D F.basis F.weight F.adapted ht
    (V.antisymmetricPairNiltest_complexity.1.mono D htest) (by simpa using h2t)
    (fun a b => (F.height a b).trans hrt) V.antisymmetricPairPolynomial
    (piFrequency V.antisymmetricPairFrequencies) (fun _ : Fin 2 => (N : ℝ))
    (fun _ => (Real.exp_le_exp.mpr hcost).trans hN) hfactor
  exact ⟨R.mono hcost (fun _ => by exact_mod_cast NeZero.pos N)⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MixedPairComparison
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

theorem exists_mixed_pair_outer_control (n : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q r : ℝ}
      {W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (n + 1) => 1) p}
      {N : ℕ} [NeZero N] {i j : Fin W.outputDim}
      {V : NativeSampleCorrelation (fun _ : Fin (n + 2) => 1) (n + 1) q
        Finset.univ (fun z : Fin (n + 2) → ZMod N => fun k => ((z k).val : ℤ))
        (fun z => W.mixedAntisymmetric i j (fun k => ((z k).val : ℤ)))}
      (R : NativePolynomialOrbitFactors (pi V.mixedPairModels)
        V.mixedPairPolynomial (piFrequency V.mixedPairFrequencies)
        (fun _ : Fin (n + 2) => (N : ℝ)) r), 0 ≤ r →
      R.HasOuterValueControl ((p + q + r + C) ^ C) := by
  obtain ⟨a, _, hcontrol⟩ := exists_native_orbit_outer_control
    (∑ _ : MixedReplicatedIndex (n + 1), 1) (n + 2)
  let X : Polynomial ℕ := Polynomial.X
  let B := 4 * (X + 1) + (X + (X + 2) ^ 2 + 3) + 6
  let T := (B + 2) ^ 2 + B + (B + (B ^ 2 + B + 3) ^ 2) + B ^ 2 + 4 + X + 3
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((T + Polynomial.C a) ^ a)
  refine ⟨C, hC, ?_⟩
  intro p q r W N _ i j V R hr
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  have hq : 0 ≤ q := (Nat.cast_nonneg V.dim).trans V.complexity.1.1
  let u := p + q + r
  let b := 4 * (u + 1) + raisedNiltestBudget u + 6
  let t := productNiltestBudget b + u + 3
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hpqu : p + q ≤ u := le_add_of_nonneg_right hr
  have hb : 0 ≤ b := by dsimp [b, raisedNiltestBudget]; positivity
  have hprod : 0 ≤ productNiltestBudget b := by
    unfold productNiltestBudget productObservableLipBudget
    positivity
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hrt : r ≤ t := by dsimp [t, u]; linarith
  have hBt : mixedPairBudget p q ≤ b := by
    dsimp [mixedPairBudget, b, raisedNiltestBudget]
    gcongr
  have hB0 : 0 ≤ mixedPairBudget p q :=
    (by norm_num : (0 : ℝ) ≤ 6).trans V.mixedPairBudget_six_le
  have hprodmono : productNiltestBudget (mixedPairBudget p q) ≤ productNiltestBudget b :=
    productNiltestBudget_mono hB0 hBt
  have htest : productNiltestBudget (mixedPairBudget p q) ≤ t :=
    hprodmono.trans (by dsimp [t]; linarith)
  let D := pi V.mixedPairModels
  have hD : D.GeometryComplexityLE t := by
    apply (pi_geometry V.mixedPairModels hB0
      (by simpa using (show (3 : ℝ) ≤ mixedPairBudget p q from
        (by norm_num : (3 : ℝ) ≤ 6).trans V.mixedPairBudget_six_le))
      (fun k => (V.mixedPairTests_complexity k).1)).mono D
    exact (productNiltestBudget_geometry hB0).trans htest
  have hcost : (t + a) ^ a ≤ (p + q + r + C) ^ C := by
    simpa [X, B, T, t, b, u, raisedNiltestBudget, productNiltestBudget,
      productObservableLipBudget, Polynomial.eval₂_pow] using hbudget u hu
  have hN : ∀ _k : Fin (n + 2), (0 : ℝ) < N := fun _ => Nat.cast_pos.mpr (NeZero.pos N)
  have hout : R.HasOuterValueControl ((t + a) ^ a) :=
    hcontrol (R.mono hrt hN) ht hD hN (by simp)
  exact R.hasOuterValueControl_mono hout hcost

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeFrozenComparison
namespace OAI

section

namespace Erdos3

open Module RationalFilteredNilmanifold NilpotentLieBCHGroup
open scoped TensorProduct

theorem exists_native_frozen_comparison (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L : Type} {σ : Type*} [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {d : ℕ} (D : RationalFilteredNilmanifold L (s + 1) d)
      {g : (D.filtration.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group}
      {eta : L →ₗ[ℚ] ℚ} {A : σ → ℝ} {p : ℝ}
      (R : NativePolynomialOrbitFactors D g eta A p)
      (T : Fin 2 → D.Niltest (fun _ : σ => 1)),
      0 ≤ p → (∀ j, (T j).ComplexityLE p) →
      (∀ j x, ‖(T j).observable x‖ ≤ 1) →
      (∀ z : D.RealGroup,
        z.coord ∈ D.filtration.realGradedRefiltrationLayer R.subalgebra (s + 1) →
        ∀ x y : D.Space,
          (T 0).observable (z • x) * star ((T 1).observable (z • y)) =
            (T 0).observable x * star ((T 1).observable y)) →
      ∀ m : ℕ, 0 < m → (m : ℝ) ≤ Real.exp p →
      ∀ a r : Fin 2 → D.RealGroup,
        (∀ j i, |(D.basis.baseChange ℝ).repr (a j).coord i| ≤ Real.exp p) →
        (∀ j, (D.basis.baseChange ℝ).equivFun (r j).coord ∈ realDenominatorGrid m) →
        Nonempty (NativeIntegerExpansion (fun _ : σ => 1) s ((p + C) ^ C)
          (fun x => (T 0).observable (QuotientGroup.mk (R.frozenMiddleValue (a 0) (r 0) x)) *
            star ((T 1).observable (QuotientGroup.mk (R.frozenMiddleValue (a 1) (r 1) x))))) := by
  obtain ⟨B, _, hmodel⟩ := exists_native_middle_model
  obtain ⟨K, _, hcompare⟩ := exists_fixed_model_frozen_comparison s
  let X : Polynomial ℕ := Polynomial.X
  let P := X + (X + Polynomial.C B) ^ B + 4
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((P + Polynomial.C K) ^ K)
  refine ⟨C, hC, ?_⟩
  intro L σ _ _ _ _ _ _ d D g eta A p R T hp hT hcap hpair m hm hmb a r ha hr
  obtain ⟨E, hEF, _hEL, hE, hinc, orbit, horbit⟩ := hmodel D R hp (hT 0).1
  let := moduleTopology ℝ (ℝ ⊗[ℚ] D.filtration.gradedRefiltrationSubalgebra R.subalgebra)
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ]
      D.filtration.gradedRefiltrationSubalgebra R.subalgebra) := IsModuleTopology.topologicalAddGroup ℝ _
  let := realification_moduleTopology_t2 E.basis
  let t := p + (p + B) ^ B + 4
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hpt : p ≤ t := by dsimp [t]; linarith [pow_nonneg (by positivity : 0 ≤ p + B) B]
  have hEt : (p + B) ^ B ≤ t := by dsimp [t]; linarith
  let φ := realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
    (hM := D.filtration.lowerCentralSeries_eq_bot)
    (D.filtration.gradedRefiltrationSubalgebra R.subalgebra).incl
  have hinv (z : E.RealGroup) (hz : z ∈ E.filtration.realification.subgroup (s + 1))
      (x : E.RealGroup) :
      (T 0).observable (QuotientGroup.mk (a 0 * φ (z * x) * r 0)) *
        star ((T 1).observable (QuotientGroup.mk (a 1 * φ (z * x) * r 1))) =
      (T 0).observable (QuotientGroup.mk (a 0 * φ x * r 0)) *
        star ((T 1).observable (QuotientGroup.mk (a 1 * φ x * r 1))) := by
    have htop : (φ z).coord ∈ D.filtration.realGradedRefiltrationLayer R.subalgebra (s + 1) := by
      apply (D.filtration.mem_native_refiltration_layer R.subalgebra (s + 1) z.coord).mp
      have h : z.coord ∈ E.filtration.realification.layer (s + 1) := hz
      simpa only [hEF] using h
    rw [D.frozen_refiltered_group_action R.subalgebra E hEF (a 0) (r 0) z hz x,
      D.frozen_refiltered_group_action R.subalgebra E hEF (a 1) (r 1) z hz x]
    exact hpair (φ z) htop (QuotientGroup.mk (a 0 * φ x * r 0))
      (QuotientGroup.mk (a 1 * φ x * r 1))
  obtain ⟨V⟩ := hcompare E D (D.filtration.gradedRefiltrationSubalgebra R.subalgebra).incl
    orbit T ht (hE.mono E hEt) (fun j => (hT j).mono hpt) hcap
    (fun i j => (hinc j i).trans hEt) m hm (hmb.trans (Real.exp_le_exp.mpr hpt))
    a r (fun j i => (ha j i).trans (Real.exp_le_exp.mpr hpt)) hr hinv
  have hcost : (t + K) ^ K ≤ (p + C) ^ C := by
    simpa [X, P, t, Polynomial.eval₂_pow] using hbudget p hp
  have heval : (fun x => (T 0).observable (QuotientGroup.mk
      (a 0 * φ (E.filtration.realification.polynomialOrbitEval (fun _ => 1) x orbit) * r 0)) *
      star ((T 1).observable (QuotientGroup.mk
        (a 1 * φ (E.filtration.realification.polynomialOrbitEval (fun _ => 1) x orbit) * r 1)))) =
    (fun x => (T 0).observable (QuotientGroup.mk (R.frozenMiddleValue (a 0) (r 0) x)) *
      star ((T 1).observable (QuotientGroup.mk (R.frozenMiddleValue (a 1) (r 1) x)))) := by
    funext x
    dsimp only [φ]
    simp only [horbit]
    rfl
  exact ⟨heval ▸ V.mono hcost⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MixedPreciseSampledExchange
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
  NativeMixedPairPartition.finite

theorem exists_mixed_sampled_exchange (n : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q r b δ β : ℝ} {m N : ℕ} [NeZero N]
      {W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (n + 1) => 1) p}
      {i j : Fin (W.tensorPower m).outputDim}
      {V : NativeSampleCorrelation (fun _ : Fin (n + 2) => 1) (n + 1) q
        Finset.univ (fun z : Fin (n + 2) → ZMod N => fun k => ((z k).val : ℤ))
        (fun z => (W.tensorPower m).mixedAntisymmetric i j (fun k => ((z k).val : ℤ)))}
      {R : NativePolynomialOrbitFactors (pi V.mixedPairModels)
        V.mixedPairPolynomial (piFrequency V.mixedPairFrequencies)
        (fun _ : Fin (n + 2) => (N : ℝ)) r}
      (P : NativeMixedPointwisePartition R b δ β), 0 ≤ b →
      ∃ G : (Fin (n + 2) → Fin 2) → Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ,
        (∀ π a c, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) (n + 1)
          ((b + C) ^ C) (G π a c))) ∧
        (∀ π a c (x : Fin 2 → ZMod N), G π a c (fun z => ((x z).val : ℤ)) =
          ∑ cell, (P.partition.cellWeight cell (fun l => x (π l)) : ℂ) *
            (P.partition.cellVector cell 0 a (fun l => x (π l)) *
              star (P.partition.cellVector cell 1 c (fun l => x (π l))))) ∧
        (∀ π a c (x : Fin 2 → ZMod N), ‖G π a c (fun z => ((x z).val : ℤ))‖ ≤ 1) ∧
        (∀ π a c, (𝔼 x : Fin 2 → ZMod N,
          ‖W.eval a (mixedSlotInput ((x (π 0)).val : ℤ) ((x (π 1)).val : ℤ) (fun l => ((x (π l.succ.succ)).val : ℤ))) *
              star (W.eval c (mixedSlotInput ((x (π 1)).val : ℤ) ((x (π 0)).val : ℤ) (fun l => ((x (π l.succ.succ)).val : ℤ)))) -
            G π a c (fun z => ((x z).val : ℤ))‖) ≤ 2 * (δ + 4 * β)) := by
  obtain ⟨A, _, hpartition⟩ := exists_positive_partition_integer_expansion
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((X + Polynomial.C (n + 2) + Polynomial.C A) ^ A)
  refine ⟨C, hC, ?_⟩
  intro p q r b δ β m N _ W i j V R P hb
  classical
  let t := b + ((n + 2 : ℕ) : ℝ)
  have hdim : (0 : ℝ) ≤ ((n + 2 : ℕ) : ℝ) := Nat.cast_nonneg _
  have ht : 0 ≤ t := by dsimp [t]; linarith
  have hbt : b ≤ t := by dsimp [t]; linarith
  have hσ : (Fintype.card (Fin (n + 2)) : ℝ) ≤ t := by simp only [Fintype.card_fin]; dsimp [t]; linarith
  let v := fun (cell : Fin (n + 2) → P.partition.I) (ac : Fin W.outputDim × Fin W.outputDim)
      (x : Fin (n + 2) → ℤ) =>
    R.mixedPairAnchoredVector (fun k => ((P.partition.anchor cell k).val : ℤ)) 0 ac.1 x *
      star (R.mixedPairAnchoredVector (fun k => ((P.partition.anchor cell k).val : ℤ)) 1 ac.2 x)
  have hv (cell : Fin (n + 2) → P.partition.I) (ac : Fin W.outputDim × Fin W.outputDim) :
      Nonempty (NativeIntegerExpansion (fun _ : Fin (n + 2) => 1) (n + 1) t (v cell ac)) :=
    ((P.partition.equivalence cell).mono hbt).expansion ac.1 ac.2
  obtain ⟨F, hF, hFeval⟩ := hpartition ht hσ
    (P.partition.card_bound.trans (Real.exp_le_exp.mpr hbt))
    (fun cell k => P.partition.weight (cell k)) v
    (fun cell k => (P.partition.positive (cell k)).mono (by omega : 1 ≤ n + 1) hbt) hv
  let G := fun (π : Fin (n + 2) → Fin 2) (a c : Fin W.outputDim) (x : Fin 2 → ℤ) =>
    F (a, c) (fun l => x (π l))
  have hcost : (t + A) ^ A ≤ (b + C) ^ C := by
    simpa [X, t, Polynomial.eval₂_pow] using hbudget b hb
  have hexp (π : Fin (n + 2) → Fin 2) (a c : Fin W.outputDim) :
      Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) (n + 1) ((b + C) ^ C) (G π a c)) := by
    let f : Fin (n + 2) → ((Fin 2 → ℤ) →+ ℤ) :=
      fun k => ⟨⟨fun x => x (π k), rfl⟩, fun _ _ => rfl⟩
    exact ⟨((Classical.choice (hF (a, c))).linearPullbackHom f).mono hcost⟩
  have heval (π : Fin (n + 2) → Fin 2) (a c : Fin W.outputDim) (x : Fin 2 → ZMod N) :
      G π a c (fun z => ((x z).val : ℤ)) =
        ∑ cell, (P.partition.cellWeight cell (fun l => x (π l)) : ℂ) *
          (P.partition.cellVector cell 0 a (fun l => x (π l)) *
            star (P.partition.cellVector cell 1 c (fun l => x (π l)))) :=
    hFeval (a, c) (fun l => x (π l))
  refine ⟨G, hexp, heval, ?_, ?_⟩
  · intro π a c x
    rw [heval]
    apply norm_positive_partition_sum_le_one
      (fun cell => P.partition.cellWeight cell (fun l => x (π l)))
      (fun cell => P.partition.cellVector cell 0 a (fun l => x (π l)) *
        star (P.partition.cellVector cell 1 c (fun l => x (π l))))
      (fun cell => P.partition.cellWeight_nonneg cell _) (P.partition.cellWeight_total _)
    intro cell
    rw [norm_mul, norm_star]
    exact (mul_le_mul_of_nonneg_right (P.partition.cellVector_norm cell 0 a _)
      (norm_nonneg _)).trans (by
        simpa only [one_mul] using P.partition.cellVector_norm cell 1 c _)
  · intro π a c
    simpa only [heval] using P.two_variable_exchange_approximation π a c

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedCenteredNarrowPrescribedMarginal
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal

theorem exists_allocated_narrow_normalized_approximation (m : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {X G : Type*} [Fintype X] [DecidableEq X] [Fintype G]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (basis : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
    (hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
    [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j) (_hσ1 : ∀ j, σ j ≤ 1)
    (C V : Fin m → ℝ≥0)
    (_hC : ∀ j z, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j) z‖ ≤ C j * ‖z‖)
    (_hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ≤ V j)
    (Cinv : Fin m → ℝ) (_hCinv : ∀ j, 0 ≤ Cinv j)
    (_hchart : ∀ j z, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j)).symm z‖ ≤ Cinv j * ‖z‖)
    (_hsmall : ∀ j, Cinv j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 4)
    {P E : ℝ} (_hP : 0 ≤ P) (_hmSize : (m : ℝ) ≤ P)
    (_hK : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ P)
    (_hX : (Fintype.card X : ℝ) ≤ P)
    (_hdim : (Fintype.card (Option (LayerSamplerVariables G I n B) × X) : ℝ) ≤ P)
    (_hRP : ∀ j, (R j)⁻¹ ≤ Real.exp P) (_hσP : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
    (_hcount : ∀ j : Fin m,
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ P)
    (_hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ P) (_hn : ∀ j, (n j : ℝ) ≤ P)
    (_hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ P)
    (_hAP : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P) (_hLP : (S.value : ℝ) ≤ Real.exp P)
    (_hCP : ∀ j, (C j : ℝ) ≤ Real.exp P) (_hVP : ∀ j, (V j : ℝ) ≤ Real.exp P)
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j))
    (hm : ∀ j d, coefficients (p j) d ∈ U j)
    (stride : X → ℕ) (_hs : ∀ d, 0 < stride d) (_hsP : ∀ d, (stride d : ℝ) ≤ Real.exp P)
    {W τ ξ : ℝ} (_hW : 0 ≤ W) (_hWP : W ≤ Real.exp P)
    (_hτ : 0 < τ) (_hτP : τ⁻¹ ≤ Real.exp P)
    (_hτhalf : τ ≤ 1 / 2) (_hτdim : (Fintype.card X : ℝ) * τ ≤ 1 / 2)
    (_hξ : 0 < ξ) (_hξ1 : ξ ≤ 1) (_hξP : ξ⁻¹ ≤ Real.exp P)
    (N : X → ℕ) (_hsize : ∀ d, Real.exp ((max P E + A) ^ A) ≤ (N d : ℝ))
    {rank : ℝ} (_hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun d => (N d : ℝ)) rank (U j) (p j))
    (_hRank : Real.exp ((max P E + A) ^ A) ≤ rank)
    (T : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)) (_hT : T.Nonempty),
    let widths := narrowTrimmedSpatialWidths (G := G)
      (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N
    let bases := trimmedIntegerBox N (spatialTrimMargin τ N)
    let density := allocatedJointBaseDensity B U basis hb o hR hσ S X p hm
    let Z := selectedJointDensityMass bases stride T widths density
    ∃ (hN : ∀ x, 0 < N x) (hbases : bases.Nonempty) (hbox : (integerBox N).Nonempty)
      (hmass : 0 < ∑' z, selectedResidueSmoothWeight stride T widths z),
    ∃ hnormalizer : |Z - 1| ≤ Real.exp (-E) ∧
      Z ∈ Set.Icc (1 / 2 : ℝ) (3 / 2) ∧ 0 < Z ∧ Z⁻¹ ≤ 2,
    ∃ hmargin : ∀ x, 2 * spatialTrimMargin τ N x ≤ N x,
    ∀ {Sites : Type*} [Fintype Sites] [Nonempty Sites]
      (root : Sites → LayerSamplerVariables G I n B → ℤ)
      (_hroot : ∀ t k, |(root t k : ℝ)| ≤ Real.exp P)
      (hrootSum : ∀ t, (∑ k, |(root t k : ℝ)|) ≤ W),
      let pathLaw := allocatedOriginalPathLaw B U basis hb o hR hσ S X p hm N hN _hW _hτ _hξ
        stride T hmass bases hbases hnormalizer.2.2.1
      let physical := narrowPhysicalSiteMap (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n))
        _hW _hτ _hξ1 N hN hmargin root hrootSum
      let Ctail := 4 * ∏ j, earlyConstantDensityCap (Fintype.card (I j)) (n j) (R j) (V j)
      ∀ {Tests : (bases × rectangularWeightIndices 0 widths 1) → Type*}
        [∀ z, Nonempty (Tests z)]
        (slices : ∀ z, Tests z → Finset Sites) (tests : ∀ z, Tests z → Sites → ℂ)
        (w : X → ℕ) (degree : ℕ) {u pModel budget K : ℝ}
        (_hu : 0 ≤ u) (_hpModel : 0 ≤ pModel) (_hbudget : 0 ≤ budget)
        (_hKmodel : 0 ≤ K) (_hKp : K ≤ Real.exp pModel) (_hCtail : Ctail ≤ Real.exp pModel)
        (_hsizeModel : ∀ z j, (Fintype.card Sites : ℝ) / (slices z j).card ≤ K)
        (_htests : ∀ z j t, ‖tests z j t‖ ≤ 1)
        {periodCap coverCap : ℝ} {lip : ℝ≥0},
        u + 2 * pModel + budget + 30 ≤ E →
        (∀ signal : (X → ℤ) → ℂ, (∀ t, ‖signal t‖ ≤ 1) →
          (∀ t, t ∉ integerBox N → signal t = 0) →
          allocatedModelUnitThreshold u pModel K Ctail ≤ sampledSliceSeminorm pathLaw
            (fun z t => jointIntegerPhysicalSite (root t) (z.1.val, z.2.val)) slices tests signal →
          ∃ (twist : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap lip)
            (F : integerBox N → ℂ),
            Nonempty (NativeSampleModel w degree budget (fun t : integerBox N => t.val) F) ∧
            Real.exp (-budget) ≤ ‖(FiniteProbabilityWeights.uniformFinset (integerBox N) hbox).correlation
              (fun t => signal t.val) (fun t => star (twist.eval N p t.val) * F t)‖) →
        ∀ (input : integerBox N → ℂ), (∀ t, ‖input t‖ ≤ Real.exp pModel) →
        ∃ (nterms : ℕ) (_ : 0 < nterms)
          (Q : Fin nterms → (integerBox N → ℂ))
          (coeff : Fin nterms → ℝ) (err : integerBox N → ℂ),
          (∀ i, Q i ∈ twistedNativeSampleFunctions w degree budget
            (fun t : integerBox N => t.val)
            (fun (twist : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap lip)
              (t : integerBox N) => twist.eval N p t.val)) ∧
          input = (∑ i, coeff i • Q i) + err ∧
          (∑ i, |coeff i|) ≤ Real.exp (budget + 2) ∧
          sampledSliceSeminorm pathLaw physical slices tests err ≤ Real.exp (-u) ∧
          (nterms : ℝ) ≤ Real.exp (2 * budget + 2 * u + 4 * pModel + 30) := by
  obtain ⟨A, hA, hmarginal⟩ := exists_allocated_narrow_prescribed_marginal m
  refine ⟨A, hA, ?_⟩
  intro X G _ _ _ I _ n B _ J _ U basis R σ S hb o _ _ _ _ μ _ _ ν _ _
    hR hσ hσ1 C V hC hV Cinv hCinv hchart hsmall P E hP hmSize hK hX hdim
    hRP hσP hcount hI hn hJ hAP hLP hCP hVP p hp hm stride hs hsP W τ ξ
    hW hWP hτ hτP hτhalf hτdim hξ hξ1 hξP N hsize rank hrank hRank T hT widths bases density Z
  obtain ⟨hN, hbases, hbox, hmass, hnormalizer, hmargin, hsite⟩ :=
    hmarginal B U basis S hb o μ ν hR hσ hσ1 C V hC hV Cinv hCinv hchart hsmall
      hP hmSize hK hX hdim hRP hσP hcount hI hn hJ hAP hLP hCP hVP p hp hm stride hs hsP
      hW hWP hτ hτP hτhalf hτdim hξ hξ1 hξP N hsize hrank hRank T hT
  refine ⟨hN, hbases, hbox, hmass, hnormalizer, hmargin, ?_⟩
  intro Sites _ _ root hroot hrootSum pathLaw physical Ctail Tests _ slices tests
    w degree u pModel budget K hu hpModel hbudget hKmodel hKp hCtail hsizeModel htests
    periodCap coverCap lip htail hdetect input hinput
  let : ∀ i, NeZero (N i) := fun i => ⟨(hN i).ne'⟩
  have hCtail0 : 0 ≤ Ctail := by
    apply mul_nonneg (by norm_num : (0 : ℝ) ≤ 4)
    exact Finset.prod_nonneg (fun j _ =>
      earlyConstantDensityCap_nonneg _ _ (hR j) (V j).coe_nonneg)
  exact exists_normalizedTwist_native_approximation_with_budget N p pathLaw physical
    (fun z t => jointIntegerPhysicalSite (root t) (z.1.val, z.2.val)) (fun _ _ => rfl)
    slices tests w degree hu hpModel hbudget hKmodel hCtail0 hKp hCtail hsizeModel htests
    hdetect htail (hsite root hroot hrootSum) input hinput

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal

theorem exists_allocated_centered_narrow_prescribed_marginal_oneCenter (m : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ AllocatedCenteredNarrowPrescribedMarginalOneCenterStatement m A := by
  obtain ⟨A, hA, hmarginal⟩ := exists_allocated_narrow_prescribed_marginal m
  refine ⟨A, hA, ?_⟩
  intro X G _ _ _ I _ n B _ J _ U basis R σ S hb o _ _ _ _ μ _ _ ν _ _
    hR hσ hσ1 C V hC hV Cinv hCinv hchart hsmall P E hP hmSize hK hX hdim
    hRP hσP hcount hI hn hJ hAP hLP hCP hVP p hp hm stride hs hsP W τ ξ
    hW hWP hτ hτP hτhalf hτdim hξ hξ1 hξP N hsize rank hrank hRank T hT
    center widths bases density Z
  obtain ⟨c, hc⟩ := exists_subtractive_constant_center U center
  obtain ⟨hN, hbases, hbox, hmass, hnorm, hmargin, hsite⟩ :=
    hmarginal B U basis S hb o μ ν hR hσ hσ1 C V hC hV
      Cinv hCinv hchart hsmall hP hmSize hK hX hdim hRP hσP hcount hI hn hJ
      hAP hLP hCP hVP (fun j => subtractConstant (c j).val (p j))
      (fun j => (hp j).subtractConstant (c j).val)
      (fun j => coefficients_subtractConstant_mem (U j) (c j) (p j) (hm j))
      stride hs hsP hW hWP hτ hτP hτhalf hτdim hξ hξ1 hξP N hsize
      (fun j => (hasLayerSamplingRank_subtractConstant_iff (Nat.succ_pos j.val)
        (fun d => (N d : ℝ)) rank (U j) (c j).val (p j)).mpr (hrank j)) hRank T hT
  have heq := allocatedJointBaseDensity_subtractConstant_centered B U basis hb o hR hσ
    S p hm center c hc
  have hnormalizer : |Z - 1| ≤ Real.exp (-E) ∧
      Z ∈ Set.Icc (1 / 2 : ℝ) (3 / 2) ∧ 0 < Z ∧ Z⁻¹ ≤ 2 := by
    simpa only [heq] using hnorm
  refine ⟨hN, hbases, hbox, hmass, hmargin, hnormalizer, ?_⟩
  intro law Sites _ _ root hroot hrootSum
  have h := hsite root hroot hrootSum
  have hlaw := allocatedOriginalPathLaw_subtractConstant_eq_centered B U basis hb o hR hσ S
    p hm N hN hW hτ hξ stride T hmass bases hbases center c hc hnorm.2.2.1
    hnormalizer.2.2.1
  rw [hlaw] at h
  exact h

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.AllocatedProductChartRadius
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {α : Type*} [Fintype α] (rowSets : Fin m → Finset (Finset α))
variable {D c : ℝ}
variable (hdim : AllocatedComparisonDimensions (G := G) B α (fun j => (rowSets j : Type _)) D)
variable (hc : 0 ≤ c) (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ D) (hn : ∀ j, (n j : ℝ) ≤ D)
variable (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j) (hCc : ∀ j, C j ≤ Real.exp c)

local notation "H" => 8 * allocatedIdealCoverInputLog m D c + 14

include hdim hc hI hn hC hCc in
theorem allocatedProductChartRadius_le_charts (j : Fin m) :
    allocatedProductChartRadius m D c ≤ allocatedProductGridRadius (G := G) B rowSets C j ∧
      allocatedProductChartRadius m D c ≤ allocatedPhysicalChartRadius (G := G) B α C 1 j ∧
      allocatedProductChartRadius m D c ≤ allocatedIdealCoverRadius (G := G) B rowSets C j := by
  have hgrid := allocatedProductGridRadius_inv_exp_bound B rowSets hdim hc hI hn C hC hCc j
  have hgridPos := allocatedProductGridRadius_pos (G := G) B rowSets C hC j
  have hg := (inv_le_inv₀ (Real.exp_pos (allocatedProductChartLog m D c)) (inv_pos.mpr hgridPos)).2 hgrid
  have hgridLe : allocatedProductChartRadius m D c ≤ allocatedProductGridRadius (G := G) B rowSets C j := by
    simpa only [allocatedProductChartRadius, Real.exp_neg, inv_inv] using hg
  have hcover := allocatedIdealCoverRadius_inverse_from_dimensions B rowSets hdim hc hI hn C hC hCc j
  have hcoverPos := allocatedIdealCoverRadius_pos (G := G) B rowSets C hC j
  have hcInv := (inv_le_inv₀ (Real.exp_pos H) (inv_pos.mpr hcoverPos)).2 hcover
  have hcLe : Real.exp (-H) ≤ allocatedIdealCoverRadius (G := G) B rowSets C j := by
    simpa only [Real.exp_neg, inv_inv] using hcInv
  have hhalf : allocatedProductChartRadius m D c ≤
      allocatedIdealCoverRadius (G := G) B rowSets C j / 2 := by
    apply ((allocatedProductChartRadius_bounds m hdim.nonneg hc).2.2.2).trans
    apply le_trans _ (div_le_div_of_nonneg_right hcLe (by norm_num : (0 : ℝ) ≤ 2))
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
    have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    calc
      _ ≤ Real.exp (-(H + 1)) * Real.exp 1 := mul_le_mul_of_nonneg_left htwo (Real.exp_pos _).le
      _ = Real.exp (-H) := by rw [← Real.exp_add]; congr 1; ring
  exact ⟨hgridLe, hhalf.trans (allocatedIdealCoverRadius_half_le_physical B rowSets C hC j),
    hhalf.trans (by linarith)⟩

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedUniformEarlyRadiusWithCutoff
namespace OAI

section

namespace Erdos3.VectorPolynomial

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {α : Type*} [Fintype α] (rowSets : Fin m → Finset (Finset α))

theorem allocatedCommonProductRadius_admissible {p g : ℝ}
    (hp : 0 ≤ p) (hg : 0 ≤ g) (hq : Fintype.card α ≤ m + 1)
    (hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ p) (hn : ∀ j, (n j : ℝ) ≤ p)
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j) (hCg : ∀ j, C j ≤ Real.exp g) (j : Fin m) :
    allocatedCommonProductRadius m p g ≤ allocatedBufferedPhysicalChartRadius (G := G) B α C j ∧
      allocatedCommonProductRadius m p g ≤ allocatedPhysicalChartRadius (G := G) B α C 1 j ∧
      allocatedCommonProductRadius m p g ≤ allocatedIdealCoverRadius (G := G) B rowSets C j ∧
      allocatedCommonProductRadius m p g ≤ allocatedProductGridRadius (G := G) B rowSets C j := by
  obtain ⟨_, _, _, _, hcommon, hproduct, _⟩ := allocatedCommonProductRadius_bounds m hp hg
  obtain ⟨hbuffer, hphysical, hideal⟩ := allocatedCommonRadius_admissible B rowSets
    hp hg hq hvars hI hn C hC hCg j
  have hdim := allocatedComparisonDimensions_of_primitive (G := G) (α := α)
    (O := fun k => (rowSets k : Type _)) B (fun k => (Subtype.val : rowSets k → Finset α))
    hq (fun _ => Subtype.val_injective) hp hvars hI hn
  have hpD := (allocatedComparisonDimension_bounds m hp).2.2.1
  have hgrid := (allocatedProductChartRadius_le_charts B rowSets hdim hg
    (fun k => (hI k).trans hpD) (fun k => (hn k).trans hpD) C hC hCg j).1
  exact ⟨hcommon.trans hbuffer, hcommon.trans hphysical, hcommon.trans hideal, hproduct.trans hgrid⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped Classical BigOperators NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {α : Type*} [Fintype α] (rowSets : Fin m → Finset (Finset α))
variable [∀ j, Nonempty (rowSets j)]

theorem allocatedCanonicalSlice_source_geometry
    {p g : ℝ} (hp : 0 ≤ p) (hg : 0 ≤ g) (hdim : Fintype.card α ≤ m + 1)
    (hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ p) (hn : ∀ j, (n j : ℝ) ≤ p)
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j) (hCg : ∀ j, C j ≤ Real.exp g)
    {R : Fin m → ℝ} (hR : ∀ j, 0 ≤ R j)
    (hsmall : ∀ j, R j ≤ allocatedCommonProductRadius m p g) :
    let T := allocatedIdealCoverSupport (G := G) B rowSets
    let r := allocatedProductIdealSiteRadius (G := G) B rowSets
    1 ≤ r ∧ (∀ j, 0 ≤ T j) ∧
      (∀ j, partitionedIdealRadius α m + 1 ≤ T j) ∧
      (∀ j, (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) *
        ((2 : ℝ) ^ Fintype.card α * ((Fintype.card α : ℝ) + 1) ^ (j.val + 1)) ≤ T j) ∧
      (∀ j, (rowSets j).card * T j ≤ (r : ℝ)) ∧
      (∀ j, C j * (((Fintype.card (I j) : ℝ) + 1) * (T j * R j)) ≤ 1 / 4) ∧
      (∀ j, ((rowSets j).card + 1 : ℝ) * (Fintype.card (Finset α) *
        (C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (r : ℝ) * R j)))) ≤ 1 / 4) := by
  intro T r
  have hgrid (j) : R j ≤ allocatedProductGridRadius (G := G) B rowSets C j :=
    (hsmall j).trans (allocatedCommonProductRadius_admissible B rowSets hp hg hdim hvars hI hn C hC hCg j).2.2.2
  have hT0 := allocatedIdealCoverSupport_nonneg (G := G) B rowSets
  have hrdom := allocatedProductIdealSiteRadius_dominates (G := G) B rowSets
  refine ⟨allocatedProductIdealSiteRadius_one_le B rowSets, hT0,
    allocatedIdealCoverSupport_ideal B rowSets, allocatedIdealCoverSupport_inactive B rowSets,
    hrdom, ?_, allocatedProductGridRadius_recovery_budget B rowSets C hC hR hgrid⟩
  intro j
  have hrow : (1 : ℝ) ≤ (rowSets j).card := by
    let a : rowSets j := Classical.choice (inferInstance : Nonempty (rowSets j))
    exact_mod_cast Nat.succ_le_of_lt (Finset.card_pos.mpr ⟨a.val, a.property⟩)
  have hTr : T j ≤ (r : ℝ) := by
    calc
      _ ≤ (rowSets j).card * T j := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hrow (hT0 j)
      _ ≤ _ := hrdom j
  have hT2r : T j ≤ 2 * (r : ℝ) := by linarith [r.coe_nonneg]
  apply le_trans _ (allocatedProductGridRadius_source_budget B rowSets C hC hR hgrid j)
  exact mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hT2r (hR j)) (by positivity)) (hC j)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedModularRankCongruenceOutput
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial VectorPolynomial
open scoped BigOperators Classical

variable {D G R : Type*} {B : D → Type*} [Fintype D] [Fintype G]
    [∀ d, Fintype (B d)] [CommRing R]

namespace VectorPolynomial

variable {m : ℕ} {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*} [∀ a, Fintype (B a)]

theorem allocatedBoundedCoefficient_selected_long_top
    (inactive : LayerSamplerAxis I n → Prop) (a : {a // ¬ inactive a})
    {J : ℕ} (block : Fin J ↪ B a.val)
    (fixed : BoundedCoefficientExponent (LayerSamplerVariables G I n B) (a.val.1.val + 1) → R)
    (c : Fin J → R) (v : LayerSamplerVariables G I n B → R) :
    homogeneousComponent (a.val.1.val + 1)
      (conditionPolynomial (allocatedLongEmbedding inactive)
        (allocatedLongEmbedding inactive).injective v
        (modularBoundedCoefficientPolynomial (a.val.1.val + 1)
          (Function.extend (canonicalPrincipalSubblockSlot (layerSamplerDegree I n) a.val block)
            c fixed))) =
      canonicalSelectedLongTopResidual inactive (layerSamplerDegree I n) a block fixed +
        ∑ j, c j • ∏ k ∈ canonicalRankBlock (G := G)
          (B := fun b : {b // ¬ inactive b} => B b.val)
          (fun b => b.val.1.val + 1) a (block j), X k :=
  canonicalBoundedCoefficient_selected_long_top inactive (layerSamplerDegree I n) a
    (Nat.zero_lt_succ _) block fixed c v

end VectorPolynomial
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedModularRankMixedUniform
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped Classical

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*}

def allocatedRankComponentCoefficientSlot
    (inactive : LayerSamplerAxis I n → Prop) :
    AllocatedRankComponentCoefficientIndex G X I E n B inactive →
      AllocatedActualCoefficientIndex G X I E n B
  | ⟨⟨_j, .inl x⟩, q⟩ => .inl (q, x.val)
  | ⟨⟨j, .inr (.inl i)⟩, q⟩ => .inr (.inl ⟨j, q, i⟩)
  | ⟨⟨j, .inr (.inr i)⟩, q⟩ => .inr (.inr ⟨⟨j, .inr i.val⟩, q⟩)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.AllocatedModularRankTaggedPolynomials
namespace OAI

section

namespace Erdos3.VectorPolynomial
open _root_.MvPolynomial
open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*}
    [Fintype G] [∀ j, Fintype (I j)] [∀ a, Fintype (B a)]
    {N L : ℕ}

theorem allocatedDegreeRankPolynomial_eq_designated
    (inactive : LayerSamplerAxis I n → Prop) (j : Fin m)
    (r : CoefficientDeckResidues (K := LayerSamplerVariables G I n B) E N)
    (projection : AllocatedDegreeActiveAxis inactive j →
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ZMod N)
    (kernel : Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ a : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j, a.val⟩)
    (c : AllocatedDegreeRankOutput E inactive j → Fin L → ZMod N)
    (v : LayerSamplerVariables G I n B → ZMod N)
    (o : AllocatedDegreeRankOutput E inactive j) :
    allocatedDegreeRankPolynomial inactive j r projection kernel block c v o =
      designatedVectorComponent (allocatedDegreeRankBlock inactive j kernel block)
        (allocatedDegreeRankResidual inactive j r projection kernel block) c o := by
  cases o with
  | inl i =>
    exact modularDeckPolynomial_kernel_resample_long_top inactive r j i kernel (c (.inl i)) v
  | inr a =>
    exact allocatedBoundedCoefficient_selected_long_top inactive
      (allocatedDegreeLongAxis inactive j a) (block a) (projection a) (c (.inr a)) v

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open _root_.MvPolynomial
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*}
    [Fintype G] [∀ j, Fintype (I j)] [∀ a, Fintype (B a)]
    {N L : ℕ}

theorem allocatedTaggedRankPolynomial_eq_designated
    (inactive : LayerSamplerAxis I n → Prop) (j : Fin m)
    (noise : Option (LayerSamplerVariables G I n B) × X → ZMod N)
    (r : CoefficientDeckResidues (K := LayerSamplerVariables G I n B) E N)
    (projection : AllocatedDegreeActiveAxis inactive j →
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ZMod N)
    (spatial : Fin L ↪ G) (kernel : Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ a : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j, a.val⟩)
    (c : AllocatedTaggedRankOutput X E inactive j → Fin L → ZMod N)
    (v : LayerSamplerVariables G I n B → ZMod N)
    (o : AllocatedTaggedRankOutput X E inactive j) :
    allocatedTaggedRankPolynomial inactive j noise r projection spatial kernel block c v o =
      designatedVectorComponent (allocatedTaggedRankBlock inactive j spatial kernel block)
        (allocatedTaggedRankResidual inactive j noise r projection spatial kernel block) c o := by
  cases o with
  | inl x =>
    have h := allocatedSpatialRankPolynomial_kernel_selected_long inactive spatial
      (fun d => noise (d,x.val)) (c (.inl x)) v
    simpa only [allocatedTaggedRankPolynomial, designatedVectorComponent,
      allocatedTaggedRankResidual, allocatedTaggedRankBlock,
      allocatedSpatialRankBlock_product] using h
  | inr o =>
    simpa only [allocatedTaggedRankPolynomial, designatedVectorComponent,
      allocatedTaggedRankBlock, allocatedTaggedRankResidual] using
      allocatedDegreeRankPolynomial_eq_designated inactive j r projection kernel block
        (fun o => c (.inr o)) v o

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedModularRankActualRead
namespace OAI

section

namespace Erdos3
open _root_.MvPolynomial
open scoped BigOperators Classical

namespace VectorPolynomial
variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*}
    [Fintype G] [∀ j, Fintype (I j)] [∀ a, Fintype (B a)]
    {N L : ℕ}

theorem allocatedOriginalTaggedTop_eq_designated
    (inactive : LayerSamplerAxis I n → Prop) (j : Fin m)
    (noise : Option (LayerSamplerVariables G I n B) × X → ZMod N)
    (r : CoefficientDeckResidues (K := LayerSamplerVariables G I n B) E N)
    (projection : AllocatedDegreeActiveAxis inactive j →
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ZMod N)
    (spatial : Fin L ↪ G) (kernel : Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ a : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j, a.val⟩)
    (v : LayerSamplerVariables G I n B → ZMod N)
    (o : AllocatedTaggedRankOutput X E inactive j) :
    allocatedOriginalTaggedTop inactive j noise r projection v o =
      designatedVectorComponent (allocatedTaggedRankBlock inactive j spatial kernel block)
        (allocatedTaggedRankResidual inactive j noise r projection spatial kernel block)
        (allocatedSelectedRankCoefficients inactive j noise r projection spatial kernel block) o := by
  rw [← allocatedTaggedRankPolynomial_original inactive j noise r projection spatial kernel block v o]
  exact allocatedTaggedRankPolynomial_eq_designated inactive j noise r projection spatial kernel block _ v o

end VectorPolynomial
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedModularRankBadProduct
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*}
    [Fintype G] [∀ j, Fintype (I j)]
    [∀ a, Fintype (B a)] {N L : ℕ}

theorem allocatedCongruenceRankPolynomial_original
    (inactive : LayerSamplerAxis I n → Prop) (j : Fin m)
    (noise : Option (LayerSamplerVariables G I n B) × X → ZMod N)
    (r : CoefficientDeckResidues (K := LayerSamplerVariables G I n B) E N)
    (projection : AllocatedDegreeActiveAxis inactive j →
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ZMod N)
    (spatial : Fin L ↪ G) (kernel : Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ a : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j, a.val⟩)
    (v : LayerSamplerVariables G I n B → ZMod N)
    (o : AllocatedCongruenceRankOutput X E inactive j) :
    allocatedCongruenceRankPolynomial inactive j noise r projection spatial kernel block
      (fun z => allocatedSelectedRankCoefficients inactive j noise r projection spatial kernel block
        (allocatedCongruenceOutputEmbedding inactive j z)) v o =
      allocatedOriginalTaggedTop inactive j noise r projection v
        (allocatedCongruenceOutputEmbedding inactive j o) := by
  rw [allocatedCongruenceRankPolynomial, allocatedTaggedRankPolynomial_eq_designated,
    allocatedOriginalTaggedTop_eq_designated inactive j noise r projection spatial kernel block]
  simp only [designatedVectorComponent,
    (allocatedCongruenceOutputEmbedding (X := X) (E := E) inactive j).injective.extend_apply]

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedModularRankAffineProbability
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped Classical

variable {m : ℕ} {X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {L : ℕ} {R : Type*}

noncomputable def allocatedMixedAffineSelectedValues
    (inactive : LayerSamplerAxis I n → Prop) (stride : X → ℤ)
    (offset : AllocatedCongruenceCoefficientIndex X E inactive L → ℤ)
    {N : ℕ} (x : AllocatedSmoothRankCoefficientIndex X inactive L → ℤ)
    (deck : AllocatedDeckRankCoefficientIndex E L → ZMod N) :
    AllocatedCongruenceCoefficientIndex X E inactive L → ℤ :=
  allocatedCongruenceAffineCoefficients inactive stride offset
    (allocatedMixedSelectedValues inactive x deck)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedModularRankAffineFullWitness
namespace OAI

section

namespace Erdos3.VectorPolynomial
open _root_.MvPolynomial
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*} {L : ℕ}
    [Fintype G] [Fintype X] [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
    [∀ a, Fintype (B a)]

theorem allocatedActualModulusBad_eq_residue
    (inactive : LayerSamplerAxis I n → Prop)
    (spatial : Fin L ↪ G) (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ j, ∀ b : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j, b.val⟩)
    (C : ℝ) (M : ℕ) [NeZero M]
    (f : AllocatedActualCoefficientIndex G X I E n B → ℤ) :
    allocatedActualModulusBad inactive spatial kernel block C M f =
      allocatedResidueModulusBad inactive C M (fun i => (f i : ZMod M)) := by
  unfold allocatedActualModulusBad allocatedCongruenceModulusBad
    allocatedCongruenceRankFailureProbability allocatedResidueModulusBad
  simp only [allocatedCongruenceIntegerSelectedCoefficients_reduce,
    allocatedCongruenceRankPolynomial_original]
  rfl

theorem allocatedResiduePrimePowerWitness_iff_actual
    (inactive : LayerSamplerAxis I n → Prop)
    (spatial : Fin L ↪ G) (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ j, ∀ b : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j, b.val⟩)
    (C : ℝ) (P : Finset ℕ) [∀ p : P, NeZero p.val] (A : ℕ → ℕ)
    (M : ℕ) (hdiv : ∀ p : P, p.val ^ A p.val ∣ M)
    (f : AllocatedActualCoefficientIndex G X I E n B → ℤ) :
    allocatedResiduePrimePowerWitness inactive C P A M hdiv (fun i => (f i : ZMod M)) ↔
      ∀ p : P, allocatedActualModulusBad inactive spatial kernel block C (p.val ^ A p.val) f := by
  unfold allocatedResiduePrimePowerWitness
  apply forall_congr'
  intro p
  rw [allocatedActualModulusBad_eq_residue]
  have hcast : (fun i => ZMod.castHom (hdiv p) (ZMod (p.val ^ A p.val)) (f i : ZMod M)) =
      (fun i => (f i : ZMod (p.val ^ A p.val))) := by
    funext i
    exact map_intCast _ _
  rw [hcast]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical
open FiniteProbabilityWeights

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*} {L : ℕ}
    [Fintype G] [Fintype X] [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
    [∀ a, Fintype (B a)]

variable (inactive : LayerSamplerAxis I n → Prop)
    (noise : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (r : ∀ j : Fin m,
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → E j → ℤ)
    (projection : ∀ j, AllocatedDegreeActiveAxis inactive j →
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ℤ)
    (spatial : Fin L ↪ G) (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ j, ∀ b : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j, b.val⟩)

noncomputable local instance affineWitnessSmoothIndexFintype_r37696e_1 (inactive : LayerSamplerAxis I n → Prop) :
    Fintype (AllocatedSmoothRankCoefficientIndex X inactive L) := inferInstance
attribute [local instance] OAI.Erdos3.VectorPolynomial.affineWitnessDeckIndexFintype
attribute [local instance] OAI.Erdos3.VectorPolynomial.affineWitnessDeckIndexDecidableEq
noncomputable local instance affineWitnessCongruenceIndexFintype_r37696e_1 (inactive : LayerSamplerAxis I n → Prop) :
    Fintype (AllocatedCongruenceCoefficientIndex X E inactive L) := inferInstance
noncomputable local instance affineWitnessCongruenceIndexDecidableEq_r37696e_1 (inactive : LayerSamplerAxis I n → Prop) :
    DecidableEq (AllocatedCongruenceCoefficientIndex X E inactive L) := Classical.decEq _
def allocatedAffineMixedModulusBad (stride : X → ℕ)
    (offset : AllocatedCongruenceCoefficientIndex X E inactive L → ℤ)
    (C : ℝ) (M : ℕ) [NeZero M]
    (x : (AllocatedSmoothRankCoefficientIndex X inactive L ⊕
      AllocatedDeckRankCoefficientIndex E L) → ZMod M) : Prop :=
  allocatedCongruenceModulusBad inactive noise r projection spatial kernel block C M
    (allocatedCongruenceAffineCoefficients inactive (fun x => (stride x : ZMod M))
      (fun j => (offset j : ZMod M)) (allocatedMixedCoefficientEquiv inactive L (ZMod M) x))

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedShortRankWitnessWidth
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped Classical

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*} {L : ℕ}

variable [Fintype G] [Fintype X] [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
    [∀ a, Fintype (B a)]

theorem allocatedChartResiduePrimePowerWitness_iff_actual
    (inactive : LayerSamplerAxis I n → Prop)
    (spatial : Fin L ↪ G) (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ j, ∀ b : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j, b.val⟩)
    (C : ℝ) (P : Finset ℕ) [∀ p : P, NeZero p.val] (A : ℕ → ℕ)
    (M : ℕ) (hdiv : ∀ p : P, p.val ^ A p.val ∣ M)
    (f : AllocatedActualCoefficientIndex G X I E n B → ℤ) :
    allocatedChartResiduePrimePowerWitness inactive C P A M hdiv
      (allocatedReadNoise (fun i => (f i : ZMod M)))
      (allocatedReadCoefficientChartResidues (fun i => (f i : ZMod M))) ↔
      ∀ p : P, allocatedActualModulusBad inactive spatial kernel block C (p.val ^ A p.val) f := by
  rw [allocatedChartResiduePrimePowerWitness_read]
  exact allocatedResiduePrimePowerWitness_iff_actual inactive spatial kernel block C P A M hdiv f

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedAnchoredRecoveredSource
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X] {I E J : Fin m → Type*}
variable [∀ j, Fintype (I j)] [∀ j, Fintype (E j)] [∀ j, Fintype (J j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (bW : ∀ j, Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hm : ∀ j d, coefficients (poly j) d ∈ U j)
variable (inactive : LayerSamplerAxis I n → Prop) {L : ℕ} (spatial : Fin L ↪ G)
variable (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
variable (block : ∀ j, ∀ a : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j,a.val⟩)
variable (C : ℝ)

theorem allocatedPhysicalRankReadCertificate_of_event_read
    (z : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (f : AllocatedActualCoefficientIndex G X I E n B → ℤ)
    (hnoise : allocatedReadNoise f = z)
    (hevent : ∀ (q : ℕ) (hq : 0 < q), letI : NeZero q := ⟨hq.ne'⟩
      ∀ event : CoefficientChartResidues (LayerSamplerVariables G I n B) n E q → Prop,
        coefficientDeckChartEvent U bW b hb o q event
          (affineCoefficientCoverSample U poly hm q (fun k x => (z (k,x) : ℝ))) ↔
        event (allocatedReadCoefficientChartResidues (fun i => (f i : ZMod q)))) :
    AllocatedPhysicalRankReadCertificate B U bW b hb o poly hm inactive spatial kernel block C z f := by
  intro P hP
  let := hP
  intro A M hM
  let : NeZero M := ⟨hM.ne'⟩
  intro hdiv
  have he := hevent M hM (allocatedChartResiduePrimePowerWitness inactive C P A M hdiv
    (fun v => (z v : ZMod M)))
  apply he.trans
  have hn : allocatedReadNoise (fun i => (f i : ZMod M)) = fun v => (z v : ZMod M) := by
    funext v
    change ((allocatedReadNoise f v : ℤ) : ZMod M) = _
    rw [hnoise]
  rw [← hn]
  exact allocatedChartResiduePrimePowerWitness_iff_actual inactive spatial kernel block C P A M hdiv f

theorem AllocatedPhysicalRankReadCertificate.modulusBad_congr
    {z : Option (LayerSamplerVariables G I n B) × X → ℤ}
    {f g : AllocatedActualCoefficientIndex G X I E n B → ℤ}
    (hf : AllocatedPhysicalRankReadCertificate B U bW b hb o poly hm inactive spatial kernel block C z f)
    (hg : AllocatedPhysicalRankReadCertificate B U bW b hb o poly hm inactive spatial kernel block C z g)
    (p a : ℕ) [NeZero p] :
    allocatedActualModulusBad inactive spatial kernel block C (p ^ a) f ↔
      allocatedActualModulusBad inactive spatial kernel block C (p ^ a) g := by
  let P : Finset ℕ := {p}
  have hP : ∀ q : P, NeZero q.val := by
    intro q
    have hq : q.val = p := Finset.mem_singleton.mp q.property
    rw [hq]
    infer_instance
  let := hP
  have hpa : 0 < p ^ a := pow_pos (Nat.pos_of_ne_zero (NeZero.ne p)) _
  let : NeZero (p ^ a) := ⟨hpa.ne'⟩
  have hdiv : ∀ q : P, q.val ^ (fun _ => a) q.val ∣ p ^ a := by
    intro q
    have hq : q.val = p := Finset.mem_singleton.mp q.property
    simp only [hq, dvd_refl]
  have he := (hf P hP (fun _ => a) (p ^ a) hpa hdiv).symm.trans
    (hg P hP (fun _ => a) (p ^ a) hpa hdiv)
  constructor
  · intro h
    apply (he.mp ?_) ⟨p, Finset.mem_singleton_self p⟩
    intro q
    obtain ⟨q, hq⟩ := q
    have hqp : q = p := Finset.mem_singleton.mp hq
    subst q
    exact h
  · intro h
    apply (he.mpr ?_) ⟨p, Finset.mem_singleton_self p⟩
    intro q
    obtain ⟨q, hq⟩ := q
    have hqp : q = p := Finset.mem_singleton.mp hq
    subst q
    exact h

theorem AllocatedPhysicalRankReadCertificate.primeBad_congr
    {z : Option (LayerSamplerVariables G I n B) × X → ℤ}
    {f g : AllocatedActualCoefficientIndex G X I E n B → ℤ}
    (hf : AllocatedPhysicalRankReadCertificate B U bW b hb o poly hm inactive spatial kernel block C z f)
    (hg : AllocatedPhysicalRankReadCertificate B U bW b hb o poly hm inactive spatial kernel block C z g)
    (P : Finset ℕ) [∀ p : P, NeZero p.val] (p : P) (a : ℕ) :
    allocatedActualPrimeBad inactive spatial kernel block P C p.val a f ↔
      allocatedActualPrimeBad inactive spatial kernel block P C p.val a g := by
  rw [allocatedActualPrimeBad_iff_modulusBad, allocatedActualPrimeBad_iff_modulusBad]
  exact hf.modulusBad_congr B U bW b hb o poly hm inactive spatial kernel block C hg p.val a

theorem selectedResidueDensityPMF_certifiedRead_badProduct_congr
    (modulus : X → ℕ)
    (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X modulus))
    (width : Option (LayerSamplerVariables G I n B) × X → ℝ) (hwidth : ∀ z, 0 < width z)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight modulus cells width z)
    (D : (Option (LayerSamplerVariables G I n B) × X → ℤ) → ℝ) (hD0 : ∀ z, 0 ≤ D z)
    (hD : 0 < selectedResidueDensityMass modulus cells width D)
    (read other : (Option (LayerSamplerVariables G I n B) × X → ℤ) →
      AllocatedActualCoefficientIndex G X I E n B → ℤ)
    (hread : ∀ z, D z ≠ 0 →
      AllocatedPhysicalRankReadCertificate B U bW b hb o poly hm inactive spatial kernel block C z (read z))
    (hother : ∀ z, D z ≠ 0 →
      AllocatedPhysicalRankReadCertificate B U bW b hb o poly hm inactive spatial kernel block C z (other z))
    (P : Finset ℕ) [∀ p : P, NeZero p.val] (A : ℕ → ℕ) (threshold : ℕ) :
    (∑' z, (selectedResidueDensityPMF modulus cells width hwidth hZ D hD0 hD z).toReal *
      (if threshold < ∏ p ∈ P, p ^ largestTestedBadDepth A
        (fun p a z => allocatedActualPrimeBad inactive spatial kernel block P C p a (read z)) p z
      then (1 : ℝ) else 0)) =
    ∑' z, (selectedResidueDensityPMF modulus cells width hwidth hZ D hD0 hD z).toReal *
      (if threshold < ∏ p ∈ P, p ^ largestTestedBadDepth A
        (fun p a z => allocatedActualPrimeBad inactive spatial kernel block P C p a (other z)) p z
      then (1 : ℝ) else 0) := by
  apply selectedResidueDensityPMF_badProduct_event_congr
  intro z hz p hp a _ _
  exact (hread z hz).primeBad_congr B U bW b hb o poly hm inactive spatial kernel block C
    (hother z hz) P ⟨p, hp⟩ a

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule
open scoped Classical

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X] {I E J : Fin m → Type*}
variable [∀ j, Fintype (I j)] [∀ j, Fintype (E j)] [∀ j, Fintype (J j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (bW : ∀ j, Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hm : ∀ j d, coefficients (poly j) d ∈ U j)
variable (inactive : LayerSamplerAxis I n → Prop) {L : ℕ} (spatial : Fin L ↪ G)
variable (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
variable (block : ∀ j, ∀ a : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j,a.val⟩)
variable (C : ℝ)

theorem exists_allocatedCentered_recovered_sample_read
    (center : CoefficientTorus (K := LayerSamplerVariables G I n B) U)
    (c : ∀ j, U j)
    (hc : coefficientConstantCenter U center =
      -(QuotientAddGroup.mk' (coefficientIntegerLattice U)
        (constantCoefficientArray U (fun s => c s.1)))) (a : X → ℤ) :
    ∃ sample read, AllocatedCenteredRecoveredSampleReadAt B U bW b hb o S hR hσ poly hm
      inactive spatial kernel block C center c a sample read := by
  obtain ⟨sample, read, hread⟩ := exists_allocatedPhysical_recovered_sample_read B U bW b hb o S hR hσ
    (allocatedCenteredConditionalPolynomial U poly c a)
    (allocatedCenteredConditionalPolynomial_mem U poly hm c a)
  refine ⟨sample, read, ?_⟩
  intro z
  refine ⟨(hread z).1, ?_⟩
  intro hz
  have hdensity := allocatedCenteredConditionalPolynomial_density U poly hm c a B b hb o hR hσ S center hc z
  have hrec := (hread z).2 (hdensity.trans_ne hz)
  refine ⟨hrec.1, hrec.2.1, ?_, hrec.2.2.1, hrec.2.2.2, ?_⟩
  · intro d
    exact (hrec.2.1 d.1.1).1 d.1.2 d.2
  · exact allocatedPhysicalRankReadCertificate_of_event_read B U bW b hb o
      (allocatedCenteredConditionalPolynomial U poly c a)
      (allocatedCenteredConditionalPolynomial_mem U poly hm c a)
      inactive spatial kernel block C z (read z) (hread z).1 hrec.2.2.2

theorem exists_allocatedCentered_recovered_sample_reads
    (c : CoefficientTorus (K := LayerSamplerVariables G I n B) U → ∀ j, U j)
    (hc : ∀ center, coefficientConstantCenter U center =
      -(QuotientAddGroup.mk' (coefficientIntegerLattice U)
        (constantCoefficientArray U (fun s => c center s.1)))) :
    ∃
      (sample : CoefficientTorus (K := LayerSamplerVariables G I n B) U → (X → ℤ) →
        (Option (LayerSamplerVariables G I n B) × X → ℤ) →
          CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
      (read : CoefficientTorus (K := LayerSamplerVariables G I n B) U → (X → ℤ) →
        (Option (LayerSamplerVariables G I n B) × X → ℤ) →
          AllocatedActualCoefficientIndex G X I E n B → ℤ),
      ∀ center a, AllocatedCenteredRecoveredSampleReadAt B U bW b hb o S hR hσ poly hm
        inactive spatial kernel block C center (c center) a (sample center a) (read center a) := by
  choose sample read hread using fun center a =>
    exists_allocatedCentered_recovered_sample_read B U bW b hb o S hR hσ poly hm
      inactive spatial kernel block C center (c center) (hc center) a
  exact ⟨sample, read, hread⟩

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedCenteredBadPrimeSurrogate
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule MeasureTheory
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X] {I E J : Fin m → Type*}
variable [∀ j, Fintype (I j)] [∀ j, Fintype (E j)] [∀ j, Fintype (J j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (bW : ∀ j, Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hm : ∀ j d, coefficients (poly j) d ∈ U j)
variable (inactive : LayerSamplerAxis I n → Prop) (rankC : ℝ)

variable {L : ℕ} (spatial : Fin L ↪ G)
variable (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
variable (block : ∀ j, ∀ a : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j,a.val⟩)

theorem AllocatedPhysicalRankReadCertificate.primePowerEvent_iff
    {z : Option (LayerSamplerVariables G I n B) × X → ℤ}
    {f : AllocatedActualCoefficientIndex G X I E n B → ℤ}
    (hf : AllocatedPhysicalRankReadCertificate B U bW b hb o poly hm inactive spatial kernel block rankC z f)
    (p a : ℕ) [NeZero p] :
    allocatedPhysicalPrimePowerEvent B U bW b hb o poly hm inactive rankC z p a ↔
      allocatedActualModulusBad inactive spatial kernel block rankC (p ^ a) f := by
  have hpa : 0 < p ^ a := pow_pos (NeZero.pos p) a
  have he := hf {p} (singleton_prime_neZero p) (fun _ => a) (p ^ a) hpa
    (singleton_prime_power_dvd p a)
  refine he.trans ?_
  constructor
  · intro h
    exact h ⟨p, Finset.mem_singleton_self p⟩
  · intro h r
    have hr : r.val = p := Finset.mem_singleton.mp r.property
    rcases r with ⟨r, hrmem⟩
    have hrp : r = p := Finset.mem_singleton.mp hrmem
    subst r
    exact h

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedCenteredMeasurableFramedBadTail
namespace OAI

section

namespace Erdos3.VectorPolynomial
open _root_.MvPolynomial
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*} {L : ℕ}

variable [Fintype G] [∀ j, Fintype (I j)] [∀ a, Fintype (B a)]

variable [Fintype X] [∀ j, Fintype (E j)]

theorem allocatedActualModulusBad_jointFrame
    (inactive : LayerSamplerAxis I n → Prop)
    (spatial : Fin L ↪ G) (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ j, ∀ b : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j, b.val⟩)
    (C : ℝ) (M : ℕ) [NeZero M] (a : X → ℤ)
    (f : AllocatedActualCoefficientIndex G X I E n B → ℤ) :
    allocatedActualModulusBad inactive spatial kernel block C M (allocatedJointFrameRead a f) =
      allocatedActualModulusBad inactive spatial kernel block C M f := by
  rw [allocatedActualModulusBad_eq_residue, allocatedActualModulusBad_eq_residue,
    allocatedJointFrameRead_reduce]
  exact allocatedResidueModulusBad_congr_slopes inactive C M _ _ (fun _ _ => rfl) rfl (fun _ _ => rfl)

theorem allocatedJointFrameRead_rankBad
    (inactive : LayerSamplerAxis I n → Prop)
    (spatial : Fin L ↪ G) (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ j, ∀ b : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j, b.val⟩)
    (P : Finset ℕ) [∀ p : P, NeZero p.val] (C : ℝ) (p d : ℕ)
    (a : X → ℤ) (f : AllocatedActualCoefficientIndex G X I E n B → ℤ) :
    allocatedCongruenceRankBad inactive
      (allocatedReadNoise (allocatedJointFrameRead a f)) (allocatedReadDeck (allocatedJointFrameRead a f))
      (fun j b => allocatedReadProjection (allocatedJointFrameRead a f) ⟨j,b.val⟩)
      spatial kernel block P C p d
      (allocatedCongruenceIntegerSelectedCoefficients inactive
        (allocatedReadNoise (allocatedJointFrameRead a f)) (allocatedReadDeck (allocatedJointFrameRead a f))
        (fun j b => allocatedReadProjection (allocatedJointFrameRead a f) ⟨j,b.val⟩)
        spatial kernel block) =
    allocatedCongruenceRankBad inactive (allocatedReadNoise f) (allocatedReadDeck f)
      (fun j b => allocatedReadProjection f ⟨j,b.val⟩) spatial kernel block P C p d
      (allocatedCongruenceIntegerSelectedCoefficients inactive (allocatedReadNoise f) (allocatedReadDeck f)
        (fun j b => allocatedReadProjection f ⟨j,b.val⟩) spatial kernel block) := by
  unfold allocatedCongruenceRankBad smoothResiduePrimeBad
  apply propext
  apply exists_congr
  intro hp
  let : NeZero p := inferInstanceAs (NeZero (⟨p,hp⟩ : P).val)
  exact (allocatedActualModulusBad_jointFrame inactive spatial kernel block C (p ^ d) a f).to_iff

theorem allocatedJointFrameRead_badDepth
    (inactive : LayerSamplerAxis I n → Prop)
    (spatial : Fin L ↪ G) (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ j, ∀ b : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j, b.val⟩)
    (P : Finset ℕ) [∀ p : P, NeZero p.val] (A : ℕ → ℕ) (C : ℝ) (p : ℕ)
    (a : X → ℤ) (f : AllocatedActualCoefficientIndex G X I E n B → ℤ) :
    allocatedCongruenceBadDepth inactive
      (allocatedReadNoise (allocatedJointFrameRead a f)) (allocatedReadDeck (allocatedJointFrameRead a f))
      (fun j b => allocatedReadProjection (allocatedJointFrameRead a f) ⟨j,b.val⟩)
      spatial kernel block P A C p =
    allocatedCongruenceBadDepth inactive (allocatedReadNoise f) (allocatedReadDeck f)
      (fun j b => allocatedReadProjection f ⟨j,b.val⟩) spatial kernel block P A C p := by
  unfold allocatedCongruenceBadDepth largestTestedBadDepth
  simp only [allocatedJointFrameRead_rankBad]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule MeasureTheory
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X] {I E J : Fin m → Type*}
variable [∀ j, Fintype (I j)] [∀ j, Fintype (E j)] [∀ j, Fintype (J j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (bW : ∀ j, Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hm : ∀ j d, coefficients (poly j) d ∈ U j)
variable (inactive : LayerSamplerAxis I n → Prop) {L : ℕ} (spatial : Fin L ↪ G)
variable (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
variable (block : ∀ j, ∀ a : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j,a.val⟩)
variable (rankC : ℝ)
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable (c : CoefficientTorus (K := LayerSamplerVariables G I n B) U → ∀ j, U j)
variable (hc : Measurable c)
variable (sample : CoefficientTorus (K := LayerSamplerVariables G I n B) U → (X → ℤ) →
  (Option (LayerSamplerVariables G I n B) × X → ℤ) → CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
variable (read : CoefficientTorus (K := LayerSamplerVariables G I n B) U → (X → ℤ) →
  (Option (LayerSamplerVariables G I n B) × X → ℤ) → AllocatedActualCoefficientIndex G X I E n B → ℤ)
variable (hread : ∀ center a, AllocatedCenteredRecoveredSampleReadAt B U bW b hb o S hR hσ poly hm
  inactive spatial kernel block rankC center (c center) a (sample center a) (read center a))
variable (stride : X → ℕ)
variable (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride))
variable (width : Option (LayerSamplerVariables G I n B) × X → ℝ) (hwidth : ∀ z, 0 < width z)
variable (hZ : 0 < ∑' z, selectedResidueSmoothWeight stride cells width z)
variable (bases : Finset (X → ℤ)) (hbases : bases.Nonempty)
variable (hD : ∀ center, 0 < selectedJointDensityMass bases stride cells width
  (allocatedCenteredJointDensity B U b hb o hR hσ S poly hm center))
local notation "jointLaw" => (fun center => selectedJointFiniteLaw bases hbases stride cells width hwidth hZ
  (allocatedCenteredJointDensity B U b hb o hR hσ S poly hm center)
  (allocatedCenteredJointDensity_nonneg B U b hb o hR hσ S poly hm center) (hD center))
variable (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U)) [IsProbabilityMeasure μ]
variable (P : Finset ℕ) [∀ p : P, NeZero p.val] (A : ℕ → ℕ) (cutoff : ℕ)

omit [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
  [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
  [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)] in
include hread in
theorem allocatedCentered_joint_positive_rankCertificate : ∀ center (x : bases × rectangularWeightIndices 0 width 1),
      0 < (jointLaw center).weight x →
      AllocatedPhysicalRankReadCertificate B U bW b hb o
        (allocatedCenteredConditionalPolynomial U poly (c center) x.1.val)
        (allocatedCenteredConditionalPolynomial_mem U poly hm (c center) x.1.val)
        inactive spatial kernel block rankC x.2.val (read center x.1.val x.2.val) := by
    intro center x hx
    have hdensity := (selectedJointFiniteLaw_support bases hbases stride cells width hwidth hZ
      (allocatedCenteredJointDensity B U b hb o hR hσ S poly hm center)
      (allocatedCenteredJointDensity_nonneg B U b hb o hR hσ S poly hm center) (hD center) x hx).2.ne'
    exact ((hread center x.1.val x.2.val).2 hdensity).2.2.2.2.2

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedRecoveredPreparedFreeze
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X] {I E J : Fin m → Type*}
variable [∀ j, Fintype (I j)] [∀ j, Fintype (E j)] [∀ j, Fintype (J j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (bW : ∀ j, Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hm : ∀ j d, coefficients (poly j) d ∈ U j)
variable (inactive : LayerSamplerAxis I n → Prop) {L : ℕ} (spatial : Fin L ↪ G)
variable (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
variable (block : ∀ j, ∀ a : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j,a.val⟩)
variable (C : ℝ)
variable [∀ j, IsZLattice ℝ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]

theorem allocatedCentered_recovered_sample_ae
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
    (bases : Finset (X → ℤ)) (hbases : bases.Nonempty) (stride : X → ℕ)
    (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride))
    (width : Option (LayerSamplerVariables G I n B) × X → ℝ) (hwidth : ∀ z, 0 < width z)
    (hmass : 0 < ∑' z, selectedResidueSmoothWeight stride cells width z)
    (hD : ∀ center, 0 < selectedJointDensityMass bases stride cells width
      (allocatedCenteredJointDensity B U b hb o hR hσ S poly hm center))
    (c : CoefficientTorus (K := LayerSamplerVariables G I n B) U → ∀ j, U j)
    (sample : CoefficientTorus (K := LayerSamplerVariables G I n B) U → (X → ℤ) →
      (Option (LayerSamplerVariables G I n B) × X → ℤ) →
        CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (read : CoefficientTorus (K := LayerSamplerVariables G I n B) U → (X → ℤ) →
      (Option (LayerSamplerVariables G I n B) × X → ℤ) →
        AllocatedActualCoefficientIndex G X I E n B → ℤ)
    (hread : ∀ center a, AllocatedCenteredRecoveredSampleReadAt B U bW b hb o S hR hσ poly hm
      inactive spatial kernel block C center (c center) a (sample center a) (read center a)) :
    let law := fun center => selectedJointFiniteLaw bases hbases stride cells width hwidth hmass
      (allocatedCenteredJointDensity B U b hb o hR hσ S poly hm center)
      (allocatedCenteredJointDensity_nonneg B U b hb o hR hσ S poly hm center) (hD center)
    ∀ᵐ z ∂centeredFiniteProbabilityMeasure μ law,
      columnResiduePattern stride z.2.2.val ∈ cells ∧
      0 < allocatedCenteredJointDensity B U b hb o hR hσ S poly hm z.1 z.2.1.val z.2.2.val ∧
      AllocatedCenteredFramedRecoveredSampleAt B U b hb o S hR hσ poly hm
        (c z.1) z.2.1.val z.2.2.val (sample z.1 z.2.1.val z.2.2.val)
        (allocatedJointFrameRead z.2.1.val (read z.1 z.2.1.val z.2.2.val)) := by
  intro law
  have hweight : ∀ x, Measurable (fun center => (law center).weight x) :=
    selectedJointFiniteLaw_weight_measurable bases hbases stride cells width hwidth hmass
      (allocatedCenteredJointDensity B U b hb o hR hσ S poly hm)
      (allocatedCenteredJointDensity_measurable_center B U b hb o hR hσ S poly hm)
      (allocatedCenteredJointDensity_nonneg B U b hb o hR hσ S poly hm) hD
  apply (centeredFiniteProbabilityMeasure_ae_positive_weight μ law hweight).mono
  intro z hz
  have hs := selectedJointFiniteLaw_support bases hbases stride cells width hwidth hmass
    (allocatedCenteredJointDensity B U b hb o hR hσ S poly hm z.1)
    (allocatedCenteredJointDensity_nonneg B U b hb o hR hσ S poly hm z.1) (hD z.1) z.2 hz
  have hf := (hread z.1 z.2.1.val).jointFrame B U bW b hb o S hR hσ poly hm
    inactive spatial kernel block C z.2.2.val
  exact ⟨hs.1, hs.2, hf.1, hf.2.2.2 hs.2.ne'⟩

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.CertifiedFullChartFrozenTerminal
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal

theorem exists_allocated_fullBox_normalized_approximation (m : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {X G : Type*} [Fintype X] [DecidableEq X] [Fintype G] [DecidableEq G]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (basis : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
    (hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
    [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j) (_hσ1 : ∀ j, σ j ≤ 1)
    (C V : Fin m → ℝ≥0)
    (_hC : ∀ j z, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j) z‖ ≤ C j * ‖z‖)
    (_hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ≤ V j)
    (Cinv : Fin m → ℝ) (_hCinv : ∀ j, 0 ≤ Cinv j)
    (_hchart : ∀ j z, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j)).symm z‖ ≤ Cinv j * ‖z‖)
    (_hsmall : ∀ j, Cinv j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 4)
    {P E : ℝ} (_hP : 0 ≤ P) (_hmSize : (m : ℝ) ≤ P)
    (_hK : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ P)
    (_hX : (Fintype.card X : ℝ) ≤ P)
    (_hdim : (Fintype.card (Option (LayerSamplerVariables G I n B) × X) : ℝ) ≤ P)
    (_hRP : ∀ j, (R j)⁻¹ ≤ Real.exp P) (_hσP : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
    (_hcount : ∀ j : Fin m,
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ P)
    (_hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ P) (_hn : ∀ j, (n j : ℝ) ≤ P)
    (_hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ P)
    (_hAP : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P) (_hLP : (S.value : ℝ) ≤ Real.exp P)
    (_hCP : ∀ j, (C j : ℝ) ≤ Real.exp P) (_hVP : ∀ j, (V j : ℝ) ≤ Real.exp P)
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j))
    (hm : ∀ j d, coefficients (p j) d ∈ U j)
    (stride : X → ℕ) (_hs : ∀ d, 0 < stride d) (_hsP : ∀ d, (stride d : ℝ) ≤ Real.exp P)
    {W τ ξ : ℝ} (_hW : 0 ≤ W) (_hWP : W ≤ Real.exp P)
    (hRootBudget : allocatedPhysicalRootBudget B U basis S (fun _ => 0) ≤ W)
    (_hτ : 0 < τ) (_hτP : τ⁻¹ ≤ Real.exp P)
    (_hτhalf : τ ≤ 1 / 2) (_hτdim : (Fintype.card X : ℝ) * τ ≤ 1 / 2)
    (_hξ : 0 < ξ) (_hξ1 : ξ ≤ 1) (_hξP : ξ⁻¹ ≤ Real.exp P)
    (N : X → ℕ) (_hsize : ∀ d, Real.exp ((max P E + A) ^ A) ≤ (N d : ℝ))
    {rank : ℝ} (_hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun d => (N d : ℝ)) rank (U j) (p j))
    (_hRank : Real.exp ((max P E + A) ^ A) ≤ rank)
    (T : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)) (_hT : T.Nonempty),
    let widths := narrowTrimmedSpatialWidths (G := G)
      (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N
    let bases := trimmedIntegerBox N (spatialTrimMargin τ N)
    let density := allocatedJointBaseDensity B U basis hb o hR hσ S X p hm
    let Z := selectedJointDensityMass bases stride T widths density
    ∃ (hN : ∀ x, 0 < N x) (hbases : bases.Nonempty) (hbox : (integerBox N).Nonempty)
      (hmass : 0 < ∑' z, selectedResidueSmoothWeight stride T widths z),
    ∃ hnormalizer : |Z - 1| ≤ Real.exp (-E) ∧
      Z ∈ Set.Icc (1 / 2 : ℝ) (3 / 2) ∧ 0 < Z ∧ Z⁻¹ ≤ 2,
    ∃ hmargin : ∀ x, 2 * spatialTrimMargin τ N x ≤ N x,
    let sides := Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U basis S)
    let Sites := integerBox sides
    let root : Sites → LayerSamplerVariables G I n B → ℤ := Subtype.val
    let hrootSum := fun t => (allocatedParameterBox_root_bound B U basis S t).trans hRootBudget
      let pathLaw := allocatedOriginalPathLaw B U basis hb o hR hσ S X p hm N hN _hW _hτ _hξ
        stride T hmass bases hbases hnormalizer.2.2.1
      let physical := narrowPhysicalSiteMap (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n))
        _hW _hτ _hξ1 N hN hmargin root hrootSum
      let Ctail := 4 * ∏ j, earlyConstantDensityCap (Fintype.card (I j)) (n j) (R j) (V j)
      ∀ {Tests : (bases × rectangularWeightIndices 0 widths 1) → Type*}
        [∀ z, Nonempty (Tests z)]
        (slices : ∀ z, Tests z → Finset Sites) (tests : ∀ z, Tests z → Sites → ℂ)
        (w : X → ℕ) (degree : ℕ) {u pModel budget pSlice : ℝ}
        (_hu : 0 ≤ u) (_hpModel : 0 ≤ pModel) (_hbudget : 0 ≤ budget)
        (_hSliceLog : pSlice * Fintype.card (LayerSamplerVariables G I n B) ≤ pModel)
        (_hCtail : Ctail ≤ Real.exp pModel)
        (_hDense : ∀ z j, IsDenseCommonStrideBox sides pSlice ((slices z j).image root))
        (_htests : ∀ z j t, ‖tests z j t‖ ≤ 1)
        {periodCap coverCap : ℝ} {lip : ℝ≥0},
        let K := Real.exp (pSlice * Fintype.card (LayerSamplerVariables G I n B))
        u + 2 * pModel + budget + 30 ≤ E →
        (∀ signal : (X → ℤ) → ℂ, (∀ t, ‖signal t‖ ≤ 1) →
          (∀ t, t ∉ integerBox N → signal t = 0) →
          allocatedModelUnitThreshold u pModel K Ctail ≤ sampledSliceSeminorm pathLaw
            (fun z t => jointIntegerPhysicalSite (root t) (z.1.val, z.2.val)) slices tests signal →
          ∃ (twist : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap lip)
            (F : integerBox N → ℂ),
            Nonempty (NativeSampleModel w degree budget (fun t : integerBox N => t.val) F) ∧
            Real.exp (-budget) ≤ ‖(FiniteProbabilityWeights.uniformFinset (integerBox N) hbox).correlation
              (fun t => signal t.val) (fun t => star (twist.eval N p t.val) * F t)‖) →
        ∀ (input : integerBox N → ℂ), (∀ t, ‖input t‖ ≤ Real.exp pModel) →
        ∃ (nterms : ℕ) (_ : 0 < nterms)
          (Q : Fin nterms → (integerBox N → ℂ))
          (coeff : Fin nterms → ℝ) (err : integerBox N → ℂ),
          (∀ i, Q i ∈ twistedNativeSampleFunctions w degree budget
            (fun t : integerBox N => t.val)
            (fun (twist : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap lip)
              (t : integerBox N) => twist.eval N p t.val)) ∧
          input = (∑ i, coeff i • Q i) + err ∧
          (∑ i, |coeff i|) ≤ Real.exp (budget + 2) ∧
          sampledSliceSeminorm pathLaw physical slices tests err ≤ Real.exp (-u) ∧
          (nterms : ℝ) ≤ Real.exp (2 * budget + 2 * u + 4 * pModel + 30) := by
  obtain ⟨A, hA, hmodel⟩ := exists_allocated_narrow_normalized_approximation m
  refine ⟨A, hA, ?_⟩
  intro X G _ _ _ _ I _ _ n B _ _ J _ U basis R σ S hb o _ _ _ _ μ _ _ ν _ _
    hR hσ hσ1 C V hC hV Cinv hCinv hchart hsmall P E hP hmSize hK hX hdim
    hRP hσP hcount hI hn hJ hAP hLP hCP hVP p hp hm stride hs hsP W τ ξ
    hW hWP hRootBudget hτ hτP hτhalf hτdim hξ hξ1 hξP N hsize rank hrank hRank T hT widths bases density Z
  obtain ⟨hN, hbases, hbox, hmass, hnormalizer, hmargin, hmodel⟩ :=
    hmodel B U basis S hb o μ ν hR hσ hσ1 C V hC hV Cinv hCinv hchart hsmall
      hP hmSize hK hX hdim hRP hσP hcount hI hn hJ hAP hLP hCP hVP p hp hm stride hs hsP
      hW hWP hτ hτP hτhalf hτdim hξ hξ1 hξP N hsize hrank hRank T hT
  refine ⟨hN, hbases, hbox, hmass, hnormalizer, hmargin, ?_⟩
  intro sides Sites root hrootSum pathLaw physical Ctail Tests _ slices tests
    w degree u pModel budget pSlice hu hpModel hbudget hSliceLog hCtail hDense htests
    periodCap coverCap lip K htail hdetect input hinput
  have hsides (k : LayerSamplerVariables G I n B) : 0 < sides k := by
    cases k with
    | inl g => exact S.positive
    | inr j => exact allocatedPrincipalSides_pos B U basis S j
  let : ∀ k, NeZero (sides k) := fun k => ⟨(hsides k).ne'⟩
  let : Nonempty Sites := (integerBox_nonempty sides).to_subtype
  have hroot (t : Sites) (k) : |(root t k : ℝ)| ≤ Real.exp P :=
    (allocatedParameterBox_coordinate_bound B U basis S t k).trans hLP
  have hsizeModel (z) (j) : (Fintype.card Sites : ℝ) / (slices z j).card ≤ K :=
    allocatedParameterBox_slice_cost B U basis S (hDense z j)
  exact hmodel root hroot hrootSum slices tests w degree hu hpModel hbudget
    (Real.exp_nonneg _) (Real.exp_le_exp.mpr hSliceLog) hCtail hsizeModel htests
    htail hdetect input hinput

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.SharedWidthAllocatedDetectedSpatialNativeSourceGeneral
namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct

noncomputable abbrev allocatedDetectedGain (s variableCount : ℕ)
    (Pdetect : Polynomial ℕ) (p q α : ℝ) : ℝ :=
  (Real.exp (-((5 * p + 20) * variableCount + p + 2)) * (α / 2)) *
    Real.exp (-((q + sampledSupportedSlicedDetectionConstant s Pdetect) ^
      sampledSupportedSlicedDetectionConstant s Pdetect)) ^ (2 ^ (s + 1))

noncomputable abbrev allocatedDetectedKernelCutoff (s : ℕ) (G : Type) [Fintype G]
    (variableCount : ℕ) (Pdetect : Polynomial ℕ) (p q α : ℝ) : ℕ :=
  scalarKernelCutoff (Fin (s + 1)) G 1 ⌈Real.exp (p + 1)⌉₊
    (allocatedDetectedGain s variableCount Pdetect p q α / 2)

attribute [local instance 2000] fullBooleanRowSetFintype
attribute [local instance] ScalarSiteExpansion.termFinite

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedModularRankPreparedBlocks
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

variable {X₀ J₀ : Type} {m : ℕ} (L : RankPreparationFamily X₀ J₀ m)

noncomputable def enlargedPreparedRankPrincipalEmbedding (Jalloc J : ℕ) (hJ : J ≤ Jalloc)
    (a : LayerSamplerAxis (PreparedSamplerContinuous L) (preparedSamplerTransverse L)) :
    Fin J ↪ EnlargedPreparedCommonSamplerBlock L Jalloc a :=
  (Fin.castLEEmb hJ).trans (Fin.natAddEmb (preparedCommonBlockCount m a.1))

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedEnlargedModularAllocation
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

variable {X₀ J₀ : Type} {m : ℕ} (prep : RankPreparationFamily X₀ J₀ m)

noncomputable def preparedInitialRankPrincipalEmbedding (nX M : ℕ)
    (inactive : LayerSamplerAxis (PreparedSamplerContinuous prep)
      (preparedSamplerTransverse prep) → Prop)
    (j : Fin m) (a : AllocatedDegreeActiveAxis inactive j) :
    Fin (modularInitialBlockCount m (nX + m * M)) ↪
      EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))
        ⟨j, a.val⟩ :=
  enlargedPreparedRankPrincipalEmbedding prep _ _ le_rfl ⟨j, a.val⟩

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AllocatedRetainedActualForecastFactory
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G X : Type} [Fintype G] [Fintype X]
    {I E J : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    [∀ j, Fintype (E j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j ex, coefficients (poly j) ex ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    {A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center}

def AllocatedRetainedActualForecastFactoryConclusion
    (bW : ∀ j, Basis (E j) ℤ
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
    (centerLift : ∀ j, U j)
    (sampleFn : (X → ℤ) → (Option (LayerSamplerVariables G I n B) × X → ℤ) →
      CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (readFn : (X → ℤ) → (Option (LayerSamplerVariables G I n B) × X → ℤ) →
      AllocatedActualCoefficientIndex G X I E n B → ℤ)
    (retained : Finset A.Path)
    (Dmod : ℕ) {Lrank : ℕ} (spatial : Fin Lrank ↪ G)
    (kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G)
    (block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
      (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j,a.val⟩)
    (e : Fin 2 × X ↪ G) (Ptest Crecovered : ℝ)
    {Selected : Type} {selected : Selected → Σ j : Fin m, Fin (n j)} {δslice : ℝ}
    (setup : ActualFixedSpatialForecastSetup (X := X) (Eout := E)
      B U b S Dmod selected τ δslice) : Prop :=
    ∃ path : retained → ActualFixedSpatialForecastPath (Eout := E) B U b S hR hσ
      Dmod spatial kernel block (spatialTwoBlockEquiv e)
      (allocatedPhysicalRootBudget B U b S (fun _ => 0)) (S.value : ℝ) N τ 1 setup.P setup.Pbad 0,
      (∀ z, AllocatedCenteredRecoveredSampleReadAt B U bW b hb o S hR hσ poly hm
        (allocatedShortAxis (I := I) U b S.value) spatial kernel block Crecovered
        center (path z).center (path z).base (sampleFn z.val.1.val) (readFn z.val.1.val)) ∧
      (∀ z, (path z).primes = boundedPrimes ⌈Real.exp (2 * Ptest)⌉₊) ∧
      (∀ z, (path z).exponent = fun p => Nat.log p ⌈Real.exp (2 * Ptest)⌉₊) ∧
      (∀ z, (path z).base = z.val.1.val) ∧
      (∀ z, (path z).noise = z.val.2.val) ∧
      (∀ z, (path z).sample = sampleFn z.val.1.val z.val.2.val) ∧
      (∀ z, (path z).read = allocatedReplaceReadNoise B z.val.2.val
        (allocatedJointFrameRead z.val.1.val (readFn z.val.1.val z.val.2.val))) ∧
      (∀ z, (path z).center = centerLift)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedCanonicalRelativeEndpointBounds
namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct

structure PreparedCanonicalRelativeScalarInputs
    {nX m D : ℕ} (prep : RankPreparationFamily (Fin nX) (Fin D) m)
    (s : ℕ) (p pRelative Bstruct : ℝ) : Prop where
  hcoord : ∀ j, Fintype.card (prep j).Coord ≤ preparationCoordinateCap m D (m * D)
  hCoord : ∀ j, Fintype.card (prep j).Coord ≤ preparationCoordinateCap (max m s) D (s * D)
  hpRelative : 0 ≤ pRelative
  hpB : pRelative ≤ Bstruct
  hB : 0 ≤ Bstruct
  hp0 : 0 ≤ p
  hpInput : p ≤ pRelative
  hpSource : p ≤ Bstruct
  hnum :
    (enlargedPreparedCommonSamplerDimension (max m s)
      (preparationCoordinateCap (max m s) D (s * D))
      (modularInitialBlockCount (max m s)
        (nX + max m s * preparationCoordinateCap (max m s) D (s * D))) : ℝ) ≤ Bstruct
  hchartBudget : allocatedUniformChartLog
    (preparationCoordinateCap (max m s) D (s * D) : ℝ) + 1 ≤ Bstruct
  hChartExp : Real.exp (allocatedUniformChartLog
    (preparationCoordinateCap (max m s) D (s * D) : ℝ)) ≤ Real.exp Bstruct
  hEarlyRadius : ∀ j,
    Real.exp (6 * pRelative + 35) *
      ((Fintype.card (PreparedSamplerContinuous (prep.pad (max m s)) j) : ℝ) + 1) *
      allocatedCommonProductRadius (max m s) Bstruct Bstruct ≤ 1 / 4

end Erdos3.VectorPolynomial

end

end OAI
end


