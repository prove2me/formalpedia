-- Prove2me | Definitions.Def_OAIE3v2B244
-- name    : OAIE3v2B244
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-18T05:08:10.195232+00:00
-- url     : https://prove2.me/theorems/25b4b98e-1d58-430b-ab57-9b3f9ac94f36
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 249 of 311
-- statement:
--   Definitions bundle 249 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B209`, `OAIE3v2B301`, `OAIE3v2B230`, `OAIE3v2B231`, `OAIE3v2B232` of this split.
--
--   Modules: `Dynamics/AllocatedFixedPathSlicedNativeAmbientComparison.lean`, `Estimates/HigherResidualRowDifferences.lean`, `Estimates/NativeMarkedFreezingPhysicalData.lean`, `Estimates/NativeResidualCrossInduction.lean`, `Geometry/ActualFixedSpatialSlicedAnalyticIdentification.lean`, `Geometry/ActualFixedSpatialSlicedDataComparison.lean`, `Geometry/ActualFixedSpatialSlicedModelPrecision.lean`, `Geometry/ActualFixedSpatialSlicedPrimitiveGeometry.lean`, `Geometry/ActualFixedSpatialSlicedSourceLog.lean`, `Geometry/ActualFixedSpatialSlicedTargetReal.lean`, `Geometry/NativePairChartSymbol.lean`, `Lattices/ActualFixedSpatialGoodPrimeDeletion.lean`, `Lattices/UniformExternalMarkedAffineSliceFreezingDictionary.lean`, `Linear/ControlledProjectionUniformBudget.lean`, `Probability/ActualFixedSpatialSlicedDensityIdentification.lean`, `Probability/ActualFixedSpatialUnchargedDensity.lean`, `Sampling/ActualFixedSpatialSlicedForecastSourceLaw.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B209
import Definitions.Def_OAIE3v2B301
import Definitions.Def_OAIE3v2B230
import Definitions.Def_OAIE3v2B231
import Definitions.Def_OAIE3v2B232

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.HigherResidualRowDifferences
namespace OAI

section

namespace Erdos3

open scoped TensorProduct BigOperators

attribute [local instance] NativeMeanRowCorrelation.lie NativeMeanRowCorrelation.algebra
  NativeMeanRowCorrelation.topology NativeMeanRowCorrelation.topologicalAdd
  NativeMeanRowCorrelation.continuousSMul NativeMeanRowCorrelation.hausdorff

theorem exists_unit_row_model_with_differences (s : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ}, 0 ≤ p →
      ∀ (f : ZMod N → ℂ) (R : (Unit → ℤ) → ℂ), (∀ n, ‖f n‖ ≤ 1) →
      Nonempty (NativeIntegerExpansion (fun _ : Unit => 1) (s + 1) p R) →
      Real.exp (-p) ≤ ‖𝔼 n : ZMod N, f n * star (R (fun _ => (n.val : ℤ)))‖ →
      ∃ g : (Unit → ℤ) → ℂ,
        (∀ x, ‖g x‖ ≤ 1) ∧
        Nonempty (NativeIntegerExpansion (fun _ : Unit => 1) (s + 1) ((p + C) ^ C) g) ∧
        Real.exp (-((p + C) ^ C)) ≤ ‖𝔼 n : ZMod N, f n * star (g (fun _ => (n.val : ℤ)))‖ ∧
        ∀ {e : ℝ}, 0 ≤ e → Real.exp (e + 16) ≤ (N : ℝ) →
          ∀ k : ZMod N, ∃ K : (Unit → ℤ) → ℂ,
            Nonempty (NativeIntegerExpansion (fun _ : Unit => 1) s ((p + e + C) ^ C) K) ∧
            (𝔼 n : ZMod N,
              ‖g (fun _ => (n.val : ℤ)) * star (g (fun _ => ((n + k).val : ℤ))) -
                K (fun _ => (n.val : ℤ))‖) ≤ Real.exp (-e) := by
  obtain ⟨A, _, hunit⟩ := RationalFilteredNilmanifold.exists_unit_vertical_mean_row_model (s + 1)
  obtain ⟨B, _, hdifference⟩ :=
    RationalFilteredNilmanifold.UnitVerticalObservable.exists_univariate_cyclic_difference_models s hs
  let X : Polynomial ℕ := Polynomial.X
  let U := (2 * X + Polynomial.C A) ^ A
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (U + 4 + (U + X + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro N _ p hp f R hf hR hcorr
  let sample (_ : Unit) (n : ZMod N) : Unit → ℤ := fun _ => (n.val : ℤ)
  have hc : Real.exp (-p) ≤ 𝔼 _h : Unit, ‖𝔼 n : ZMod N, f n * star (R (sample () n))‖ := by
    simpa only [Fintype.expect_const] using hcorr
  obtain ⟨P⟩ := NativeMeanRowCorrelation.exists_of_expansion (Classical.choice hR) hp hc
  have hpp : p + p = 2 * p := by ring
  rw [hpp] at P
  obtain ⟨n, hn, hncard, V, hD, hV⟩ := hunit P.model P.test
    (by positivity : 0 ≤ 2 * p) P.complexity sample (fun _ n => f n) (fun _ n => hf n) P.correlation
  let u := (2 * p + A) ^ A
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hsum : u + 4 + (u + p + B) ^ B ≤ (p + C) ^ C := by
    simpa [X, U, u, Polynomial.eval₂_pow] using hbudget p hp
  have huC : u + 4 ≤ (p + C) ^ C := (le_add_of_nonneg_right (by positivity)).trans hsum
  have huC' : u ≤ (p + C) ^ C := by linarith
  let g : (Unit → ℤ) → ℂ := (V.test P.test.orbit 0).eval
  have hcard : (Fintype.card (Fin (n + 1)) : ℝ) ≤ Real.exp u := by
    simpa only [Fintype.card_fin, Nat.cast_add, Nat.cast_one] using hncard
  refine ⟨g, ?_, ?_, ?_, ?_⟩
  · intro x
    exact (V.test P.test.orbit 0).norm_eval_le x
  · exact ⟨(NativeIntegerExpansion.ofTest (V.test P.test.orbit 0)
      (V.test_complexity P.test.orbit hu hD 0) (fun _ => rfl)).mono huC⟩
  · apply (Real.exp_le_exp.mpr (neg_le_neg huC')).trans
    simpa only [sample, Fintype.expect_const] using hV
  · intro e he hN k
    obtain ⟨K, ⟨E⟩, herr⟩ := hdifference P.model V P.test.orbit hu hD hcard he hN 0 0 k
    have hcost : (u + e + B) ^ B ≤ (p + e + C) ^ C := by
      have hu' : u ≤ (2 * (p + e) + A) ^ A :=
        pow_le_pow_left₀ (by positivity) (by linarith) A
      have hb : (2 * (p + e) + A) ^ A + 4 +
          ((2 * (p + e) + A) ^ A + (p + e) + B) ^ B ≤ (p + e + C) ^ C := by
        simpa [X, U, Polynomial.eval₂_pow] using hbudget (p + e) (add_nonneg hp he)
      apply le_trans _ ((le_add_of_nonneg_left (by positivity)).trans hb)
      exact pow_le_pow_left₀ (by positivity) (by linarith) B
    exact ⟨K, ⟨E.mono hcost⟩, herr⟩

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_unit_row_family_with_differences (s : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {H : Type*} [Fintype H] [Nonempty H] {N : ℕ} [NeZero N]
      {p : ℝ}, 0 ≤ p → ∀ (F : H → ZMod N → ℂ) (R : H → (Unit → ℤ) → ℂ),
      (∀ h n, ‖F h n‖ ≤ 1) →
      (∀ h (n : ZMod N), ‖R h (fun _ => (n.val : ℤ))‖ ≤ 1) →
      (∀ h, Nonempty (NativeIntegerExpansion (fun _ : Unit => 1) (s + 1) p (R h))) →
      Real.exp (-p) ≤ (𝔼 h, ‖𝔼 n : ZMod N, F h n * star (R h (fun _ => (n.val : ℤ)))‖) →
      ∃ g : H → (Unit → ℤ) → ℂ,
        (∀ h x, ‖g h x‖ ≤ 1) ∧
        (∀ h, Nonempty (NativeIntegerExpansion (fun _ : Unit => 1) (s + 1) ((p + C) ^ C) (g h))) ∧
        Real.exp (-((p + C) ^ C)) ≤
          (𝔼 h, ‖𝔼 n : ZMod N, F h n * star (g h (fun _ => (n.val : ℤ)))‖) ∧
        ∀ {e : ℝ}, 0 ≤ e → Real.exp (e + 16) ≤ (N : ℝ) →
          ∀ (h : H) (k : ZMod N), ∃ K : (Unit → ℤ) → ℂ,
            Nonempty (NativeIntegerExpansion (fun _ : Unit => 1) s ((p + e + C) ^ C) K) ∧
            (𝔼 n : ZMod N,
              ‖g h (fun _ => (n.val : ℤ)) * star (g h (fun _ => ((n + k).val : ℤ))) -
                K (fun _ => (n.val : ℤ))‖) ≤ Real.exp (-e) := by
  obtain ⟨A, _, hmodel⟩ := exists_unit_row_model_with_differences s hs
  let X : Polynomial ℕ := Polynomial.X
  let T := X + 2
  let U := (T + Polynomial.C A) ^ A
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (T + U + 2)
  refine ⟨C, hC, ?_⟩
  intro H _ _ N _ p hp F R hF hR hE hcorr
  classical
  let t := p + 2
  let a := (t + A) ^ A
  have ht : 0 ≤ t := by dsimp [t]; linarith
  have hpt : p ≤ t := by dsimp [t]; linarith
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hsum : t + a + 2 ≤ (p + C) ^ C := by
    simpa [X, T, U, t, a, Polynomial.eval₂_pow] using hbudget p hp
  have haC : a ≤ (p + C) ^ C := by linarith
  have htaC : t + a ≤ (p + C) ^ C := by linarith
  have htwo : 2 ≤ (p + C) ^ C := by linarith
  have hcost (e : ℝ) (he : 0 ≤ e) : (t + e + A) ^ A ≤ (p + e + C) ^ C := by
    have hh : (p + e + 2) + (p + e + 2 + A) ^ A + 2 ≤ (p + e + C) ^ C := by
      simpa [X, T, U, Polynomial.eval₂_pow] using hbudget (p + e) (add_nonneg hp he)
    have heq : t + e + A = p + e + 2 + A := by dsimp [t]; ring
    rw [heq]
    linarith
  have htwo' (e : ℝ) (he : 0 ≤ e) : 2 ≤ (p + e + C) ^ C := by
    have hh : (p + e + 2) + (p + e + 2 + A) ^ A + 2 ≤ (p + e + C) ^ C := by
      simpa [X, T, U, Polynomial.eval₂_pow] using hbudget (p + e) (add_nonneg hp he)
    have hpow : 0 ≤ (p + e + 2 + A) ^ A := by positivity
    linarith
  let c (h : H) := ‖𝔼 n : ZMod N, F h n * star (R h (fun _ => (n.val : ℤ)))‖
  have hcap (h : H) : c h ≤ 1 := by
    apply (RCLike.norm_expect_le (K := ℂ)).trans
    apply Finset.expect_le Finset.univ_nonempty
    intro n _
    rw [norm_mul, norm_star]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hF h n)).trans (hR h n)
  obtain ⟨S, hS, hlarge⟩ := exists_dense_level_set c (Real.exp_nonneg (-p)) hcap hcorr
  have hhalf : Real.exp (-t) ≤ Real.exp (-p) / 2 := by
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
    calc
      _ ≤ Real.exp (-t) * Real.exp 2 := mul_le_mul_of_nonneg_left
        (by linarith [Real.add_one_le_exp (2 : ℝ)]) (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; dsimp [t]; ring
  have hgood (h : H) (hh : h ∈ S) :=
    hmodel ht (F h) (R h) (hF h) ⟨(Classical.choice (hE h)).mono hpt⟩
      (hhalf.trans (hlarge h hh))
  let g₀ (h : H) (hh : h ∈ S) := Classical.choose (hgood h hh)
  have hg₀ (h : H) (hh : h ∈ S) := Classical.choose_spec (hgood h hh)
  let g : H → (Unit → ℤ) → ℂ := fun h => if hh : h ∈ S then g₀ h hh else fun _ => 1
  have hg (h : H) (hh : h ∈ S) : g h = g₀ h hh := dif_pos hh
  have hgnot (h : H) (hh : h ∉ S) : g h = fun _ => 1 := dif_neg hh
  refine ⟨g, ?_, ?_, ?_, ?_⟩
  · intro h x
    by_cases hh : h ∈ S
    · rw [hg h hh]
      exact (hg₀ h hh).1 x
    · rw [hgnot h hh]
      simp
  · intro h
    by_cases hh : h ∈ S
    · rw [hg h hh]
      exact ⟨(Classical.choice (hg₀ h hh).2.1).mono haC⟩
    · rw [hgnot h hh]
      exact ⟨NativeIntegerExpansion.constOne _ _ htwo⟩
  · have hmass := dense_set_mean_lower_bound S
      (fun h => ‖𝔼 n : ZMod N, F h n * star (g h (fun _ => (n.val : ℤ)))‖)
      (fun _ => norm_nonneg _) (Real.exp_nonneg (-a))
      ((mul_le_mul_of_nonneg_right hhalf (Nat.cast_nonneg _)).trans hS) (by
        intro h hh
        rw [hg h hh]
        exact (hg₀ h hh).2.2.1)
    apply (Real.exp_le_exp.mpr (neg_le_neg htaC)).trans
    have heq : Real.exp (-(t + a)) = Real.exp (-t) * Real.exp (-a) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rwa [heq]
  · intro e he hN h k
    by_cases hh : h ∈ S
    · obtain ⟨K, ⟨E⟩, herr⟩ := (hg₀ h hh).2.2.2 he hN k
      refine ⟨K, ⟨E.mono (hcost e he)⟩, ?_⟩
      simpa only [hg h hh] using herr
    · refine ⟨fun _ => 1, ⟨NativeIntegerExpansion.constOne _ _ (htwo' e he)⟩, ?_⟩
      simp only [hgnot h hh, star_one, mul_one, sub_self, norm_zero, Finset.expect_const_zero]
      exact Real.exp_nonneg _

end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct BigOperators

theorem exists_residual_row_differences_degree (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L : Type} [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {d : ℕ} (D : RationalFilteredNilmanifold L (s + 3) d)
      (T : D.Niltest (fun _ : Fin 2 => 1)) {p : ℝ}, 0 ≤ p → T.ComplexityLE p →
      ∀ {N : ℕ} [NeZero N], Real.exp ((p + C) ^ C) ≤ (N : ℝ) →
      ∀ (F : ZMod N → ZMod N → ℂ) (R : ZMod N → (Unit → ℤ) → ℂ),
      (∀ h n, ‖F h n‖ ≤ 1) →
      (∀ h (n : ZMod N), ‖R h (fun _ => (n.val : ℤ))‖ ≤ 1) →
      (∀ h, Nonempty (NativeIntegerExpansion (fun _ : Unit => 1) (s + 2) p (R h))) →
      Real.exp (-p) ≤ (𝔼 h, ‖𝔼 n : ZMod N,
        (F h n * star (R h (fun _ => (n.val : ℤ)))) *
          star (T.eval ![(h.val : ℤ), (n.val : ℤ)])‖) →
      ∃ K : ZMod N → (Fin 2 → ℤ) → ℂ,
      ∃ J : ZMod N → ZMod N → (Unit → ℤ) → ℂ,
        (∀ k, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) (s + 2) ((p + C) ^ C) (K k))) ∧
        (∀ k h, Nonempty (NativeIntegerExpansion (fun _ : Unit => 1) (s + 1) ((p + C) ^ C) (J k h))) ∧
        Real.exp (-((p + C) ^ C)) ≤ (𝔼 k, 𝔼 h, ‖𝔼 n : ZMod N,
          multiplicativeDerivative (F h) k n * star (K k ![(h.val : ℤ), (n.val : ℤ)]) *
            star (J k h (fun _ => (n.val : ℤ)))‖) := by
  obtain ⟨A, _, hunit⟩ := exists_unit_vertical_mean_row_model (s + 3)
  obtain ⟨B, _, hrows⟩ := exists_unit_row_family_with_differences (s + 1) (by omega)
  obtain ⟨D₀, _, hcyclic⟩ :=
    UnitVerticalObservable.exists_cyclic_second_difference_models_degree (s + 2) (by omega)
  let X : Polynomial ℕ := Polynomial.X
  let Q := (X + Polynomial.C A) ^ A
  let T₀ := X + Q + 4
  let V₀ := (T₀ + Polynomial.C B) ^ B
  let E₁ := 2 * V₀ + 4
  let A₀ := (Q + E₁ + Polynomial.C D₀) ^ D₀
  let E₂ := E₁ + 2 * A₀
  let B₀ := (T₀ + E₂ + Polynomial.C B) ^ B
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (A₀ + B₀ + 2 * V₀ + E₂ + 20)
  refine ⟨C, hC, ?_⟩
  intro L _ _ _ _ _ _ d D T p hp hT N _ hN F R hF hR hRE hcorr
  classical
  let q := (p + A) ^ A
  let t := p + q + 4
  let v := (t + B) ^ B
  let e₁ := 2 * v + 4
  let a := (q + e₁ + D₀) ^ D₀
  let e₂ := e₁ + 2 * a
  let b := (t + e₂ + B) ^ B
  let z := 2 * v + 2
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have ht : 0 ≤ t := by dsimp [t]; linarith
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have he₁ : 0 ≤ e₁ := by dsimp [e₁]; linarith
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have he₂ : 0 ≤ e₂ := by dsimp [e₂]; linarith
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hpt : p ≤ t := by dsimp [t]; linarith
  have hqt : q ≤ t := by dsimp [t]; linarith
  have hsum : a + b + 2 * v + e₂ + 20 ≤ (p + C) ^ C := by
    simpa [X, Q, T₀, V₀, E₁, A₀, E₂, B₀, q, t, v, e₁, a, e₂, b,
      Polynomial.eval₂_pow] using hbudget p hp
  have haC : a ≤ (p + C) ^ C := by linarith
  have hbC : b ≤ (p + C) ^ C := by linarith
  have hzC : z ≤ (p + C) ^ C := by dsimp [z]; linarith
  have hN₁ : Real.exp (e₁ + 16) ≤ (N : ℝ) := by
    apply (Real.exp_le_exp.mpr ?_).trans hN
    dsimp [e₂] at hsum
    linarith
  have hN₂ : Real.exp (e₂ + 16) ≤ (N : ℝ) :=
    (Real.exp_le_exp.mpr (by linarith)).trans hN
  obtain ⟨m, _, hmcard, V, hD, hVcorr⟩ := hunit D T hp hT
    (fun h n : ZMod N => ![(h.val : ℤ), (n.val : ℤ)])
    (fun h n => F h n * star (R h (fun _ => (n.val : ℤ)))) (by
      intro h n
      rw [norm_mul, norm_star]
      exact (mul_le_of_le_one_left (norm_nonneg _) (hF h n)).trans (hR h n)) hcorr
  let u (h n : ZMod N) := (V.test T.orbit 0).eval ![(h.val : ℤ), (n.val : ℤ)]
  have hu (h n : ZMod N) : ‖u h n‖ ≤ 1 := (V.test T.orbit 0).norm_eval_le _
  have hcard : (Fintype.card (Fin (m + 1)) : ℝ) ≤ Real.exp q := by
    simpa only [Fintype.card_fin, Nat.cast_add, Nat.cast_one] using hmcard
  have hrowcorr : Real.exp (-t) ≤ (𝔼 h, ‖𝔼 n : ZMod N,
      (F h n * star (u h n)) * star (R h (fun _ => (n.val : ℤ)))‖) := by
    apply (Real.exp_le_exp.mpr (neg_le_neg hqt)).trans
    apply hVcorr.trans_eq
    apply Finset.expect_congr rfl
    intro h _
    congr 1
    apply Finset.expect_congr rfl
    intro n _
    exact mul_right_comm _ _ _
  obtain ⟨G, hG, _, hGcorr, hGdiff⟩ := hrows ht
    (fun h n => F h n * star (u h n)) R (by
      intro h n
      rw [norm_mul, norm_star]
      exact (mul_le_of_le_one_left (norm_nonneg _) (hF h n)).trans (hu h n)) hR
    (fun h => ⟨(Classical.choice (hRE h)).mono hpt⟩) hrowcorr
  have hbase : Real.exp (-v) ≤ (𝔼 h, ‖𝔼 n : ZMod N,
      F h n * star (u h n * G h (fun _ => (n.val : ℤ)))‖) := by
    simpa only [star_mul, mul_comm, mul_left_comm, mul_assoc] using hGcorr
  have hmodels (k : ZMod N) : ∃ K : (Fin 2 → ℤ) → ℂ,
      Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) (s + 2) a K) ∧
      ∀ h : ℤ, (𝔼 n : ZMod N,
        ‖cyclicSecondDifference (V.test T.orbit 0).eval (V.test T.orbit 0).eval k h n -
          K ![h, (n.val : ℤ)]‖) ≤ Real.exp (-e₁) :=
    hcyclic D V T.orbit hq hD hcard he₁ hN₁ 0 0 k
  choose K hK herrK using hmodels
  have hrowmodels (k h : ZMod N) : ∃ J : (Unit → ℤ) → ℂ,
      Nonempty (NativeIntegerExpansion (fun _ : Unit => 1) (s + 1) b J) ∧
      (𝔼 n : ZMod N,
        ‖G h (fun _ => (n.val : ℤ)) * star (G h (fun _ => ((n + k).val : ℤ))) -
          J (fun _ => (n.val : ℤ))‖) ≤ Real.exp (-e₂) :=
    hGdiff he₂ hN₂ h k
  choose J hJ herrJ using hrowmodels
  have hd := mean_row_correlation_sq_le_product_derivatives F u
    (fun h n => G h (fun _ => (n.val : ℤ)))
    (fun k h n => K k ![(h.val : ℤ), (n.val : ℤ)])
    (fun k h n => J k h (fun _ => (n.val : ℤ)))
    (B := Real.exp (2 * a)) (ε := Real.exp (-e₁)) (δ := Real.exp (-e₂))
    hF (fun h n => hG h _) (Real.exp_nonneg _) (by
      intro k h n
      exact (Classical.choice (hK k)).norm_eval_le _) (by
      intro k h
      simpa only [u, multiplicativeDerivative, cyclicSecondDifference] using herrK k h.val) (by
      intro k h
      simpa only [multiplicativeDerivative] using herrJ k h)
  have hlarge : Real.exp (-(2 * v)) ≤ (𝔼 k, 𝔼 h, ‖𝔼 n : ZMod N,
      multiplicativeDerivative (F h) k n * star (K k ![(h.val : ℤ), (n.val : ℤ)]) *
        star (J k h (fun _ => (n.val : ℤ)))‖) +
          (Real.exp (-e₁) + Real.exp (2 * a) * Real.exp (-e₂)) := by
    have hsquare := (pow_le_pow_left₀ (Real.exp_nonneg (-v)) hbase 2).trans hd
    have hexp : Real.exp (-v) ^ 2 = Real.exp (-(2 * v)) := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    simpa only [hexp, star_mul, mul_comm, mul_left_comm, mul_assoc] using hsquare
  have herror : Real.exp (-e₁) + Real.exp (2 * a) * Real.exp (-e₂) ≤ Real.exp (-z) := by
    have hmul : Real.exp (2 * a) * Real.exp (-e₂) = Real.exp (-e₁) := by
      rw [← Real.exp_add]
      congr 1
      dsimp [e₂]
      ring
    rw [hmul]
    calc
      _ = 2 * Real.exp (-e₁) := by ring
      _ ≤ Real.exp 2 * Real.exp (-e₁) := mul_le_mul_of_nonneg_right
        (by linarith [Real.add_one_le_exp (2 : ℝ)]) (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; dsimp [e₁, z]; ring
  have htwo : 2 * Real.exp (-z) ≤ Real.exp (-(2 * v)) := by
    calc
      _ ≤ Real.exp 2 * Real.exp (-z) := mul_le_mul_of_nonneg_right
        (by linarith [Real.add_one_le_exp (2 : ℝ)]) (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; dsimp [z]; ring
  refine ⟨K, J, fun k => ⟨(Classical.choice (hK k)).mono haC⟩,
    fun k h => ⟨(Classical.choice (hJ k h)).mono hbC⟩, ?_⟩
  apply (Real.exp_le_exp.mpr (neg_le_neg hzC)).trans
  linarith

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeResidualCrossInduction
namespace OAI

section

namespace Erdos3

open scoped TensorProduct BigOperators

theorem exists_native_residual_cross_row_step {s A : ℕ}
    (hdetect : NativeResidualCrossRowDetection s A) :
    ∃ C : ℕ, 2 ≤ C ∧ NativeResidualCrossRowDetection (s + 1) C := by
  obtain ⟨B, _, hdifference⟩ := RationalFilteredNilmanifold.exists_residual_row_differences_degree s
  obtain ⟨D, _, hfamily⟩ := exists_gowers_of_native_residual_cross_family hdetect
  let X : Polynomial ℕ := Polynomial.X
  let U := (X + Polynomial.C B) ^ B
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (U + (U + Polynomial.C D) ^ D)
  refine ⟨C, hC, ?_⟩
  intro L _ _ _ _ _ _ d M T p hp hT N _ hN f g R hf hg hR hRE hcorr
  let u := (p + B) ^ B
  let v := (u + D) ^ D
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have hsum : u + v ≤ (p + C) ^ C := by
    simpa [X, U, u, v, Polynomial.eval₂_pow] using hbudget p hp
  have huC : u ≤ (p + C) ^ C := by linarith
  have hvC : v ≤ (p + C) ^ C := by linarith
  obtain ⟨K, J, hK, hJ, hdiff⟩ := hdifference M T hp hT
    ((Real.exp_le_exp.mpr huC).trans hN) (fun h n => f n * star (g (n + h))) R
    (by
      intro h n
      rw [norm_mul, norm_star]
      exact (mul_le_of_le_one_left (norm_nonneg _) (hf n)).trans (hg (n + h))) hR hRE hcorr
  have hderiv (h k n : ZMod N) :
      multiplicativeDerivative (fun n => f n * star (g (n + h))) k n =
        multiplicativeDerivative f k n * star (multiplicativeDerivative g k (n + h)) := by
    simp only [multiplicativeDerivative, star_mul, star_star]
    rw [add_right_comm n k h]
    ring
  have hclean : Real.exp (-u) ≤ (𝔼 k, 𝔼 h, ‖𝔼 n : ZMod N,
      ((multiplicativeDerivative f k n * star (multiplicativeDerivative g k (n + h))) *
        star (J k h (fun _ => (n.val : ℤ)))) *
        star (K k ![(h.val : ℤ), (n.val : ℤ)])‖) := by
    simpa only [hderiv, mul_comm, mul_left_comm, mul_assoc] using hdiff
  have hmean := hfamily hu ((Real.exp_le_exp.mpr hvC).trans hN)
    (multiplicativeDerivative f) (multiplicativeDerivative g) K J
    (multiplicativeDerivative_norm_le_one f hf) (multiplicativeDerivative_norm_le_one g hg)
    hK hJ hclean
  exact (Real.exp_le_exp.mpr (neg_le_neg hvC)).trans
    (exp_le_gowers_of_mean_derivative (s + 2) g hv hmean)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.AllocatedFixedPathSlicedNativeAmbientComparison
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G X T : Type*} [Fintype T] [Fintype G] [Fintype X]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Active" => {a : LayerSamplerAxis I n // ¬short a}
local notation "degree" => layerSamplerDegree I n
local notation "Input" => (Σ a : Active, B (Subtype.val a) × Fin (degree (Subtype.val a)))
local notation "Output" => (Σ _a : Active, Unit)

variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable {PrimeIndex : Type*} [Fintype PrimeIndex]
variable (primes exponent : PrimeIndex → ℕ) [∀ l, NeZero (primes l)]
variable (HP stepP : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (cP : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ)
variable (hinsideP : ∀ j (v : Fin (HP j)), 0 ≤ cP j + (stepP j : ℤ) * v.val ∧
  cP j + (stepP j : ℤ) * v.val < allocatedPrincipalSides B U basis S j)
variable (hHP : ∀ j, 0 < HP j)

variable (τ ξ : ℝ)
variable (hτ : 0 < τ)
variable (hξ : 0 < ξ)
variable (box : X → ℕ)
variable (hbox : ∀ x, 0 < box x)
variable (integerFrame : Option (LayerSamplerVariables G I n B) × X → ℤ)
variable (hframe : integerFrame ∈ rectangularWeightIndices 0
      (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) (allocatedPhysicalRootBudget B U basis S (fun _ => 0)) τ ξ box) 1)
variable (HG : G → ℕ)
variable (hHG : ∀ g, 2 ≤ HG g)
variable (cG : G → ℤ)
variable (stepG : ℕ)
variable (hstepG : 0 < stepG)
variable (hcontainedG : ∀ g, integerProgressionSupport (cG g) (stepG : ℤ) (HG g) ⊆
      Finset.Ico (0 : ℤ) (S.value : ℤ))
variable (e : G ≃ X ⊕ (X ⊕ T))
variable (h0 : (fixedSpatialKernelBlock e (allocatedPhysicalRootBudget B U basis S (fun _ => 0)) (S.value : ℝ) (allocatedFixedPathKernelFrame B U basis S τ ξ box integerFrame) false).det ≠ 0)
variable (h1 : (fixedSpatialKernelBlock e (allocatedPhysicalRootBudget B U basis S (fun _ => 0)) (S.value : ℝ) (allocatedFixedPathKernelFrame B U basis S τ ξ box integerFrame) true).det ≠ 0)
variable (hB : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, 4 ≤ Fintype.card (B a.val))
variable (sample : (CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n))
variable (hs : ∀ j, mixedArraySupported (allocatedLayerCenters B U basis S j)
      (allocatedLayerWidths B U basis S j)
      (allocatedLayerIntegerPMFs B U basis hR hσ S j) (sample j))
variable {t : ℝ}
variable (ht : 0 < t)
variable (hσbound : ∀ j, |σ j| ≤ t)
variable (H : (Σ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, B a.val × Fin (layerSamplerDegree I n a.val)) → ℕ)
variable (c : (Σ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, B a.val × Fin (layerSamplerDegree I n a.val)) → ℤ)
variable (hH : ∀ j, 2 ≤ H j)
variable {δ : ℝ}
variable (hδ : 0 < δ)
variable (hsubset : ∀ j, integerProgressionSupport (c j) (stepG : ℤ) (H j) ⊆
      Finset.Ico (0 : ℤ) (S.value : ℤ))
variable (hdense : ∀ j, δ * S.value ≤
      ((integerProgressionSupport (c j) (stepG : ℤ) (H j)).card : ℝ))
variable (q : ℕ)
variable [NeZero q]
variable (hsizeG : ∀ g, q ≤ HG g)
variable (hsmallG : ∀ g, scalarCubeGridBoundaryConstant Empty * ((q : ℝ) / HG g) < 1)
variable (hsize : ∀ j, q ≤ H j)
variable (hsmall : ∀ j, scalarCubeGridBoundaryConstant Empty * ((q : ℝ) / H j) < 1)
variable {ε : ℝ}
variable (hε : 0 ≤ ε)
variable (hmesh : ∀ _j : (Σ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, B a.val × Fin (layerSamplerDegree I n a.val)), (stepG : ℝ) / S.value ≤ ε)
variable (hδone : δ ≤ 1)
variable (b : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, B a.val)
variable {η : ℝ}
variable (hη : 0 < η)
variable (A : ℝ≥0)
variable (hA : LipschitzWith A Real.smoothTransition)
variable (htail : |t| * polynomialMassC2Budget (Fintype.card (Σ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, B a.val × Fin (layerSamplerDegree I n a.val))) m 1 ≤
      slicedPrincipalC2Tolerance (Fintype.card (Σ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, B a.val × Fin (layerSamplerDegree I n a.val))) (Fintype.card {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}) m 1
        (unitProfilePrincipalLowerBound B) (δ / 2) A η)
variable {Cidx : Type*}
variable (selected : Cidx → Σ j : Fin m, Fin (n j))
variable (hshort : ∀ a, basisAxisScale (basis (selected a).1) (selected a).2 ≤
      S.value ^ ((selected a).1.val + 1))
variable (xref : G → IntegerScalarCubeBox Empty S.value)
variable (base : X → ℤ)
variable (deck : ∀ j : Fin m,
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → E j → ℤ)
variable (projection : ∀ j, AllocatedDegreeActiveAxis (allocatedShortAxis (I := I) U basis S.value) j →
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ℤ)
variable (hp : ∀ l, (primes l).Prime)
variable (hcoprime : Pairwise (fun l k => (primes l ^ exponent l).Coprime (primes k ^ exponent k)))
variable (hqN : q ∣ (∏ l, primes l ^ exponent l))
variable {gridVolume : ℝ}
variable (hV : gridVolume ≠ 0)
variable (test : (Cidx → ((Finset.univ : Finset (Finset Empty)) : Type) → ℤ) →
      ((Sigma (AllocatedCongruenceRankOutput X E (allocatedShortAxis (I := I) U basis S.value))) → ZMod q) → (((Σ _ : X, Unit ⊕ Empty) → ℝ) × ((Σ _a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, Unit) → ℝ)) → ℂ)
variable {Kφ : ℝ≥0}
variable (htest : ∀ grid residue, LipschitzWith Kφ (test grid residue))
variable (hbound : ∀ grid residue y, ‖test grid residue y‖ ≤ 1)

attribute [local instance] OAI.Erdos3.VectorPolynomial.slicedPhysicalDensityCRTNeZero
noncomputable def allocatedSlicedPhysicalSourceMean : ℂ :=
    let kernel := FiniteProbabilityWeights.pi (fun g => integerScalarCubeWeights Empty (HG g) (lt_of_lt_of_le (by decide : 0 < 2) (hHG g)))
    let active := FiniteProbabilityWeights.pi (fun j : Input => integerScalarCubeWeights Empty (H j)
      (lt_of_lt_of_le (by decide : 0 < 2) (hH j)))
    let embed := fun (x : ∀ g, IntegerScalarCubeBox Empty (HG g)) g =>
      containedProgressionCubeMap Empty S.value (HG g) stepG (cG g) S.positive (hcontainedG g) (x g)
    let activeEmbed := allocatedActiveContainedProgression B U basis S (fun _ => stepG) H c hsubset
    let joined := fun u v => principalAxisJoin short u (activeEmbed v)
    let shortLaw := allocatedInactiveAffineIntervalLaw B U basis S HP stepP cP hinsideP hHP
    let coeff := allocatedOriginalSampleInactiveCoefficients B selected sample
    let φ := fun u rG rA => test (forecastInactiveShortGrid B U basis S selected coeff u)
      (allocatedJointResidueOutput B U basis S base integerFrame deck projection q rG
        (allocatedPrincipalResidueJoin B U basis S q u rA))
    shortLaw.complexMean (fun u => kernel.complexMean (fun x => active.complexMean (fun v =>
        φ u (fun g => ((cG g + (stepG : ℤ) * (x g none : ℤ) : ℤ) : ZMod q))
          (fun j => ((c j + (stepG : ℤ) * (v j none : ℤ) : ℤ) : ZMod q))
          ((fun o : Σ _ : X, Unit ⊕ Empty =>
              (integerPhysicalSite (allocatedPhysicalCubeRoot B U basis S (fun _ => 0)
                (embed x) (joined u v)) integerFrame o.1 : ℝ) / (τ * (box o.1 : ℝ) / 8)),
            (fun o : Output => allocatedFullMixedSiteValue (R := R) U basis
              (allocatedOriginalSamplePhysicalMixedValue B U basis S sample (embed x) (joined u v))
                o.1.val)))))

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.UniformExternalMarkedAffineSliceFreezingDictionary
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal BigOperators

theorem exists_uniform_external_marked_affine_slice_freezing (s a u : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {X σ κ L T : Type*} [Fintype σ] [DecidableEq σ] [Fintype κ]
      [LieRing L] [LieAlgebra ℚ L] [LieRing T] [LieAlgebra ℚ T]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {d t : ℕ} (D : RationalFilteredNilmanifold L s d)
      (F : NilpotentLieFiltration T t) (c : Basis κ ℚ T)
      (ω : Fin d → ℕ)
      (_hDlayers : ∀ j, D.filtration.layer j = Submodule.span ℚ (D.basis '' {i | j ≤ ω i}))
      (τ : κ → ℕ) (_hFlayers : ∀ j, F.layer j = Submodule.span ℚ (c '' {i | j ≤ τ i}))
      (φ : L →ₗ⁅ℚ⁆ T) (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ F.layer j),
      (∀ j, ∀ y ∈ F.layer j, ∃ x ∈ D.filtration.layer j, φ x = y) →
      ∀ w : σ → ℕ, (∀ i, 0 < w i) → ∀ p : ℝ,
      0 ≤ p → D.GeometryComplexityLE p → (Fintype.card σ : ℝ) ≤ p →
      (Fintype.card κ : ℝ) ≤ p →
      (∀ i j, rationalLogHeight (c.repr (φ (D.basis j)) i) ≤ p) →
      ∃ (S : T →ₗ[ℚ] L) (hS : ∀ j, ∀ y ∈ F.layer j, S y ∈ D.filtration.layer j),
        Function.RightInverse S φ ∧
        (∀ i j, RationalHeightLE (D.basis.repr (S (c j)) i)
          (rationalKernelHeight (Fintype.card κ) ⌈Real.exp p⌉₊)) ∧
        ∀ l : ℕ, 0 < l → (l : ℝ) ≤ Real.exp p →
          ∀ Tbox : σ → ℝ, (∀ i, 0 < Tbox i) →
            D.ExternalMarkedAffineSliceFreezing (X := X) F c φ hφ w S hS l Tbox
              (Real.exp ((p + 2) ^ a)) (Real.exp (-((p + 2) ^ u)))
              (Real.exp ((p + C) ^ C)) := by
  obtain ⟨C, hC, hbase⟩ := exists_uniform_bounded_cell_marked_polynomial_freezing s a u
  refine ⟨C, hC, ?_⟩
  intro X σ κ L T _ _ _ _ _ _ _ _ _ _ _ d t D F c ω hDlayers τ hFlayers φ hφ hsurj
    w hw p hp hD hσ hκ hφb
  obtain ⟨S, hS, hright, hSb, hfreeze⟩ := hbase D F c ω hDlayers τ hFlayers φ hφ hsurj
    w hw p hp hD hσ hκ hφb
  exact ⟨S, hS, hright, hSb, fun l hl hlp Tbox hT =>
    (hfreeze l hl hlp Tbox hT).external_affine_slice hT (Real.exp_nonneg _)⟩

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal

theorem exists_uniform_external_marked_affine_slice_freezing_dictionary (s a u : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {X σ κ L T : Type*} [Fintype σ] [DecidableEq σ] [Fintype κ]
      [LieRing L] [LieAlgebra ℚ L] [LieRing T] [LieAlgebra ℚ T]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {d t : ℕ} (D : RationalFilteredNilmanifold L s d)
      (F : NilpotentLieFiltration T t) (c : Basis κ ℚ T)
      (ω : Fin d → ℕ)
      (_hDlayers : ∀ j, D.filtration.layer j = Submodule.span ℚ (D.basis '' {i | j ≤ ω i}))
      (τ : κ → ℕ) (_hFlayers : ∀ j, F.layer j = Submodule.span ℚ (c '' {i | j ≤ τ i}))
      (φ : L →ₗ⁅ℚ⁆ T) (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ F.layer j),
      (∀ j, ∀ y ∈ F.layer j, ∃ x ∈ D.filtration.layer j, φ x = y) →
      ∀ w : σ → ℕ, (∀ i, 0 < w i) → ∀ p : ℝ,
      0 ≤ p → D.GeometryComplexityLE p → (Fintype.card σ : ℝ) ≤ p →
      (Fintype.card κ : ℝ) ≤ p →
      (∀ i j, rationalLogHeight (c.repr (φ (D.basis j)) i) ≤ p) →
      ∃ (S : T →ₗ[ℚ] L) (hS : ∀ j, ∀ y ∈ F.layer j, S y ∈ D.filtration.layer j),
        Function.RightInverse S φ ∧
        (∀ i j, RationalHeightLE (D.basis.repr (S (c j)) i)
          (rationalKernelHeight (Fintype.card κ) ⌈Real.exp p⌉₊)) ∧
        ∀ l : ℕ, 0 < l → (l : ℝ) ≤ Real.exp p →
          ∀ Tbox : σ → ℝ, (∀ i, 0 < Tbox i) →
            ∀ slow : ℝ, slow ≤ Real.exp ((p + 2) ^ a) →
              Nonempty (ExternalMarkedAffineSliceFreezing.Dictionary (X := X)
                D F c φ hφ w S hS l Tbox slow (Real.exp (-((p + 2) ^ u)))
                (Real.exp ((p + C) ^ C))) := by
  obtain ⟨C, hC, hbase⟩ := exists_uniform_external_marked_affine_slice_freezing s a u
  refine ⟨C, hC, ?_⟩
  intro X σ κ L T _ _ _ _ _ _ _ _ _ _ _ d t D F c ω hDlayers τ hFlayers φ hφ hsurj
    w hw p hp hD hσ hκ hφb
  obtain ⟨S, hS, hright, hSb, hfreeze⟩ := hbase D F c ω hDlayers τ hFlayers φ hφ hsurj
    w hw p hp hD hσ hκ hφb
  refine ⟨S, hS, hright, hSb, ?_⟩
  intro l hl hlp Tbox hT slow hslow
  obtain ⟨dictionary⟩ := (hfreeze l hl hlp Tbox hT).exists_dictionary
  exact ⟨dictionary.mono_slow hT hslow⟩

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeMarkedFreezingPhysicalData
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct

noncomputable def nativeMarkedFreezingExponent (s a : ℕ) : ℕ :=
  Classical.choose
    (exists_uniform_external_marked_affine_slice_freezing_dictionary.{0, 0, 0, 0, 0} s a 3)

variable {X σ κ L T : Type} [Fintype σ] [DecidableEq σ] [Fintype κ] [DecidableEq κ]
    [LieRing L] [LieAlgebra ℚ L] [LieRing T] [LieAlgebra ℚ T]
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {s d t : ℕ} (D : RationalFilteredNilmanifold L s d)
    (F : NilpotentLieFiltration T t) (c : Basis κ ℚ T)
    (φ : L →ₗ⁅ℚ⁆ T) (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ F.layer j)
    (w : σ → ℕ) (l : ℕ) (Tbox : σ → ℝ) (slow p : ℝ) (C : ℕ)

omit C in

theorem exists_nativeMarkedFreezingPhysicalData
    (a : ℕ)
    (ω : Fin d → ℕ)
    (hDlayers : ∀ j, D.filtration.layer j = Submodule.span ℚ (D.basis '' {i | j ≤ ω i}))
    (τ : κ → ℕ)
    (hFlayers : ∀ j, F.layer j = Submodule.span ℚ (c '' {i | j ≤ τ i}))
    (hsurj : ∀ j, ∀ y ∈ F.layer j, ∃ x ∈ D.filtration.layer j, φ x = y)
    (hw : ∀ i, 0 < w i) (hp : 0 ≤ p) (hD : D.GeometryComplexityLE p)
    (hσ : (Fintype.card σ : ℝ) ≤ p) (hκ : (Fintype.card κ : ℝ) ≤ p)
    (hmap : ∀ i j, rationalLogHeight (c.repr (φ (D.basis j)) i) ≤ p)
    (hl : 0 < l) (hlp : (l : ℝ) ≤ Real.exp p)
    (hT : ∀ i, 0 < Tbox i) (hslow : slow ≤ Real.exp ((p + 2) ^ a)) :
    Nonempty (NativeMarkedFreezingPhysicalData (X := X) D F c φ hφ w l Tbox slow p
      (nativeMarkedFreezingExponent s a)) := by
  let C := nativeMarkedFreezingExponent s a
  obtain ⟨sectionMap, hsection, hright, hheight, hdict⟩ :=
    (Classical.choose_spec
      (exists_uniform_external_marked_affine_slice_freezing_dictionary.{0, 0, 0, 0, 0} s a 3)).2
      (X := X) D F c ω hDlayers τ hFlayers φ hφ hsurj w hw p hp hD hσ hκ hmap
  obtain ⟨dictionary⟩ := hdict l hl hlp Tbox hT slow hslow
  have hp1 : 0 ≤ p + 1 := by linarith
  have hp_le : p ≤ p + 1 := le_add_of_nonneg_right zero_le_one
  have hceil : (⌈Real.exp p⌉₊ : ℝ) ≤ Real.exp (p + 1) := ceil_exp_le_exp_add_one hp
  have hmatrix : ∀ i j, RationalHeightLE (LinearMap.toMatrix c D.basis sectionMap i j)
      (rationalKernelHeight (Fintype.card κ) ⌈Real.exp p⌉₊) := by
    simpa only [LinearMap.toMatrix_apply] using hheight
  have hsectionBound := rationalKernelHeight_le_budget (Fintype.card κ) ⌈Real.exp p⌉₊
    hp1 (hκ.trans hp_le) hceil
  have hden := real_image_section_denominator_bound
    (LinearMap.toMatrix c D.basis sectionMap) ⌈Real.exp p⌉₊ l hmatrix hp1
    (hκ.trans hp_le) (by simpa only [Fintype.card_fin] using hD.1.trans hp_le)
    hceil (hlp.trans (Real.exp_le_exp.mpr hp_le))
  have hb := nativeMarkedFreezingPhysicalParameter_bounds hp C
  refine ⟨⟨sectionMap, hsection, hright, hmatrix, ?_, dictionary, ?_⟩⟩
  · exact hsectionBound.trans (Real.exp_le_exp.mpr (by
      simpa only [show p + 1 + 2 = p + 3 by ring] using hb.2.2.1))
  · calc
      _ = ((matrixDenominator (LinearMap.toMatrix c D.basis sectionMap) * l : ℕ) : ℝ) *
          dictionary.denominator := by rw [Nat.cast_mul]
      _ ≤ Real.exp ((p + 1 + 2) ^ 36) * Real.exp ((p + C) ^ C) :=
        mul_le_mul hden dictionary.denominator_bound (Nat.cast_nonneg _)
          (Real.exp_nonneg _)
      _ = Real.exp (nativeMarkedFreezingPhysicalParameter p C) := by
        rw [← Real.exp_add]
        congr 1
        simp only [nativeMarkedFreezingPhysicalParameter, show p + 1 + 2 = p + 3 by ring]

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ActualFixedSpatialSlicedForecastSourceLaw
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable {X : Type} [Fintype X] [DecidableEq X]
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable (Dmod : ℕ) {Lrank : ℕ}
variable (spatial : Fin Lrank ↪ G)
variable (kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G)
variable (block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j,a.val⟩)
variable {Tsp : Type} [Fintype Tsp]
variable (spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)) (Wsp Lsp : ℝ)
variable (physicalN : X → ℕ) (τ δslice P Pbad Ppres : ℝ)

namespace ActualFixedSpatialSlicedForecastPath
variable {B U b S hR hσ Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice P Pbad Ppres}
variable (slice : ActualFixedSpatialSlicedForecastPath (Eout := Eout) B U b S hR hσ
  Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice P Pbad Ppres)

omit [Fintype Tsp] in
theorem principalSupport (j : PrincipalTupleIndex B (layerSamplerDegree I n)) :
    integerProgressionSupport (slice.principalStart j) (slice.principalStep j : ℤ)
      (slice.principalLength j) ⊆ Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U b S j : ℤ) :=
  integerProgressionSupport_subset_of_fin _ _ _ _ (slice.principalInside j)

end ActualFixedSpatialSlicedForecastPath
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.ActualFixedSpatialSlicedAnalyticIdentification
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable {X : Type} [Fintype X] [DecidableEq X]
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable (Dmod : ℕ) {Lrank : ℕ}
variable (spatial : Fin Lrank ↪ G)
variable (kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G)
variable (block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j,a.val⟩)
variable {Tsp : Type} [Fintype Tsp]
variable (spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)) (Wsp Lsp : ℝ)
variable (physicalN : X → ℕ) (τ δslice P Pbad Ppres : ℝ)

namespace ActualFixedSpatialSlicedForecastPath
variable {B U b S hR hσ Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice P Pbad Ppres}
variable (slice : ActualFixedSpatialSlicedForecastPath (Eout := Eout) B U b S hR hσ
  Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice P Pbad Ppres)

local notation "Active" => {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a}

omit [Fintype Tsp] in
theorem activeSide (a : Active) (p : B a.val × Fin (layerSamplerDegree I n a.val)) :
    allocatedPrincipalSides B U b S ⟨a.val,p⟩ = S.value :=
  allocatedPrincipalSides_long_of_not_short B U b S a.val a.property p.1 p.2

omit [Fintype Tsp] in
theorem activeLength_two (hδ : 0 < δslice)
    (a : Active) (p : B a.val × Fin (layerSamplerDegree I n a.val)) :
    2 ≤ slice.principalLength ⟨a.val,p⟩ := by
  by_contra h
  have hlen : slice.principalLength ⟨a.val,p⟩ - 1 = 0 := by omega
  have hw := slice.path.hwidth a p
  rw [slice.width_eq a p, hlen, Nat.cast_zero, mul_zero, zero_div] at hw
  exact (not_le_of_gt hδ) hw

omit [Fintype Tsp] in
theorem activeSupport (a : Active) (p : B a.val × Fin (layerSamplerDegree I n a.val)) :
    integerProgressionSupport (slice.principalStart ⟨a.val,p⟩) (slice.step : ℤ)
      (slice.principalLength ⟨a.val,p⟩) ⊆ Finset.Ico (0 : ℤ) (S.value : ℤ) := by
  simpa only [slice.principalStep_active a p, activeSide (B := B) (U := U) (b := b) (S := S) a p] using
    slice.principalSupport ⟨a.val,p⟩

end ActualFixedSpatialSlicedForecastPath
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable {X : Type} [Fintype X] [DecidableEq X]
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable (Dmod : ℕ) {Lrank : ℕ}
variable (spatial : Fin Lrank ↪ G)
variable (kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G)
variable (block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j,a.val⟩)
variable {Tsp : Type} [Fintype Tsp]
variable (spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp))
variable (physicalN : X → ℕ) (τ δslice P Pbad Ppres : ℝ)

namespace ActualFixedSpatialSlicedForecastPath
variable {B U b S hR hσ Dmod spatial kernel block spatialEquiv physicalN τ δslice P Pbad Ppres}
variable (slice : ActualFixedSpatialSlicedForecastPath (Eout := Eout) B U b S hR hσ
  Dmod spatial kernel block spatialEquiv (allocatedPhysicalRootBudget B U b S (fun _ => 0)) (S.value : ℝ) physicalN τ δslice P Pbad Ppres)

omit [Fintype Tsp] in
theorem normalizedNoise_eq_kernelFrame (ξ : ℝ) :
    slice.path.normalizedNoise =
      allocatedFixedPathKernelFrame B U b S τ ξ physicalN slice.path.noise := by
  funext k
  rcases k with ⟨_ | g, x⟩ <;>
    rfl

end ActualFixedSpatialSlicedForecastPath
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.ActualFixedSpatialSlicedPrimitiveGeometry
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {X : Type} [Fintype X] [DecidableEq X]
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable {A : Type} [Fintype A]
variable {Dmod : ℕ} {selected : A → Σ j : Fin m, Fin (n j)}
variable {τ δslice : ℝ}

namespace ActualFixedSpatialForecastSetup
variable (s : ActualFixedSpatialForecastSetup (X := X) (Eout := Eout) B U b S Dmod selected τ δslice)

noncomputable def slicedGeometryDimension : ℝ := s.P + (layerTailDegree m + 1 : ℕ) + 1
noncomputable def slicedGeometryRadiusLog : ℝ := s.P + s.Pscale

end ActualFixedSpatialForecastSetup
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.ActualFixedSpatialSlicedTargetReal
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable {X : Type} [Fintype X] [DecidableEq X]
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable (Dmod : ℕ) {Lrank : ℕ}
variable (spatial : Fin Lrank ↪ G)
variable (kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G)
variable (block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j,a.val⟩)
variable {Tsp : Type} [Fintype Tsp]
variable (spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)) (Wsp Lsp : ℝ)
variable (physicalN : X → ℕ) (τ δslice P Pbad Ppres : ℝ)

namespace ActualFixedSpatialForecastPath
variable {B U b S hR hσ Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice P Pbad Ppres}
variable (path : ActualFixedSpatialForecastPath (Eout := Eout) B U b S hR hσ
  Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice P Pbad Ppres)

noncomputable def referenceModulus : ℕ := ∏ p : path.primes, p.val ^ path.exponent p.val

omit [Fintype Tsp] in
theorem referenceModulus_pos : 0 < path.referenceModulus := by
  apply Finset.prod_pos
  intro p _
  exact pow_pos (path.prime p.val p.property).pos _

local instance actualPathReferenceNeZero : NeZero path.referenceModulus :=
  ⟨path.referenceModulus_pos.ne'⟩

noncomputable def referencePolynomial :=
  allocatedForecastPolynomial (allocatedShortAxis (I := I) U b S.value) path.base path.noise
    (allocatedReadDeck path.read) (fun j a => allocatedReadProjection path.read ⟨j,a.val⟩)

noncomputable def referenceInputLaw : FiniteProbabilityWeights
    (LayerSamplerLongVariables (allocatedShortAxis (I := I) U b S.value) G B →
      ZMod path.referenceModulus) := by
  letI := path.primeNeZero
  exact crtPolynomialInputLaw (fun p : path.primes => p.val)
    (fun p : path.primes => path.exponent p.val) (fun p : path.primes => path.prescribed p.val)
    (primePower_crt_coprime (fun p : path.primes => p.val)
      (fun p : path.primes => path.exponent p.val)
      (fun p => path.prime p.val p.property) Subtype.val_injective) path.origin

end ActualFixedSpatialForecastPath
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.ActualFixedSpatialSlicedDensityIdentification
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable {X : Type} [Fintype X] [decX : DecidableEq X]
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable (Dmod : ℕ) {Lrank : ℕ}
variable (spatial : Fin Lrank ↪ G)
variable (kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G)
variable (block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j,a.val⟩)
variable {Tsp : Type} [Fintype Tsp]
variable (spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp))
variable (physicalN : X → ℕ) (τ δslice P Pbad Ppres : ℝ)

namespace ActualFixedSpatialSlicedForecastPath
variable {B U b S hR hσ Dmod spatial kernel block spatialEquiv physicalN τ δslice P Pbad Ppres}
variable (slice : ActualFixedSpatialSlicedForecastPath (Eout := Eout) B U b S hR hσ
  Dmod spatial kernel block spatialEquiv (allocatedPhysicalRootBudget B U b S (fun _ => 0)) (S.value : ℝ) physicalN τ δslice P Pbad Ppres)

omit [Fintype Tsp] in
theorem analyticKernelDetFalse (ξ : ℝ) :
    let M := fixedSpatialKernelBlock spatialEquiv (allocatedPhysicalRootBudget B U b S (fun _ => 0))
      (S.value : ℝ) (allocatedFixedPathKernelFrame B U b S τ ξ physicalN slice.path.noise) false
    let := Classical.decEq X
    M.det ≠ 0 := by
  cases Subsingleton.elim decX (Classical.decEq X)
  let := Classical.decEq X
  rw [← slice.normalizedNoise_eq_kernelFrame ξ]
  exact slice.path.detFalse

omit [Fintype Tsp] in
theorem analyticKernelDetTrue (ξ : ℝ) :
    let M := fixedSpatialKernelBlock spatialEquiv (allocatedPhysicalRootBudget B U b S (fun _ => 0))
      (S.value : ℝ) (allocatedFixedPathKernelFrame B U b S τ ξ physicalN slice.path.noise) true
    let := Classical.decEq X
    M.det ≠ 0 := by
  cases Subsingleton.elim decX (Classical.decEq X)
  let := Classical.decEq X
  rw [← slice.normalizedNoise_eq_kernelFrame ξ]
  exact slice.path.detTrue

end ActualFixedSpatialSlicedForecastPath
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.ActualFixedSpatialSlicedDataComparison
namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable {X : Type} [Fintype X] [decX : DecidableEq X]
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable (Dmod : ℕ) {Lrank : ℕ}
variable (spatial : Fin Lrank ↪ G)
variable (kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G)
variable (block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j,a.val⟩)
variable {Tsp : Type} [Fintype Tsp]
variable (spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp))
variable (physicalN : X → ℕ) (τ δslice P Pbad Ppres : ℝ)

namespace ActualFixedSpatialSlicedForecastPath
variable {B U b S hR hσ Dmod spatial kernel block spatialEquiv physicalN τ δslice P Pbad Ppres}
variable (slice : ActualFixedSpatialSlicedForecastPath (Eout := Eout) B U b S hR hσ
  Dmod spatial kernel block spatialEquiv (allocatedPhysicalRootBudget B U b S (fun _ => 0)) (S.value : ℝ) physicalN τ δslice P Pbad Ppres)

variable (s : ActualFixedSpatialForecastSetup (X := X) (Eout := Eout)
  B U b S Dmod (allocatedShortIntegerSelection U b S.value) τ δslice)
variable (hb : ∀ j, Submodule.span ℤ (Set.range (b j)) =
  projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable {periodCap coverCap : ℝ} {Lip : ℝ≥0}
variable (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap Lip)
variable (originalpoly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hmem : ∀ j d, coefficients (originalpoly j) d ∈ U j)
variable (hdegree : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (originalpoly j))
variable (ξ : ℝ) (hξ : 0 < ξ)
variable (hbox : ∀ x, 0 < physicalN x)
variable (hframe : slice.path.noise ∈ rectangularWeightIndices 0
  (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n))
    (allocatedPhysicalRootBudget B U b S (fun _ => 0)) τ ξ physicalN) 1)
variable {t δ ε η : ℝ} (ht : 0 < t) (hσbound : ∀ j, |σ j| ≤ t)
variable (hδ : 0 < δ) (hδone : δ ≤ 1)
variable (hdense : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a},
  ∀ p : B a.val × Fin (layerSamplerDegree I n a.val), δ * S.value ≤
    ((integerProgressionSupport (slice.principalStart ⟨a.val,p⟩) (slice.step : ℤ)
      (slice.principalLength ⟨a.val,p⟩)).card : ℝ))
variable (q : ℕ) [NeZero q]
variable (hperiod : W.modulus ∣ q) (hcover : W.cover ∣ q)
variable (hqN : q ∣ slice.path.referenceModulus)
variable (hsizeG : ∀ g, q ≤ slice.kernelLength g)
variable (hsmallG : ∀ g, scalarCubeGridBoundaryConstant Empty * ((q : ℝ) / slice.kernelLength g) < 1)
variable (hsize : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a},
  ∀ p : B a.val × Fin (layerSamplerDegree I n a.val), q ≤ slice.principalLength ⟨a.val,p⟩)
variable (hsmall : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a},
  ∀ p : B a.val × Fin (layerSamplerDegree I n a.val),
    scalarCubeGridBoundaryConstant Empty * ((q : ℝ) / slice.principalLength ⟨a.val,p⟩) < 1)
variable (hε : 0 ≤ ε) (hmesh : (slice.step : ℝ) / S.value ≤ ε)
variable (hη : 0 < η)
variable (htail : |t| * polynomialMassC2Budget
  (Fintype.card (Σ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a},
    B a.val × Fin (layerSamplerDegree I n a.val))) m 1 ≤
  slicedPrincipalC2Tolerance
    (Fintype.card (Σ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a},
      B a.val × Fin (layerSamplerDegree I n a.val)))
    (Fintype.card {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a}) m 1
    (unitProfilePrincipalLowerBound B) (δ / 2) s.L η)

local instance actualComparisonReferenceNeZero : NeZero slice.path.referenceModulus :=
  ⟨slice.path.referenceModulus_pos.ne'⟩

noncomputable def decayConstant : ℝ :=
  ((slice.path.Rbad * ∏ p : slice.path.primes, p.val ^ slice.path.prescribed p.val : ℕ) : ℝ) ^
    (modularRankDecayExponent m (modularForecastRankConstant m Dmod : ℝ) * modularRankChargeFactor m)

end ActualFixedSpatialSlicedForecastPath
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.ActualFixedSpatialSlicedModelPrecision
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable {U : ∀ j, Submodule ℝ (J j → ℝ)}
variable {b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
variable {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
variable {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
variable {X : Type} [Fintype X] [DecidableEq X]
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable {Dmod Lrank : ℕ} {spatial : Fin Lrank ↪ G}
variable {kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G}
variable {block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j,a.val⟩}
variable {Tsp : Type} [Fintype Tsp] {spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)}
variable {physicalN : X → ℕ} {τ cost : ℝ}
variable (s : ActualFixedSpatialForecastSetup (X := X) (Eout := Eout)
  B U b S Dmod (allocatedShortIntegerSelection U b S.value) τ (Real.exp (-cost) / 2))
variable (slice : ActualFixedSpatialSlicedForecastPath (Eout := Eout) B U b S hR hσ
  Dmod spatial kernel block spatialEquiv (allocatedPhysicalRootBudget B U b S (fun _ => 0))
  (S.value : ℝ) physicalN τ (Real.exp (-cost) / 2) s.P s.Pbad s.Ppres)

namespace ActualFixedSpatialSlicedForecastPath

noncomputable def comparisonGridLog (Pu : ℝ) : ℝ :=
  max Pu (max (forecastOriginalSmoothBudget m (s.P + (Fintype.card X + 1) * (cost + 1)))
    ((s.Pbad + s.Ppres) * ((Dmod + 2 : ℕ) : ℝ) * modularRankChargeFactor m))

noncomputable def comparisonPrecisionFloor (d : ℕ) (Pu V E : ℝ) : ℕ :=
  max (fixedPathSlicedGridMeshFloor s.D 4 V cost (2 * Pu + (E + 4) + 14))
    (forecastJointGridSamplerFloor d (comparisonGridLog s Pu) (E + 4) V s.PK)

end ActualFixedSpatialSlicedForecastPath
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.ActualFixedSpatialSlicedSourceLog
namespace OAI

section

namespace Erdos3.VectorPolynomial.ActualFixedSpatialForecastSetup
open scoped BigOperators NNReal

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable {U : ∀ j, Submodule ℝ (J j → ℝ)}
variable {b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
variable {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
variable {X : Type} [Fintype X] {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable {A : Type} {Dmod : ℕ} {selected : A → Σ j, Fin (n j)}
variable {τ δslice : ℝ}
variable (s : ActualFixedSpatialForecastSetup (X := X) (Eout := Eout) B U b S Dmod selected τ δslice)

noncomputable def slicedComparisonSourceLog (Ptest : ℝ) : ℝ :=
  2 + s.D * s.D + s.pcap + max 0 Ptest

end Erdos3.VectorPolynomial.ActualFixedSpatialForecastSetup

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.NativePairChartSymbol
namespace OAI

universe universeLevel

section

namespace Erdos3.RationalFilteredNilmanifold

open Module VectorPolynomial NilpotentLieFiltration
open scoped TensorProduct BigOperators

attribute [local instance_reducible] BoolLieFamily

variable {L M : Type universeLevel} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s d e : ℕ} (D : RationalFilteredNilmanifold L s d)
    (E : RationalFilteredNilmanifold M s e)
    {σ τ ι : Type*} {w : σ → ℕ} {v : τ → ℕ}

attribute [local irreducible] realChartSubstitute polynomialOrbitRealChart
  weightedAdaptedRealChartHom realPolynomialSymbolHom realSymbolHomogeneousPullbackHom

attribute [local irreducible] pairOrbit

theorem pairOrbitSymbol_chart_eq_of_homogeneous_eq
    (p : D.filtration.realification.PolynomialOrbit w)
    (q : E.filtration.realification.PolynomialOrbit w)
    (b : Basis ι ℚ (PairAlgebra L M)) (ω : ι → ℕ)
    (hF : ∀ k, (pi (pairModels D E)).filtration.layer k =
      Submodule.span ℚ (b '' {i | k ≤ ω i}))
    (β : σ → MvPolynomial τ ℝ)
    (hβ : ∀ i, β i ∈ weightedSupportLE v (w i))
    (β' : σ → MvPolynomial τ ℝ)
    (hβ' : ∀ i, β' i ∈ weightedSupportLE v (w i))
    (htop : (fun i => MvPolynomial.weightedHomogeneousComponent v (w i) (β i)) =
      (fun i => MvPolynomial.weightedHomogeneousComponent v (w i) (β' i))) :
    pairOrbitSymbol D E (D.filtration.polynomialOrbitRealChart w v β hβ p)
      (E.filtration.polynomialOrbitRealChart w v β hβ q) b ω hF =
    pairOrbitSymbol D E (D.filtration.polynomialOrbitRealChart w v β' hβ' p)
      (E.filtration.polynomialOrbitRealChart w v β' hβ' q) b ω hF := by
  rw [pairOrbitSymbol_polynomialOrbitRealChart, pairOrbitSymbol_polynomialOrbitRealChart,
    realPolynomialSymbolHom_weightedAdaptedRealChart,
    realPolynomialSymbolHom_weightedAdaptedRealChart]
  congr 1
  congr 1

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.ActualFixedSpatialUnchargedDensity
namespace OAI

section

namespace Erdos3.VectorPolynomial
open _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable {U : ∀ j, Submodule ℝ (J j → ℝ)}
variable {b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
variable {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
variable {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
variable {X : Type} [Fintype X] [DecidableEq X]
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable {Dmod Lrank : ℕ}
variable {spatial : Fin Lrank ↪ G}
variable {kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G}
variable {block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j,a.val⟩}
variable {Tsp : Type} [Fintype Tsp]
variable {spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)} {Wsp Lsp : ℝ}
variable {physicalN : X → ℕ} {τ δslice P Pbad Ppres : ℝ}

namespace ActualFixedSpatialForecastPath

variable (path : ActualFixedSpatialForecastPath (Eout := Eout) B U b S hR hσ
  Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice P Pbad Ppres)

noncomputable def localReferencePolynomial
    (raw : PrincipalTupleIndex B (layerSamplerDegree I n) × Option Empty → ℤ)
    (j : Fin m) : AllocatedCongruenceRankOutput X Eout
      (allocatedShortAxis (I := I) U b S.value) j →
      MvPolynomial (LayerSamplerLongVariables (allocatedShortAxis (I := I) U b S.value) G B) ℤ :=
  allocatedCongruenceIntegerPolynomial (allocatedShortAxis (I := I) U b S.value) j
    path.base path.noise (allocatedReadDeck path.read)
    (fun a => allocatedReadProjection path.read ⟨j, a.val⟩)
    (samplerFrozenRaw (layerSamplerDegree I n) raw)

end ActualFixedSpatialForecastPath
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ActualFixedSpatialGoodPrimeDeletion
namespace OAI

section

namespace Erdos3.VectorPolynomial
open _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable {U : ∀ j, Submodule ℝ (J j → ℝ)}
variable {b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
variable {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
variable {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
variable {X : Type} [Fintype X] [DecidableEq X]
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable {Dmod Lrank : ℕ}
variable {spatial : Fin Lrank ↪ G}
variable {kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G}
variable {block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j,a.val⟩}
variable {Tsp : Type} [Fintype Tsp]
variable {spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)} {Wsp Lsp : ℝ}
variable {physicalN : X → ℕ} {τ δslice P Pbad Ppres : ℝ}

namespace ActualFixedSpatialForecastPath

variable (path : ActualFixedSpatialForecastPath (Eout := Eout) B U b S hR hσ
  Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice P Pbad Ppres)

local instance retainedReferencePrimeNeZero_r6144b1_1 : ∀ p : path.primes, NeZero p.val :=
  path.primeNeZero
local instance retainedReferenceModulusNeZero : NeZero path.referenceModulus :=
  ⟨path.referenceModulus_pos.ne'⟩

end ActualFixedSpatialForecastPath
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.ControlledProjectionUniformBudget
namespace OAI

universe u

section

universe v

namespace Erdos3.RationalFilteredNilmanifold

open Module VectorPolynomial NilpotentLieFiltration
open scoped TensorProduct

variable {ι : Type v} {L₀ : Type u} {L : ι → Type u}
  [LieRing L₀] [∀ i, LieRing (L i)] [LieAlgebra ℚ L₀] [∀ i, LieAlgebra ℚ (L i)]

variable [Fintype ι] {s d₀ : ℕ} {d : ι → ℕ}
  (D₀ : RationalFilteredNilmanifold L₀ s d₀)
  (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i)) (j : ι)

variable {α β σ : Type*}
  (e : Basis α ℚ (∀ i : Option ι, optionLieSpace L₀ L i)) (ω : α → ℕ)
  (hF : ∀ k, (optionProduct D₀ D).filtration.layer k =
    Submodule.span ℚ (e '' {i | k ≤ ω i}))
  (b : Basis β ℚ (PairAlgebra L₀ (L j))) (ν : β → ℕ)
  (hG : ∀ k, (pi (pairModels D₀ (D j))).filtration.layer k =
    Submodule.span ℚ (b '' {i | k ≤ ν i}))

theorem optionPairProjection_jointOrbitSymbol {w : σ → ℕ}
    (g : ∀ i, (optionFactors D₀ D i).filtration.realification.PolynomialOrbit w) :
    (optionProduct D₀ D).filtration.realSymbolProjection
      (pi (pairModels D₀ (D j))).filtration
      (optionPairProjection j) (optionPairProjection_layers D₀ D j) w
      ((optionProduct D₀ D).filtration.realPolynomialSymbolHom e ω hF w
        ⟨⟨(piRealOrbit (fun i => (optionFactors D₀ D i).filtration) g).log,
          (piRealOrbit (fun i => (optionFactors D₀ D i).filtration) g).property⟩⟩) =
      pairOrbitSymbol D₀ (D j) (g none) (g (some j)) b ν hG := by
  apply NilpotentLieBCHGroup.ext
  have h := (optionProduct D₀ D).filtration.realFilteredPolynomialSymbolMap_polynomial
    (pi (pairModels D₀ (D j))).filtration
    (optionPairProjection j) (optionPairProjection_layers D₀ D j)
    e ω hF b ν hG w
    ⟨(piRealOrbit (fun i => (optionFactors D₀ D i).filtration) g).log,
      (piRealOrbit (fun i => (optionFactors D₀ D i).filtration) g).property⟩
  change _ = (pi (pairModels D₀ (D j))).filtration.realSymbolOfPolynomial b ν hG w
    (pairOrbit D₀ (D j) (g none) (g (some j))).log
  exact h.trans (congrArg
    ((pi (pairModels D₀ (D j))).filtration.realSymbolOfPolynomial b ν hG w)
    (optionPairProjection_piRealOrbit_log D₀ D j g))

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end


