-- Prove2me | Definitions.Def_OAIErdos3B158
-- name    : OAIErdos3B158
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-10T01:26:35.139898+00:00
-- url     : https://prove2.me/theorems/a3ebbd1a-4b4e-4314-9882-175e36efd772
-- title:
--   OpenAI Erdős-3 split, definitions bundle 159 of 177
-- statement:
--   Definitions bundle 159 of 177 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs) and OpenAI's `@[simp]` lemmas from the same modules.
--
--   It imports the previous bundle `OAIErdos3B157`, so the bundles form a chain and importing this one makes the definitions of bundles 1 to 159 available.
--
--   Modules: `OAI.Erdos3.ResidueBoxSlice.fin_mean_eq_translated_zero`, `OAI.Erdos3.ResidueBoxSlice.fullSlicePoint_normalized_distance_le`, `OAI.Erdos3.VectorPolynomial.NormalizedPolynomialTwist.exists_niltest_pair_correlation_subrectangle_of_variation`, `OAI.Erdos3.VectorPolynomial.NormalizedPolynomialTwist.exists_untwisted_subrectangle_of_fullSliceLaw_of_variation`, `OAI.Erdos3.VectorPolynomial.NormalizedPolynomialTwist.forecastResidueTest`, `OAI.Erdos3.VectorPolynomial.exists_allocatedCoefficient_integer_event_read`, `OAI.Erdos3.VectorPolynomial.exists_coefficientDeck_integer_event_read`, `OAI.Erdos3.VectorPolynomial.exists_coefficientDeck_integer_lift`, `OAI.Erdos3.VectorPolynomial.forecastNativeAmbientDeckResidue`, `OAI.Erdos3.VectorPolynomial.forecastNativeCoordinateResidue`, `OAI.Erdos3.VectorPolynomial.forecastNativeDeckResidueMatrix`, `OAI.Erdos3.VectorPolynomial.forecastNativeFreeDeckResidue`, `OAI.Erdos3.VectorPolynomial.forecastNativeSheetResidue`, `OAI.Erdos3.VectorPolynomial.forecastNativeSpatialResidue`, `OAI.Erdos3.VectorPolynomial.singleSiteHaar_ambientIntegerCharacter_integrable`, `OAI.Erdos3.VectorPolynomial.singleSiteHaar_ambientIntegerCharacter_integral`, `OAI.Erdos3.ambientIntegerCharacter`, `OAI.Erdos3.ambientIntegerCharacter_lipschitz`, `OAI.Erdos3.ambientIntegerCharacter_norm`, `OAI.Erdos3.largestBadPrimeProduct_congr_on_tested`, `OAI.Erdos3.largestBadPrimeProduct_measurable`, `OAI.Erdos3.largestBadPrimeProduct_tail_measurableSet`, `OAI.Erdos3.largestTestedBadDepth_congr_on_tested`, `OAI.Erdos3.largestTestedBadDepth_measurable`, `OAI.Erdos3.selectedResidueDensityPMF_badProduct_event_congr`, `OAI.Erdos3.selectedResidueDensityPMF_event_congr_of_density_ne_zero`, `_private.Fourier.NormalizedTwistSingleSiteFourierHaar.0.OAI.Erdos3.VectorPolynomial.singleSiteEuclideanRow`, `_private.Fourier.NormalizedTwistSingleSiteFourierHaar.0.OAI.Erdos3.VectorPolynomial.singleSiteEuclideanRow_apply`, `_private.Fourier.NormalizedTwistSingleSiteFourierHaar.0.OAI.Erdos3.VectorPolynomial.singleSiteEuclideanRow_character`, `_private.Fourier.NormalizedTwistSingleSiteFourierHaar.0.OAI.Erdos3.VectorPolynomial.singleSiteEuclideanRow_eq_zero`, `_private.Fourier.NormalizedTwistSingleSiteFourierHaar.0.OAI.Erdos3.VectorPolynomial.singleSiteEuclideanRow_integral`, `_private.Lattices.AllocatedPhysicalIntegerRankLaw.0.OAI.Erdos3.finite_nat_sup_measurable`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B054
import Definitions.Def_OAIErdos3B147
import Definitions.Def_OAIErdos3B151
import Definitions.Def_OAIErdos3B152
import Definitions.Def_OAIErdos3B161

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NormalizedTwistSliceVariationPairCorrelation
namespace OAI

section

namespace Erdos3.VectorPolynomial.NormalizedPolynomialTwist

open BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {A K X : Type*} [Fintype A] [Fintype K] [DecidableEq K] [Fintype X]
variable {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable {periodCap coverCap : ℝ} {L : ℝ≥0}

end Erdos3.VectorPolynomial.NormalizedPolynomialTwist

end

section

namespace Erdos3.VectorPolynomial.NormalizedPolynomialTwist

open BooleanCubeKernel
open scoped BigOperators Classical NNReal

end Erdos3.VectorPolynomial.NormalizedPolynomialTwist

end

section

namespace Erdos3.VectorPolynomial.NormalizedPolynomialTwist

open BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {A K X : Type*} [Fintype A] [Fintype K] [DecidableEq K] [Fintype X]
variable {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable {periodCap coverCap : ℝ} {L : ℝ≥0}

end Erdos3.VectorPolynomial.NormalizedPolynomialTwist

end

section

namespace Erdos3

open scoped BigOperators Classical TensorProduct NNReal

namespace ResidueBoxSlice

theorem fin_mean_eq_translated_zero {K : Type*} [Fintype K] [DecidableEq K]
    {P : K → ℕ} {q : ℕ} (T : ResidueBoxSlice P q) (f : (K → ℤ) → ℂ) :
    (𝔼 t : (∀ k, Fin (T.length k)), f (T.fullSlicePointInIntegerBox t).val) =
      𝔼 x ∈ translatedIntegerBox (0 : K → ℤ) T.length,
        f (fun k => (q : ℤ) * x k + T.start k) := by
  have hzero : translatedIntegerBox (0 : K → ℤ) T.length = integerBox T.length := by
    ext x
    simp only [mem_translatedIntegerBox, mem_integerBox, Pi.zero_apply, zero_add]
  rw [hzero, integerBox_expect_eq_fin]
  apply Finset.expect_congr rfl
  intro t _
  congr 1
  funext k
  simp only [fullSlicePointInIntegerBox, point, Nat.cast_add, Nat.cast_mul, add_comm]

end ResidueBoxSlice

namespace VectorPolynomial.NormalizedPolynomialTwist

open BooleanCubeKernel

end VectorPolynomial.NormalizedPolynomialTwist
end Erdos3

end

section

namespace Erdos3

open BooleanCubeKernel
open scoped BigOperators Classical

namespace ResidueBoxSlice

theorem fullSlicePoint_normalized_distance_le
    {K : Type*} [Fintype K] [DecidableEq K] {P : K → ℕ} {q : ℕ}
    (S : ResidueBoxSlice P q) (htwo : ∀ k, 2 ≤ S.length k)
    (u v : ∀ k, Fin (S.length k)) {η : ℝ}
    (hnear : ∀ k, |((u k).val : ℝ) / S.length k -
      ((v k).val : ℝ) / S.length k| ≤ η) (k : K) :
    |((S.fullSlicePointInIntegerBox u).val k : ℝ) / P k -
      ((S.fullSlicePointInIntegerBox v).val k : ℝ) / P k| ≤ 2 * η := by
  have htwoK := htwo k
  have hlen : (0 : ℝ) < S.length k := by exact_mod_cast (by omega : 0 < S.length k)
  have hP : (0 : ℝ) < P k := by
    have h := S.inside k 0 (by omega)
    exact_mod_cast (show 0 < P k by omega)
  have hspan : (q : ℝ) * S.length k ≤ 2 * (P k : ℝ) := by
    exact_mod_cast S.stride_mul_length_le_twice k (htwo k)
  have hfac : (q : ℝ) * S.length k / P k ≤ 2 := (div_le_iff₀ hP).mpr hspan
  have hfac0 : 0 ≤ (q : ℝ) * S.length k / P k := by positivity
  have heq : ((S.fullSlicePointInIntegerBox u).val k : ℝ) / P k -
      ((S.fullSlicePointInIntegerBox v).val k : ℝ) / P k =
      ((q : ℝ) * S.length k / P k) *
        (((u k).val : ℝ) / S.length k - ((v k).val : ℝ) / S.length k) := by
    simp only [fullSlicePointInIntegerBox, point, Nat.cast_add, Nat.cast_mul, Int.cast_add, Int.cast_mul, Int.cast_natCast]
    field_simp
    ring
  rw [heq, abs_mul, abs_of_nonneg hfac0]
  exact mul_le_mul hfac (hnear k) (abs_nonneg _) (by norm_num)

end ResidueBoxSlice

namespace VectorPolynomial.NormalizedPolynomialTwist

theorem exists_untwisted_subrectangle_of_fullSliceLaw_of_variation
    {K : Type*} [Fintype K] [DecidableEq K]
    {P : K → ℕ} {q : ℕ} (S : ResidueBoxSlice P q) (hq : 0 < q)
    (hlen : ∀ k, 0 < S.length k) {cost p : ℝ} (hp : 0 ≤ p)
    (hS : ∀ k, Real.exp (-cost) * (P k : ℝ) ≤ S.length k)
    (hP : ∀ k, Real.exp (cost + (3 * p + 16)) ≤ (P k : ℝ))
    {M : ℕ} (hM : 0 < M) (hMexp : (M : ℝ) ≤ Real.exp p)
    (twist : integerBox P → ℂ) (htwist : ∀ t, ‖twist t‖ ≤ 1)
    {ε : ℝ}
    (hvariation : ∀ u v : integerBox P,
      (∀ k, (u.val k : ZMod M) = (v.val k : ZMod M)) →
      (∀ k, |(u.val k : ℝ) / P k - (v.val k : ℝ) / P k| ≤
        2 * (Real.exp (-(2 * p)) / 4)) → ‖twist u - twist v‖ ≤ ε)
    (signal : integerBox P → ℂ) {δ : ℝ} (hδ : 0 < δ)
    (hsignal : ∀ t, ‖signal t‖ ≤ 1)
    (hbias : δ ≤ ‖(S.fullSliceLaw hlen).complexMean
      (fun t => star (twist t) * signal t)‖) :
    ∃ T : ResidueBoxSlice P (q * M),
      0 < q * M ∧ (∀ k, 0 < T.length k) ∧
      (∀ k, Real.exp (-(cost + (3 * p + 16))) * (P k : ℝ) ≤ T.length k) ∧
      δ / 2 - ε ≤
        ‖𝔼 t : (∀ k, Fin (T.length k)), signal (T.fullSlicePointInIntegerBox t)‖ := by
  have hSL : ∀ k, Real.exp (3 * p + 16) ≤ (S.length k : ℝ) :=
    fun k => S.length_large_of_cost hS hP k
  have htwo : ∀ k, 2 ≤ S.length k := by
    intro k
    have he := Real.add_one_le_exp (3 * p + 16)
    have hh := hSL k
    have : (2 : ℝ) ≤ S.length k := by linarith
    exact_mod_cast this
  let : ∀ k, Nonempty (Fin (S.length k)) := fun k => ⟨⟨0, hlen k⟩⟩
  obtain ⟨Q, hstep, hlength, hlower, _, hnear, _, _⟩ :=
    exists_normalizedTwist_parameter_partition S.length M p hp hM hMexp hSL
  let label := BoxProgressionPartition.cell Q
  let base := fun (c : ∀ k, (Q k).Label) =>
    BoxProgressionPartition.point Q c (fun k => ⟨0, hlength k (c k)⟩)
  let coefficient := fun c => twist (S.fullSlicePointInIntegerBox (base c))
  have herr (c : ∀ k, (Q k).Label) (t : ∀ k, Fin ((Q k).length (c k))) :
      ‖twist (S.fullSlicePointInIntegerBox (BoxProgressionPartition.point Q c t)) -
        coefficient c‖ ≤ ε := by
    apply hvariation
    · intro k
      simp only [ResidueBoxSlice.fullSlicePointInIntegerBox, ResidueBoxSlice.point,
        BoxProgressionPartition.point, FiniteProgressionPartition.point_val, hstep, base,
        Nat.cast_add, Nat.cast_mul, Int.cast_add, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self, Nat.cast_zero,
        zero_mul, add_zero]
    · exact S.fullSlicePoint_normalized_distance_le htwo _ _
        (fun k => hnear k (c k) (t k) ⟨0, hlength k (c k)⟩)
  let μ := FiniteProbabilityWeights.uniform (∀ k, Fin (S.length k))
  let pulledTwist := fun u => twist (S.fullSlicePointInIntegerBox u)
  let pulledSignal := fun u => signal (S.fullSlicePointInIntegerBox u)
  have hbound : δ ≤ ‖μ.complexMean (fun u => star (pulledTwist u) * pulledSignal u)‖ := by
    rw [S.fullSliceLaw_complexMean] at hbias
    simpa only [μ, pulledTwist, pulledSignal, FiniteProbabilityWeights.uniform_complexMean] using hbias
  let : Nonempty (∀ k, (Q k).Label) := ⟨fun k => (Q k).cell ⟨0, hlen k⟩⟩
  obtain ⟨c, hc, _, hb⟩ := μ.exists_large_correlating_fiber label
    (fun t => star (pulledTwist t) * pulledSignal t) hδ (fun t => by
      rw [norm_mul, norm_star]
      exact (mul_le_mul (htwist _) (hsignal _) (norm_nonneg _) zero_le_one).trans_eq
        (one_mul 1)) hbound
  let ν := μ.condition (Finset.univ.filter (fun t => label t = c)) hc
  have hcorr : δ / 2 - ε ≤ ‖ν.complexMean pulledSignal‖ := by
    apply correlation_after_freezing ν pulledTwist pulledSignal (coefficient c)
      (htwist _) (fun t => hsignal _) ?_ hb
    intro t ht
    have htc : label t = c := by
      by_contra hn
      exact ht (by simp only [ν, FiniteProbabilityWeights.condition,
        Finset.mem_filter, Finset.mem_univ, true_and, hn, ite_false, zero_div])
    have he := herr (label t) (fun k => (Q k).offset (t k))
    have hpoint : BoxProgressionPartition.point Q (label t)
        (fun k => (Q k).offset (t k)) = t := by
      funext k
      exact (Q k).point_cell_offset (t k)
    rw [hpoint, htc] at he
    exact he
  let T₀ := ResidueBoxSlice.parameterCell Q hstep c
  let T := S.composeSlice T₀
  have heval (u : ∀ k, Fin ((Q k).length (c k))) :
      T.fullSlicePointInIntegerBox u =
        S.fullSlicePointInIntegerBox (BoxProgressionPartition.point Q c u) := by
    apply Subtype.ext
    funext k
    change ((S.start k + q * (Q k).start (c k) +
      (q * M) * (u k).val : ℕ) : ℤ) =
        ((S.start k + q * ((Q k).point (c k) (u k)).val : ℕ) : ℤ)
    rw [FiniteProgressionPartition.point_val, hstep]
    push_cast
    ring
  refine ⟨T, mul_pos hq hM, fun k => hlength k (c k), ?_, ?_⟩
  · exact fun k => S.composeSlice_length_lower T₀ hS (fun k => hlower k (c k)) k
  · have hmean : ν.complexMean pulledSignal =
        𝔼 u, signal (S.fullSlicePointInIntegerBox (BoxProgressionPartition.point Q c u)) := by
      dsimp only [ν, μ, pulledSignal]
      rw [FiniteProbabilityWeights.uniform_condition_complexMean]
      have hset : Finset.univ.filter (fun t => label t = c) =
          partitionCell (BoxProgressionPartition.cell Q) c := by
        ext t
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_partitionCell, label]
      rw [hset, BoxProgressionPartition.expect_cell_complex]
    rw [hmean] at hcorr
    have hexpect : (𝔼 t : (∀ k, Fin (T.length k)), signal (T.fullSlicePointInIntegerBox t)) =
        𝔼 u : (∀ k, Fin ((Q k).length (c k))),
          signal (S.fullSlicePointInIntegerBox (BoxProgressionPartition.point Q c u)) := by
      change (𝔼 t : (∀ k, Fin ((Q k).length (c k))), signal (T.fullSlicePointInIntegerBox t)) = _
      apply Finset.expect_congr rfl
      intro t _
      rw [heval]
    rwa [hexpect]

end VectorPolynomial.NormalizedPolynomialTwist
end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical TensorProduct NNReal

namespace VectorPolynomial.NormalizedPolynomialTwist

open BooleanCubeKernel

theorem exists_niltest_pair_correlation_subrectangle_of_variation
    {K : Type*} [Fintype K] [DecidableEq K]
    {P : K → ℕ} {q : ℕ} (S : ResidueBoxSlice P q) (hq : 0 < q)
    (hlen : ∀ k, 0 < S.length k) {cost p : ℝ} (hp : 0 ≤ p)
    (hS : ∀ k, Real.exp (-cost) * (P k : ℝ) ≤ S.length k)
    (hP : ∀ k, Real.exp (cost + (3 * p + 16)) ≤ (P k : ℝ))
    {M : ℕ} (hM : 0 < M) (hMexp : (M : ℝ) ≤ Real.exp p)
    (twist : integerBox P → ℂ) (htwist : ∀ t, ‖twist t‖ ≤ 1)
    {ε : ℝ}
    (hvariation : ∀ u v : integerBox P,
      (∀ k, (u.val k : ZMod M) = (v.val k : ZMod M)) →
      (∀ k, |(u.val k : ℝ) / P k - (v.val k : ℝ) / P k| ≤
        2 * (Real.exp (-(2 * p)) / 4)) → ‖twist u - twist v‖ ≤ ε)
    {LG MG : Type*} [LieRing LG] [LieAlgebra ℚ LG] [LieRing MG] [LieAlgebra ℚ MG]
    {s d e : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] LG)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] LG)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] LG)] [T2Space (ℝ ⊗[ℚ] LG)]
    [TopologicalSpace (ℝ ⊗[ℚ] MG)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] MG)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] MG)] [T2Space (ℝ ⊗[ℚ] MG)]
    {D : RationalFilteredNilmanifold LG s d} {E : RationalFilteredNilmanifold MG s e}
    (V : D.Niltest (fun _ : K => 1)) (Wlocal : E.Niltest (fun _ : K => 1))
    {pLocal : ℝ} (hV : V.ComplexityLE pLocal) (hW : Wlocal.normBound ≤ 1)
    {δ : ℝ} (hδ : 0 < δ)
    (hbias : δ ≤ ‖(S.fullSliceLaw hlen).complexMean (fun t =>
      star (twist t) *
        (V.eval t.val * Wlocal.eval t.val))‖) :
    ∃ T : ResidueBoxSlice P (q * M),
      0 < q * M ∧
      (∀ k, 0 < T.length k) ∧
      (∀ k, Real.exp (-(cost + (3 * p + 16))) * (P k : ℝ) ≤ T.length k) ∧
      δ / 2 - Real.exp pLocal *
          ε ≤
        ‖𝔼 x ∈ translatedIntegerBox (0 : K → ℤ) T.length,
          V.eval (fun k => ((q * M : ℕ) : ℤ) * x k + T.start k) *
          Wlocal.eval (fun k => ((q * M : ℕ) : ℤ) * x k + T.start k)‖ := by
  let signal : integerBox P → ℂ := fun t =>
    (Real.exp (-pLocal) : ℂ) * (V.eval t.val * Wlocal.eval t.val)
  have hsignal : ∀ t, ‖signal t‖ ≤ 1 := by
    intro t
    have hpartner : ‖Wlocal.eval t.val‖ ≤ 1 :=
      (Wlocal.norm_eval_le _).trans (by exact_mod_cast hW)
    have hprod : ‖V.eval t.val * Wlocal.eval t.val‖ ≤ Real.exp pLocal := by
      rw [norm_mul]
      exact (mul_le_mul (V.eval_budget hV _) hpartner (norm_nonneg _)
        (Real.exp_nonneg _)).trans_eq (mul_one _)
    dsimp only [signal]
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_nonneg _)]
    calc
      _ ≤ Real.exp (-pLocal) * Real.exp pLocal :=
        mul_le_mul_of_nonneg_left hprod (Real.exp_nonneg _)
      _ = 1 := by rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have hscaled : Real.exp (-pLocal) * δ ≤ ‖(S.fullSliceLaw hlen).complexMean
      (fun t => star (twist t) * signal t)‖ := by
    have heq : (S.fullSliceLaw hlen).complexMean
        (fun t => star (twist t) * signal t) =
        (Real.exp (-pLocal) : ℂ) * (S.fullSliceLaw hlen).complexMean (fun t =>
          star (twist t) *
            (V.eval t.val * Wlocal.eval t.val)) := by
      rw [← FiniteProbabilityWeights.complexMean_mul_left]
      congr 1
      funext t
      dsimp only [signal]
      ring
    rw [heq, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_nonneg _)]
    exact mul_le_mul_of_nonneg_left hbias (Real.exp_nonneg _)
  obtain ⟨T, hTq, hTlen, hTlength, hc⟩ := exists_untwisted_subrectangle_of_fullSliceLaw_of_variation
    S hq hlen hp hS hP hM hMexp twist htwist hvariation signal
    (mul_pos (Real.exp_pos _) hδ) hsignal hscaled
  have hmean : ‖𝔼 t : (∀ k, Fin (T.length k)), signal (T.fullSlicePointInIntegerBox t)‖ =
      Real.exp (-pLocal) *
        ‖𝔼 t : (∀ k, Fin (T.length k)),
          V.eval (T.fullSlicePointInIntegerBox t).val * Wlocal.eval (T.fullSlicePointInIntegerBox t).val‖ := by
    simp only [signal, ← Finset.mul_expect, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (Real.exp_nonneg _)]
  rw [hmean] at hc
  have he : Real.exp pLocal * Real.exp (-pLocal) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have hrestore := mul_le_mul_of_nonneg_left hc (Real.exp_nonneg pLocal)
  have hlhs : Real.exp pLocal * (Real.exp (-pLocal) * δ / 2 -
      ε) =
      δ / 2 - Real.exp pLocal *
        ε := by
    rw [mul_sub, ← mul_div_assoc, ← mul_assoc, he, one_mul]
  have hcancel (x : ℝ) : Real.exp pLocal * (Real.exp (-pLocal) * x) = x := by
    rw [← mul_assoc, he, one_mul]
  rw [hlhs, hcancel] at hrestore
  refine ⟨T, hTq, hTlen, hTlength, ?_⟩
  rwa [T.fin_mean_eq_translated_zero (fun x => V.eval x * Wlocal.eval x)] at hrestore

end VectorPolynomial.NormalizedPolynomialTwist
end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.NormalizedTwistSingleSiteFourierHaar
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical NNReal

noncomputable def ambientIntegerCharacter {J : Type*} [Fintype J] (frequency : J → ℤ)
    (x : J → UnitAddCircle) : ℂ :=
  ∏ j, CircleFourier.character (frequency j • x j)

theorem ambientIntegerCharacter_norm {J : Type*} [Fintype J]
    (frequency : J → ℤ) (x : J → UnitAddCircle) :
    ‖ambientIntegerCharacter frequency x‖ = 1 := by
  simp [ambientIntegerCharacter, norm_prod, CircleFourier.norm_character]

theorem ambientIntegerCharacter_lipschitz {J : Type*} [Fintype J]
    (frequency : J → ℤ) (C : ℝ≥0) (hC : ∀ j, |(frequency j : ℝ)| ≤ C) :
    LipschitzWith (Fintype.card J * (CircleFourier.characterLipConstant * C))
      (ambientIntegerCharacter frequency) := by
  have hcoord (j : J) : LipschitzWith C (fun x : J → UnitAddCircle => frequency j • x j) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [dist_eq_norm, ← smul_sub]
    apply (norm_zsmul_le (frequency j) (x j - y j)).trans
    apply mul_le_mul
    · simpa only [Int.norm_eq_abs] using hC j
    · simpa only [dist_eq_norm] using dist_le_pi_dist x y j
    · exact norm_nonneg _
    · exact C.coe_nonneg
  have h := (bounded_lipschitz_fintype_prod
    (fun j (x : J → UnitAddCircle) => CircleFourier.character (frequency j • x j))
    (B := 1) le_rfl (fun j => CircleFourier.character_lipschitz.comp (hcoord j))
    (fun j x => (CircleFourier.norm_character _).le)).2
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [one_pow, mul_one, ambientIntegerCharacter] using h.dist_le_mul x y

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators NNReal

end Erdos3

end

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical NNReal

variable {K F : Type*} [Fintype K] [Fintype F] {m : ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (frequency : F → ∀ j, (K →₀ ℕ) → J j → ℤ) (coeff : F → ℂ)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

variable {m : ℕ} {α : Type*} [Fintype α] [DecidableEq α]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]


end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

variable {m : ℕ} {α : Type*} [Fintype α] [DecidableEq α]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]


end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical NNReal

noncomputable def singleSiteEuclideanRow {D : Type*} [Fintype D]
    (U : Submodule ℝ (D → ℝ)) (a : D → ℤ) : euclideanSubspace U →ₗ[ℝ] ℝ :=
  (integerRowLinear a).comp (U.subtype.comp
    ((LinearMap.proj ()).comp (euclideanSubspaceArrayEquiv U).toLinearMap))

theorem singleSiteEuclideanRow_apply {D : Type*} [Fintype D]
    (U : Submodule ℝ (D → ℝ)) (a : D → ℤ) (x : euclideanSubspace U) :
    singleSiteEuclideanRow U a x = ∑ i, (a i : ℝ) * x.val i := by
  change integerRowLinear a (fun i => x.val i) = _
  exact integerRowLinear_apply a _

theorem singleSiteEuclideanRow_integral {D : Type*} [Fintype D]
    (U : Submodule ℝ (D → ℝ)) (a : D → ℤ) (x : euclideanSubspace U)
    (hx : x ∈ (latticeSection (standardEuclideanLattice D)
      (euclideanSubspace U)).toAddSubgroup) :
    ∃ n : ℤ, singleSiteEuclideanRow U a x = n := by
  have h := (euclideanSubspaceArrayEquiv_mem_lattice U x).mpr hx
  choose z hz using fun i => h () i
  refine ⟨∑ i, a i * z i, ?_⟩
  rw [singleSiteEuclideanRow_apply]
  simp only [euclideanSubspaceArrayEquiv_apply] at hz
  simp only [hz, Int.cast_sum, Int.cast_mul]

theorem singleSiteEuclideanRow_eq_zero {D : Type*} [Fintype D]
    (U : Submodule ℝ (D → ℝ)) (a : D → ℤ) :
    singleSiteEuclideanRow U a = 0 ↔ U ≤ LinearMap.ker (integerRowLinear a) := by
  constructor
  · intro h x hx
    have he := LinearMap.congr_fun h
      ((euclideanSubspaceArrayEquiv U).symm (fun _ => ⟨x, hx⟩))
    change integerRowLinear a
      ((euclideanSubspaceArrayEquiv U
        ((euclideanSubspaceArrayEquiv U).symm (fun _ => ⟨x, hx⟩))) ()).val = 0 at he
    rw [ContinuousLinearEquiv.apply_symm_apply] at he
    exact he
  · intro h
    ext x
    exact h ((euclideanSubspaceArrayEquiv U x ()).property)

theorem singleSiteEuclideanRow_character {D : Type*} [Fintype D]
    (U : Submodule ℝ (D → ℝ)) (a : D → ℤ)
    (y : euclideanSubspace U ⧸
      (latticeSection (standardEuclideanLattice D) (euclideanSubspace U)).toAddSubgroup) :
    (∏ i, CircleFourier.character
      (a i • subspaceAmbientTorus U (euclideanSubspaceTorusEquiv U y) i)) =
      quotientLinearCharacter _ (singleSiteEuclideanRow U a)
        (singleSiteEuclideanRow_integral U a) y := by
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk'_surjective _ y
  rw [euclideanSubspaceTorusEquiv_mk, quotientLinearCharacter_mk,
    singleSiteEuclideanRow_apply, character_real_sum]
  apply Finset.prod_congr rfl
  intro i _
  rw [subspaceAmbientTorus_mk, euclideanSubspaceArrayEquiv_apply,
    ← AddCircle.coe_zsmul, zsmul_eq_mul]

theorem singleSiteHaar_ambientIntegerCharacter_integral
    {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j))
        (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    (a : (Σ j, J j) → ℤ) :
    (∫ y, ambientIntegerCharacter a
      (fun i => coveredJetAmbientTorus U 1 y ⟨i.1, (), i.2⟩)
      ∂Measure.pi (fun j => Measure.pi (fun _ : Unit => ν j))) =
      if ∀ j, U j ≤ LinearMap.ker (integerRowLinear (fun i => a ⟨j, i⟩))
      then 1 else 0 := by
  have he (y : EuclideanJetLayers U (fun _ => Unit)) :
      ambientIntegerCharacter a
        (fun i => coveredJetAmbientTorus U 1 y ⟨i.1, (), i.2⟩) =
      ∏ j, ∏ u : Unit, quotientLinearCharacter _
        (singleSiteEuclideanRow (U j) (fun i => a ⟨j, i⟩))
        (singleSiteEuclideanRow_integral (U j) (fun i => a ⟨j, i⟩)) (y j u) := by
    simp only [ambientIntegerCharacter, Fintype.prod_sigma, Fintype.prod_unique,
      coveredJetAmbientTorus, quotientIntegerCover, nsmulAddMonoidHom_apply, one_nsmul]
    apply Finset.prod_congr rfl
    intro j _
    exact singleSiteEuclideanRow_character (U j) (fun i => a ⟨j, i⟩) (y j ())
  simp_rw [he]
  rw [integral_fintype_prod_eq_prod (fun j (v : Unit → _) =>
    ∏ u : Unit, quotientLinearCharacter _
      (singleSiteEuclideanRow (U j) (fun i => a ⟨j, i⟩))
      (singleSiteEuclideanRow_integral (U j) (fun i => a ⟨j, i⟩)) (v u))]
  simp_rw [integral_fintype_prod_eq_prod]
  simp_rw [quotientLinearCharacter_integral, singleSiteEuclideanRow_eq_zero]
  simp only [Fintype.prod_unique]
  split_ifs with h
  · simp only [h, ite_true, Finset.prod_const_one]
  · obtain ⟨j, hj⟩ := not_forall.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ j) (if_neg hj)

theorem singleSiteHaar_ambientIntegerCharacter_integrable
    {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j))
        (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, IsProbabilityMeasure (ν j)]
    (a : (Σ j, J j) → ℤ) :
    Integrable (fun y => ambientIntegerCharacter a
      (fun i => coveredJetAmbientTorus U 1 y ⟨i.1, (), i.2⟩))
      (Measure.pi (fun j => Measure.pi (fun _ : Unit => ν j))) := by
  have : ∀ j, IsProbabilityMeasure (Measure.pi (fun _ : Unit => ν j)) :=
    fun _ => Measure.pi.instIsProbabilityMeasure _
  have : IsProbabilityMeasure
      (Measure.pi (fun j => Measure.pi (fun _ : Unit => ν j))) :=
    Measure.pi.instIsProbabilityMeasure _
  apply Integrable.of_bound _ 1
    (ae_of_all _ (fun _ => (ambientIntegerCharacter_norm a _).le))
  apply Continuous.aestronglyMeasurable
  let C : ℝ≥0 := ⟨∑ i, |(a i : ℝ)|, Finset.sum_nonneg (fun i _ => abs_nonneg _)⟩
  have hc : Continuous (ambientIntegerCharacter a) :=
    (ambientIntegerCharacter_lipschitz a C (fun i =>
      Finset.single_le_sum (fun j _ => abs_nonneg (a j : ℝ)) (Finset.mem_univ i))).continuous
  apply hc.comp
  apply continuous_pi
  intro i
  exact (continuous_apply (⟨i.1, (), i.2⟩ : JetAmbientIndex (fun _ : Fin m => Unit) J)).comp
    (coveredJetAmbientTorus_continuous (O := fun _ : Fin m => Unit) U 1)

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedPhysicalIntegerRankLaw
namespace OAI

section

namespace Erdos3
open scoped Classical

theorem selectedResidueDensityPMF_event_congr_of_density_ne_zero
    {K I : Type*} [Fintype K] [Fintype I]
    (modulus : I → ℕ) (G : Finset (ColumnResiduePattern K I modulus))
    (V : K × I → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' x, selectedResidueSmoothWeight modulus G V x)
    (D : (K × I → ℤ) → ℝ) (hD0 : ∀ x, 0 ≤ D x)
    (hD : 0 < selectedResidueDensityMass modulus G V D)
    (f g : (K × I → ℤ) → Prop) [DecidablePred f] [DecidablePred g]
    (hfg : ∀ x, D x ≠ 0 → (f x ↔ g x)) :
    (∑' x, (selectedResidueDensityPMF modulus G V hV hZ D hD0 hD x).toReal *
      (if f x then (1 : ℝ) else 0)) =
    ∑' x, (selectedResidueDensityPMF modulus G V hV hZ D hD0 hD x).toReal *
      (if g x then (1 : ℝ) else 0) := by
  apply tsum_congr
  intro x
  by_cases hx : D x = 0
  · rw [selectedResidueDensityPMF_zero_of_density_zero modulus G V hV hZ D hD0 hD x hx]
    simp only [zero_mul]
  · simp only [hfg x hx]

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

theorem largestTestedBadDepth_congr_on_tested {Ω : Type*}
    (A : ℕ → ℕ) (bad other : ℕ → ℕ → Ω → Prop) (p : ℕ) (x : Ω)
    (h : ∀ a, 0 < a → a ≤ A p → (bad p a x ↔ other p a x)) :
    largestTestedBadDepth A bad p x = largestTestedBadDepth A other p x := by
  unfold largestTestedBadDepth
  congr 1
  apply Finset.filter_congr
  intro a ha
  exact h a (Finset.mem_Icc.mp ha).1 (Finset.mem_Icc.mp ha).2

theorem largestBadPrimeProduct_congr_on_tested {Ω : Type*}
    (S : Finset ℕ) (A : ℕ → ℕ) (bad other : ℕ → ℕ → Ω → Prop) (x : Ω)
    (h : ∀ p ∈ S, ∀ a, 0 < a → a ≤ A p → (bad p a x ↔ other p a x)) :
    (∏ p ∈ S, p ^ largestTestedBadDepth A bad p x) =
      ∏ p ∈ S, p ^ largestTestedBadDepth A other p x := by
  apply Finset.prod_congr rfl
  intro p hp
  rw [largestTestedBadDepth_congr_on_tested A bad other p x (h p hp)]

theorem selectedResidueDensityPMF_badProduct_event_congr
    {K I : Type*} [Fintype K] [Fintype I]
    (modulus : I → ℕ) (G : Finset (ColumnResiduePattern K I modulus))
    (V : K × I → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' x, selectedResidueSmoothWeight modulus G V x)
    (D : (K × I → ℤ) → ℝ) (hD0 : ∀ x, 0 ≤ D x)
    (hD : 0 < selectedResidueDensityMass modulus G V D)
    (S : Finset ℕ) (A : ℕ → ℕ)
    (bad other : ℕ → ℕ → (K × I → ℤ) → Prop) (R : ℕ)
    (heq : ∀ x, D x ≠ 0 → ∀ p ∈ S, ∀ a, 0 < a → a ≤ A p →
      (bad p a x ↔ other p a x)) :
    (∑' x, (selectedResidueDensityPMF modulus G V hV hZ D hD0 hD x).toReal *
      (if R < ∏ p ∈ S, p ^ largestTestedBadDepth A bad p x then (1 : ℝ) else 0)) =
      ∑' x, (selectedResidueDensityPMF modulus G V hV hZ D hD0 hD x).toReal *
        (if R < ∏ p ∈ S, p ^ largestTestedBadDepth A other p x then (1 : ℝ) else 0) := by
  apply selectedResidueDensityPMF_event_congr_of_density_ne_zero
  intro x hx
  rw [largestBadPrimeProduct_congr_on_tested S A bad other x (heq x hx)]

end Erdos3

end

section

namespace Erdos3
open MeasureTheory
open scoped BigOperators Classical

theorem finite_nat_sup_measurable {Ω ι : Type*} [MeasurableSpace Ω]
    (s : Finset ι) (f : ι → Ω → ℕ) (hf : ∀ i ∈ s, Measurable (f i)) :
    Measurable (fun x => s.sup (fun i => f i x)) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    simp only [Finset.sup_insert]
    exact (hf i (Finset.mem_insert_self _ _)).sup
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

theorem largestTestedBadDepth_measurable {Ω : Type*} [MeasurableSpace Ω]
    (A : ℕ → ℕ) (bad : ℕ → ℕ → Ω → Prop) (p : ℕ)
    (hbad : ∀ a ∈ Finset.Icc 1 (A p), MeasurableSet {x | bad p a x}) :
    Measurable (largestTestedBadDepth A bad p) := by
  unfold largestTestedBadDepth
  have h := finite_nat_sup_measurable (Finset.Icc 1 (A p))
    (fun a x => if bad p a x then a else 0)
    (fun a ha => Measurable.ite (hbad a ha) measurable_const measurable_const)
  convert h using 1
  funext x
  rw [Finset.sup_ite]
  simp only [show (0 : ℕ) = ⊥ from rfl, Finset.sup_bot, sup_bot_eq]
  rfl

theorem largestBadPrimeProduct_measurable {Ω : Type*} [MeasurableSpace Ω]
    (P : Finset ℕ) (A : ℕ → ℕ) (bad : ℕ → ℕ → Ω → Prop)
    (hbad : ∀ p ∈ P, ∀ a ∈ Finset.Icc 1 (A p), MeasurableSet {x | bad p a x}) :
    Measurable (fun x => ∏ p ∈ P, p ^ largestTestedBadDepth A bad p x) := by
  apply Finset.measurable_prod
  intro p hp
  exact (measurable_of_countable (fun a : ℕ => p ^ a)).comp
    (largestTestedBadDepth_measurable A bad p (hbad p hp))

theorem largestBadPrimeProduct_tail_measurableSet {Ω : Type*} [MeasurableSpace Ω]
    (P : Finset ℕ) (A : ℕ → ℕ) (bad : ℕ → ℕ → Ω → Prop)
    (hbad : ∀ p ∈ P, ∀ a ∈ Finset.Icc 1 (A p), MeasurableSet {x | bad p a x})
    (cutoff : ℕ) :
    MeasurableSet {x | cutoff < ∏ p ∈ P, p ^ largestTestedBadDepth A bad p x} :=
  measurableSet_lt measurable_const (largestBadPrimeProduct_measurable P A bad hbad)

end Erdos3

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule
open scoped Classical

variable {K : Type*} {m : ℕ} {J I E : Fin m → Type*}
variable [∀ j, Fintype (J j)] [∀ j, Fintype (I j)] [∀ j, Fintype (E j)] {n : Fin m → ℕ}
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (bW : ∀ j, Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))

theorem exists_coefficientDeck_integer_lift (c : CoefficientArray (K := K) U)
    (x : CoefficientSamplerArrays (K := K) I n)
    (hx : canonicalCoefficientSample U b hb o x =
      QuotientAddGroup.mk' (coefficientIntegerLattice U) c) :
    ∃ w : ∀ j : Fin m, BoundedCoefficientExponent K (j.val + 1) → E j → ℤ,
      ∀ (q : ℕ) (hq : 0 < q),
      canonicalCoefficientDeckSample U bW b hb o q hq x
          (fun j e => integerResidueMap (E j) q (w j e)) =
        QuotientAddGroup.mk' (coefficientIntegerLattice U) ((q : ℝ)⁻¹ • c) := by
  have hp (j : Fin m) (e : BoundedCoefficientExponent K (j.val + 1)) :
      QuotientAddGroup.mk' _ ((euclideanSubspaceArrayEquiv (U j)).symm (fun _ => c ⟨j, e⟩)) =
        normalizedLatticeQuotient (euclideanSubspace (U j)) (b j) (hb j)
          (orthonormalMixedChart (o j) (mixedArrayRegroup _ _ _ (x j) e)) := by
    have h := congrArg (fun y => euclideanCoefficientEquiv U y j e) hx
    simpa only [canonicalCoefficientSample, AddEquiv.apply_symm_apply,
      euclideanCoefficientEquiv_mk, mixedArrayQuotient] using h.symm
  choose w hw using fun (j : Fin m) (e : BoundedCoefficientExponent K (j.val + 1)) =>
    exists_normalized_representative_offset (euclideanSubspace (U j)) (bW j) (b j) (hb j)
      ((euclideanSubspaceArrayEquiv (U j)).symm (fun _ => c ⟨j, e⟩))
      (orthonormalMixedChart (o j) (mixedArrayRegroup _ _ _ (x j) e)) (hp j e)
  refine ⟨w, ?_⟩
  intro q hq
  apply (euclideanCoefficientEquiv U).injective
  funext j e
  rw [canonicalCoefficientDeckSample_coordinate, normalizedCoverLift_add_deck, hw,
    euclideanCoefficientEquiv_mk]
  congr 1

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule

variable {K : Type*} {m : ℕ} {J I E : Fin m → Type*}
variable [∀ j, Fintype (J j)] [∀ j, Fintype (I j)] [∀ j, Fintype (E j)] {n : Fin m → ℕ}
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (bW : ∀ j, Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))

theorem exists_coefficientDeck_integer_event_read
    (c : CoefficientArray (K := K) U) (x : CoefficientSamplerArrays (K := K) I n)
    (hx : canonicalCoefficientSample U b hb o x = QuotientAddGroup.mk' (coefficientIntegerLattice U) c)
    (hsmall : ∀ a, |coefficientSamplerAmbientPoint U b o x a| < 1/2) :
    ∃ w : ∀ j, BoundedCoefficientExponent K (j.val + 1) → E j → ℤ,
      ∀ (q : ℕ) (hq : 0 < q), letI : NeZero q := ⟨hq.ne'⟩
        ∀ event : CoefficientChartResidues K n E q → Prop,
          coefficientDeckChartEvent U bW b hb o q event
            (QuotientAddGroup.mk' (coefficientIntegerLattice U) ((q : ℝ)⁻¹ • c)) ↔
          event (coefficientSamplerChartResidues q x
            (fun j e => integerResidueMap (E j) q (w j e))) := by
  obtain ⟨w, hw⟩ := exists_coefficientDeck_integer_lift U bW b hb o c x hx
  refine ⟨w, ?_⟩
  intro q hq
  let : NeZero q := ⟨hq.ne'⟩
  intro event
  rw [← hw q (NeZero.pos q)]
  exact coefficientDeckChartEvent_sample_iff U bW b hb o q event x hsmall _

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule
open scoped Classical

variable {m : ℕ} {G X : Type*} {J I E : Fin m → Type*} {n : Fin m → ℕ}
variable {B : LayerSamplerAxis I n → Type*}
variable [∀ j, Fintype (J j)] [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (bW : ∀ j, Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))

theorem exists_allocatedCoefficient_integer_event_read
    (c : CoefficientArray (K := LayerSamplerVariables G I n B) U)
    (x : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (hx : canonicalCoefficientSample U b hb o x = QuotientAddGroup.mk' (coefficientIntegerLattice U) c)
    (hsmall : ∀ a, |coefficientSamplerAmbientPoint U b o x a| < 1/2)
    (noise : Option (LayerSamplerVariables G I n B) × X → ℤ) :
    ∃ f : AllocatedActualCoefficientIndex G X I E n B → ℤ,
      allocatedReadNoise f = noise ∧
      (∀ (j : Fin m) (i : Fin (n j))
        (e : BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)),
        allocatedReadProjection f ⟨j, Sum.inr i⟩ e = (x j).2 i e) ∧
      ∀ (q : ℕ) (hq : 0 < q), letI : NeZero q := ⟨hq.ne'⟩
        ∀ event : CoefficientChartResidues (LayerSamplerVariables G I n B) n E q → Prop,
          coefficientDeckChartEvent U bW b hb o q event
            (QuotientAddGroup.mk' (coefficientIntegerLattice U) ((q : ℝ)⁻¹ • c)) ↔
          event (allocatedReadCoefficientChartResidues (fun i => (f i : ZMod q))) := by
  obtain ⟨w, hw⟩ := exists_coefficientDeck_integer_event_read U bW b hb o c x hx hsmall
  let f : AllocatedActualCoefficientIndex G X I E n B → ℤ :=
    allocatedMixedFullArray (Sum.elim noise (fun ⟨j,e,i⟩ => (x j).2 i e))
      (fun ⟨j,e,i⟩ => w j e i) (fun _ => 0)
  have hi (j : Fin m) (i : Fin (n j))
      (e : BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) :
      allocatedReadProjection f ⟨j, Sum.inr i⟩ e = (x j).2 i e := rfl
  refine ⟨f, rfl, hi, ?_⟩
  intro q hq
  let : NeZero q := ⟨hq.ne'⟩
  intro event
  rw [allocatedReadCoefficientChartResidues_sampler q f x hi]
  exact hw q hq event

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule
open scoped Classical

variable {m : ℕ} {G X : Type*} [Fintype G] {I E J : Fin m → Type*}
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

variable [Fintype X]

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


end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ForecastNativeResidueTest
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module
open scoped Classical Matrix

variable {m : ℕ} {X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
variable (inactive : LayerSamplerAxis I n → Prop)

def forecastNativeSpatialResidue (hm : 0 < m) {R : Type*}
    (out : Sigma (AllocatedCongruenceRankOutput X E inactive) → R) : X → R :=
  fun x => out ⟨⟨0, hm⟩, .inl ⟨x, rfl⟩⟩

noncomputable def forecastNativeSheetResidue (q : ℕ)
    (frozen : ∀ j, {i : Fin (n j) // inactive ⟨j, .inr i⟩} → ℤ)
    (out : Sigma (AllocatedCongruenceRankOutput X E inactive) → ZMod q)
    (j : Fin m) (i : Fin (n j)) : ZMod q :=
  if hi : inactive ⟨j, .inr i⟩ then (frozen j ⟨i, hi⟩ : ZMod q)
  else out ⟨j, .inr (.inr ⟨i, hi⟩)⟩

def forecastNativeFreeDeckResidue {R : Type*}
    (out : Sigma (AllocatedCongruenceRankOutput X E inactive) → R)
    (j : Fin m) (e : E j) : R := out ⟨j, .inr (.inl e)⟩

noncomputable def forecastNativeCoordinateResidue (q : ℕ)
    (frozen : ∀ j, {i : Fin (n j) // inactive ⟨j, .inr i⟩} → ℤ)
    (out : Sigma (AllocatedCongruenceRankOutput X E inactive) → ZMod q)
    (j : Fin m) : Fin (n j) ⊕ E j → ZMod q :=
  Sum.elim (forecastNativeSheetResidue inactive q frozen out j)
    (forecastNativeFreeDeckResidue inactive out j)

variable {J : Fin m → Type*} [∀ j, Fintype (J j)] [∀ j, Fintype (E j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, Submodule.span ℤ (Set.range (b j)) =
  projectedIntegerLattice (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

noncomputable def forecastNativeDeckResidueMatrix (q : ℕ) [NeZero q] (j : Fin m) :
    Matrix (J j) (Fin (n j) ⊕ E j) ℤ :=
  Classical.choose (exists_bounded_integerMap_residue_matrix
    (standardLatticeCoordinates (euclideanSubspace (U j)) (bW j) (b j) (hb j)).symm.toLinearMap q)

noncomputable def forecastNativeAmbientDeckResidue (q : ℕ) [NeZero q]
    (frozen : ∀ j, {i : Fin (n j) // inactive ⟨j, .inr i⟩} → ℤ)
    (out : Sigma (AllocatedCongruenceRankOutput X E inactive) → ZMod q) :
    (Σ j, J j) → ZMod q := fun a =>
  (integerResidueMatrix (forecastNativeDeckResidueMatrix U b hb bW q a.1) q *ᵥ
    forecastNativeCoordinateResidue inactive q frozen out a.1) a.2

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module
open scoped Classical NNReal
variable {m : ℕ} {X : Type*} [Fintype X]
variable {I E : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
variable {n : Fin m → ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, Submodule.span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (R : Fin m → ℝ) (P : LayerSamplerAxis I n → Prop) [DecidablePred P]
local notation "Out" => Sigma (AllocatedCongruenceRankOutput X E P)
local notation "Output" => (Σ _a : {a : LayerSamplerAxis I n // ¬P a}, Unit)
local notation "Domain" => (((Σ _ : X, Unit ⊕ Empty) → ℝ) × (Output → ℝ))

namespace NormalizedPolynomialTwist
variable {periodCap coverCap : ℝ} {L : ℝ≥0}
variable (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L)

noncomputable def forecastResidueTest (q : ℕ) [NeZero q] (hm : 0 < m)
    (hperiod : W.modulus ∣ q) (hcover : W.cover ∣ q)
    (sheet : ∀ j, {i : Fin (n j) // P ⟨j, .inr i⟩} → ℤ)
    (frozen : {a : LayerSamplerAxis I n // P a} → ℝ)
    (center : X → ℝ) (τ : ℝ) (out : Out → ZMod q) : Domain → ℂ :=
  W.forecastPullback U b o R P
    (zmodPiReduction hperiod (forecastNativeSpatialResidue P hm out))
    (zmodPiReduction hcover (forecastNativeAmbientDeckResidue P U b hb bW q sheet out))
    center τ frozen

end NormalizedPolynomialTwist
end Erdos3.VectorPolynomial

end

end OAI

end


