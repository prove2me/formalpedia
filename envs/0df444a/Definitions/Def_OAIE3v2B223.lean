-- Prove2me | Definitions.Def_OAIE3v2B223
-- name    : OAIE3v2B223
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-18T04:35:17.433017+00:00
-- url     : https://prove2.me/theorems/0244e0c4-f179-45e4-aa4e-814c6e74a09e
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 228 of 311
-- statement:
--   Definitions bundle 228 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B199`, `OAIE3v2B201`, `OAIE3v2B202`, `OAIE3v2B203` of this split.
--
--   Modules: `Estimates/CommonFreeSunflower.lean`, `Estimates/CubicAntisymmetricTransfer.lean`, `Estimates/NativeAbsorbedIntervals.lean`, `Estimates/NativeDilationDescent.lean`, `Estimates/NativeDilationObservable.lean`, `Estimates/NativeGlobalErrorSplitting.lean`, `Estimates/NativeMultidegreeDilation.lean`, `Estimates/NativeMultilinearQuadruples.lean`, `Estimates/TwoDownsetPrecision.lean`, `Geometry/CommonNativeCoordinateCorrections.lean`, `Linear/CommonRankCoefficientCorrections.lean`, `Linear/CommonRealDependentProjection.lean`, `Linear/NativeCoefficientKernel.lean`, `Nilpotent/PreparedDilationNiltest.lean`, `Nilpotent/TotalDegreeNiltestSplitting.lean`, `Polynomial/BoundedRootDegreeEquivalence.lean`, `Polynomial/CanonicalPositivePolynomialSplitting.lean`, `Polynomial/NativeFreePolynomialLifts.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B199
import Definitions.Def_OAIE3v2B201
import Definitions.Def_OAIE3v2B202
import Definitions.Def_OAIE3v2B203

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeDilationObservable
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open CircleFourier
open scoped TensorProduct BigOperators

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s d r : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  (M : D.MultidegreeStructure bound) (q : ℚ)
  (E : RationalFilteredNilmanifold (M.filtration.ordinary.dilationPairSubalgebra q) s r)
  (hEL : E.lattice = M.dilationPairLattice q)

theorem dilationObservable_component_top (ε : D.RealGroup) (u : D.Space → ℂ)
    (χ : D.RealGroup → CircleFourier.Circle)
    (hu : ∀ z, z ∈ M.filtration.realification.ordinary.subgroup s →
      ∀ x, u (z • x) = character (χ z) * u x)
    (j : Fin 2) (k : E.RealGroup)
    (hk : k ∈ (M.filtration.ordinary.dilationPairFiltration q).realification.subgroup s)
    (x : E.Space) :
    u (ε • M.dilationSpaceProjection q E hEL j (k • x)) =
      character (χ (M.filtration.ordinary.realDilationPairProjection q j k)) *
        u (ε • M.dilationSpaceProjection q E hEL j x) := by
  rw [M.dilationSpaceProjection_top_smul q E hEL ε j k hk x]
  exact hu _ (M.filtration.ordinary.realDilationPairProjection_mem q j hk) _

theorem dilationObservable_top_invariant (m : ℤ) (ε : D.RealGroup)
    (u₀ : D.Space → ℂ) (u : Fin m.natAbs → D.Space → ℂ)
    (χ : D.RealGroup → CircleFourier.Circle)
    (h₀ : ∀ z, z ∈ M.filtration.realification.ordinary.subgroup s →
      ∀ x, u₀ (z • x) = character (χ z) * u₀ x)
    (hu : ∀ a z, z ∈ M.filtration.realification.ordinary.subgroup s →
      ∀ x, u a (z • x) = character (χ z) * u a x)
    (k : E.RealGroup)
    (hk : k ∈ (M.filtration.ordinary.dilationPairFiltration q).realification.subgroup s)
    (hphase : χ (M.filtration.ordinary.realDilationPairProjection q 0 k) =
      m • χ (M.filtration.ordinary.realDilationPairProjection q 1 k))
    (x : E.Space) :
    M.dilationObservable q E hEL m ε u₀ u (k • x) =
      M.dilationObservable q E hEL m ε u₀ u x := by
  have hvalue₀ := M.dilationObservable_component_top q E hEL ε u₀ χ h₀ 0 k hk x
  have hvalue (a) := M.dilationObservable_component_top q E hEL ε (u a) χ (hu a) 1 k hk x
  unfold dilationObservable
  rw [hvalue₀]
  simp_rw [hvalue]
  exact signed_power_phase_cancellation m _ _ _ _ hphase

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.CanonicalPositivePolynomialSplitting
namespace OAI


namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open NilpotentLieBCHGroup VectorPolynomial
open scoped BigOperators TensorProduct NNReal

theorem exists_positivePolynomial_source_reconstruction (t : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {α σ L : Type*} [Fintype α] [DecidableEq α]
      [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
      {s d : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
      (M : D.MultidegreeStructure bound) (J : α → Set (σ →₀ ℕ))
      [∀ a, DecidablePred (· ∈ J a)] (hJ : ∀ a, IsLowerSet (J a))
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      [TopologicalSpace (ℝ ⊗[ℚ] M.filtration.positivePolynomialAlgebra)]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] M.filtration.positivePolynomialAlgebra)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] M.filtration.positivePolynomialAlgebra)]
      [T2Space (ℝ ⊗[ℚ] M.filtration.positivePolynomialAlgebra)]
      [TopologicalSpace (ℝ ⊗[ℚ] (∀ a, M.filtration.positivePolynomialAlgebra ⧸
        restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra (J a) (hJ a)))]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ a, M.filtration.positivePolynomialAlgebra ⧸
        restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra (J a) (hJ a)))]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] (∀ a, M.filtration.positivePolynomialAlgebra ⧸
        restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra (J a) (hJ a)))]
      [T2Space (ℝ ⊗[ℚ] (∀ a, M.filtration.positivePolynomialAlgebra ⧸
        restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra (J a) (hJ a)))]
      (p q : ℝ) (B : ℕ) (hB : 0 < B) (hstable : M.PositivePolynomialGridStable p B),
      (∑ i, bound i) = t → M.ComplexityLE p → p ≤ q → (Fintype.card α : ℝ) ≤ q →
      (M.positivePolynomialModel p B hB hstable).GeometryComplexityLE q →
      M.positivePolynomialLattice p B hstable ≤
        D.lattice.comap (mapOfSteps M.filtration.positivePolynomialEvaluation) →
      (∀ c, c ≠ 0 → (∀ a, c ∉ J a) → M.filtration.layer (fun i => c i) = ⊥) →
      ∀ (u : D.Space → ℂ) (ℓ : ℝ≥0), (ℓ : ℝ) ≤ Real.exp q →
        (letI := D.metricSpace; LipschitzWith ℓ u) → (∀ x, ‖u x‖ ≤ 1) →
        ∃ (v : (M.positivePolynomialQuotientProductModel J hJ p B hB hstable).Space → ℂ) (K : ℝ≥0),
          (K : ℝ) ≤ Real.exp ((q + C) ^ C) ∧
          (letI := (M.positivePolynomialQuotientProductModel J hJ p B hB hstable).metricSpace;
            LipschitzWith K v) ∧ (∀ y, ‖v y‖ ≤ 2) ∧
          ∀ x, v (QuotientGroup.mk (M.filtration.positivePolynomialQuotientProductRealMap J hJ x)) =
            u (QuotientGroup.mk (realificationMap
              (hnil := M.filtration.positivePolynomialMultidegree.ordinary.lowerCentralSeries_eq_bot)
              (hM := D.filtration.lowerCentralSeries_eq_bot) M.filtration.positivePolynomialEvaluation x)) := by
  obtain ⟨a, _, hrec⟩ := exists_positivePolynomial_product_reconstruction t
  let P : Polynomial ℕ := (Polynomial.X + (Polynomial.X + 3) ^ 2 + Polynomial.C a) ^ a
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro α σ L _ _ _ _ _ _ s d D bound M J _ hJ _ _ _ _ _ _ _ _ _ _ _ _ p q B hB hstable
    ht hM hpq hα hX hmap hcover u ℓ hℓ hu hub
  let r := q + (q + 3) ^ 2
  have hq : 0 ≤ q := (Nat.cast_nonneg _).trans hX.1
  have hqr : q ≤ r := le_add_of_nonneg_right (sq_nonneg _)
  let u₀ := u ∘ M.positivePolynomialEvaluationCosetMap p B hB hstable hmap
  obtain ⟨K₀, hK₀, hu₀⟩ := M.exists_positivePolynomial_observable_pullback hM hpq hX.1
    B hB hstable hmap u ℓ hℓ hu
  have hub₀ : ∀ x, ‖u₀ x‖ ≤ 1 := fun x => hub _
  obtain ⟨v, K, hK, hv, hb, heval⟩ := hrec M J hJ p r B hB hstable ht (hα.trans hqr)
    (hX.mono _ hqr) hcover u₀ K₀ hK₀ hu₀ hub₀
  have hcost : (r + a) ^ a ≤ (q + C) ^ C := by
    simpa [P, r, Polynomial.eval₂_pow] using hbudget q hq
  refine ⟨v, K, hK.trans (Real.exp_le_exp.mpr hcost), hv, hb, ?_⟩
  intro x
  simpa only [u₀, Function.comp_apply, M.positivePolynomialEvaluationCosetMap_mk] using heval x

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure


namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open NilpotentLieBCHGroup VectorPolynomial
open scoped BigOperators TensorProduct NNReal

theorem exists_positivePolynomial_factor_approximation (t a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {α σ L : Type*} [Fintype α] [DecidableEq α]
      [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
      {s d : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
      (M : D.MultidegreeStructure bound) (J : α → Set (σ →₀ ℕ))
      [∀ i, DecidablePred (· ∈ J i)] (hJ : ∀ i, IsLowerSet (J i))
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      [TopologicalSpace (ℝ ⊗[ℚ] M.filtration.positivePolynomialAlgebra)]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] M.filtration.positivePolynomialAlgebra)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] M.filtration.positivePolynomialAlgebra)]
      [T2Space (ℝ ⊗[ℚ] M.filtration.positivePolynomialAlgebra)]
      [∀ i, TopologicalSpace (ℝ ⊗[ℚ] (M.filtration.positivePolynomialAlgebra ⧸
        restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra (J i) (hJ i)))]
      [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] (M.filtration.positivePolynomialAlgebra ⧸
        restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra (J i) (hJ i)))]
      [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] (M.filtration.positivePolynomialAlgebra ⧸
        restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra (J i) (hJ i)))]
      [∀ i, T2Space (ℝ ⊗[ℚ] (M.filtration.positivePolynomialAlgebra ⧸
        restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra (J i) (hJ i)))]
      [TopologicalSpace (ℝ ⊗[ℚ] (∀ i, M.filtration.positivePolynomialAlgebra ⧸
        restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra (J i) (hJ i)))]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ i, M.filtration.positivePolynomialAlgebra ⧸
        restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra (J i) (hJ i)))]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] (∀ i, M.filtration.positivePolynomialAlgebra ⧸
        restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra (J i) (hJ i)))]
      [T2Space (ℝ ⊗[ℚ] (∀ i, M.filtration.positivePolynomialAlgebra ⧸
        restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra (J i) (hJ i)))]
      (p q : ℝ) (B : ℕ) (hB : 0 < B) (hstable : M.PositivePolynomialGridStable p B),
      (∑ i, bound i) = t → M.ComplexityLE p → p ≤ q → (Fintype.card α : ℝ) ≤ q →
      (M.positivePolynomialModel p B hB hstable).GeometryComplexityLE q →
      M.positivePolynomialLattice p B hstable ≤ D.lattice.comap (mapOfSteps M.filtration.positivePolynomialEvaluation) →
      (∀ c, c ≠ 0 → (∀ i, c ∉ J i) → M.filtration.layer (fun j => c j) = ⊥) →
      ∀ epsilon : ℝ, 0 < epsilon → 1 / epsilon ≤ Real.exp ((q + 2) ^ a) →
      let E := fun i => M.positivePolynomialDownsetModel (J i) (hJ i) p B hB hstable
      letI : ∀ i, MetricSpace (E i).Space := fun i => (E i).metricSpace
      ∃ n : α → ℕ, (∀ i, 0 < n i) ∧ (∀ i, (n i : ℝ) ≤ Real.exp ((q + C) ^ C)) ∧
        (Fintype.card (∀ i, Fin (n i)) : ℝ) ≤ Real.exp ((q + C) ^ C) ∧
        ∃ K : α → ℝ≥0, (∀ i, (K i : ℝ) ≤ Real.exp ((q + C) ^ C)) ∧
          ∃ ψ : ∀ i, Fin (n i) → (E i).Space → ℝ,
            (∀ i j x, 0 ≤ ψ i j x ∧ ψ i j x ≤ 1) ∧
            (∀ i x, ∑ j, ψ i j x = 1) ∧ (∀ i j, LipschitzWith (K i) (ψ i j)) ∧
            ∀ (u : D.Space → ℂ) (ell : ℝ≥0), (ell : ℝ) ≤ Real.exp q →
              (letI := D.metricSpace; LipschitzWith ell u) → (∀ x, ‖u x‖ ≤ 1) →
              ∃ c : (∀ i, Fin (n i)) → ℂ, (∀ j, ‖c j‖ ≤ 2) ∧
                ∀ x, ‖u (QuotientGroup.mk (realificationMap
                    (hnil := M.filtration.positivePolynomialMultidegree.ordinary.lowerCentralSeries_eq_bot)
                    (hM := D.filtration.lowerCentralSeries_eq_bot) M.filtration.positivePolynomialEvaluation x)) -
                  ∑ j, (∏ i, (ψ i (j i) (productProjection E i
                    (QuotientGroup.mk (M.filtration.positivePolynomialQuotientProductRealMap J hJ x))) : ℂ)) * c j‖ ≤ epsilon := by
  obtain ⟨b, _, hrec⟩ := exists_positivePolynomial_source_reconstruction t
  obtain ⟨c, _, happ⟩ := exists_controlled_native_product_approximation t a b
  let P : Polynomial ℕ := (Polynomial.X + Polynomial.C b + Polynomial.C c) ^ c
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro α σ L _ _ _ _ _ _ s d D bound M J _ hJ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    p q B hB hstable ht hM hpq hα hX hmap hcover epsilon hepsilon hscale
  subst t
  let E := fun i => M.positivePolynomialDownsetModel (J i) (hJ i) p B hB hstable
  let : ∀ i, MetricSpace (E i).Space := fun i => (E i).metricSpace
  let := (pi E).metricSpace
  have hq : 0 ≤ q := (Nat.cast_nonneg _).trans hX.1
  let R := q + b
  have hqR : q ≤ R := le_add_of_nonneg_right (Nat.cast_nonneg b)
  have hR : 0 ≤ R := hq.trans hqR
  have hscaleR : 1 / epsilon ≤ Real.exp ((R + 2) ^ a) :=
    hscale.trans (Real.exp_le_exp.mpr (pow_le_pow_left₀ (by linarith) (by linarith) a))
  obtain ⟨n, hn, hnb, hcount, K, hKb, ψ, hunit, hsum, hLip, happrox⟩ := happ E hR (hα.trans hqR)
    (fun i => ((M.positivePolynomialDownsetModel_complexity (J i) (hJ i) p q B hB hstable hX).1).mono (E i) hqR)
    hepsilon hscaleR
  have hcost : (R + c) ^ c ≤ (q + C) ^ C := by
    simpa [P, R, Polynomial.eval₂_pow] using hbudget q hq
  have hexp := Real.exp_le_exp.mpr hcost
  refine ⟨n, hn, fun i => (hnb i).trans hexp, hcount.trans hexp,
    K, fun i => (hKb i).trans hexp, ψ, hunit, hsum, hLip, ?_⟩
  intro u ell hell hu hub
  obtain ⟨v, Kv, hKv, hv, hvb, heval⟩ := hrec M J hJ p q B hB hstable rfl hM hpq hα hX hmap hcover u ell hell hu hub
  have hKvR : (Kv : ℝ) ≤ Real.exp ((R + 2) ^ b) :=
    hKv.trans (Real.exp_le_exp.mpr (pow_le_pow_left₀ hR (by linarith) b))
  obtain ⟨coeff, hcoeff, herr⟩ := happrox v Kv hKvR hv hvb
  refine ⟨coeff, hcoeff, fun x => ?_⟩
  have h := herr (QuotientGroup.mk (M.filtration.positivePolynomialQuotientProductRealMap J hJ x))
  convert h using 1
  congr 2
  exact (heval x).symm

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure


namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open NilpotentLieBCHGroup VectorPolynomial
open scoped BigOperators TensorProduct NNReal

theorem exists_positivePolynomial_vector_factor_approximation (t a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {I α σ L : Type*} [Fintype I] [Fintype α] [DecidableEq α]
      [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
      {s d : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
      (M : D.MultidegreeStructure bound) (J : α → Set (σ →₀ ℕ))
      [∀ i, DecidablePred (· ∈ J i)] (hJ : ∀ i, IsLowerSet (J i))
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      [TopologicalSpace (ℝ ⊗[ℚ] M.filtration.positivePolynomialAlgebra)]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] M.filtration.positivePolynomialAlgebra)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] M.filtration.positivePolynomialAlgebra)]
      [T2Space (ℝ ⊗[ℚ] M.filtration.positivePolynomialAlgebra)]
      [∀ i, TopologicalSpace (ℝ ⊗[ℚ] (M.filtration.positivePolynomialAlgebra ⧸
        restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra (J i) (hJ i)))]
      [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] (M.filtration.positivePolynomialAlgebra ⧸
        restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra (J i) (hJ i)))]
      [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] (M.filtration.positivePolynomialAlgebra ⧸
        restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra (J i) (hJ i)))]
      [∀ i, T2Space (ℝ ⊗[ℚ] (M.filtration.positivePolynomialAlgebra ⧸
        restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra (J i) (hJ i)))]
      [TopologicalSpace (ℝ ⊗[ℚ] (∀ i, M.filtration.positivePolynomialAlgebra ⧸
        restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra (J i) (hJ i)))]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ i, M.filtration.positivePolynomialAlgebra ⧸
        restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra (J i) (hJ i)))]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] (∀ i, M.filtration.positivePolynomialAlgebra ⧸
        restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra (J i) (hJ i)))]
      [T2Space (ℝ ⊗[ℚ] (∀ i, M.filtration.positivePolynomialAlgebra ⧸
        restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra (J i) (hJ i)))]
      (p q : ℝ) (B : ℕ) (hB : 0 < B) (hstable : M.PositivePolynomialGridStable p B),
      (∑ i, bound i) = t → M.ComplexityLE p → p ≤ q → (Fintype.card α : ℝ) ≤ q →
      (M.positivePolynomialModel p B hB hstable).GeometryComplexityLE q →
      M.positivePolynomialLattice p B hstable ≤ D.lattice.comap (mapOfSteps M.filtration.positivePolynomialEvaluation) →
      (∀ c, c ≠ 0 → (∀ i, c ∉ J i) → M.filtration.layer (fun j => c j) = ⊥) →
      ∀ epsilon : ℝ, 0 < epsilon → 1 / epsilon ≤ Real.exp ((q + 2) ^ a) →
      (Fintype.card I : ℝ) ≤ Real.exp q →
      let E := fun i => M.positivePolynomialDownsetModel (J i) (hJ i) p B hB hstable
      letI : ∀ i, MetricSpace (E i).Space := fun i => (E i).metricSpace
      ∃ n : α → ℕ, (∀ i, 0 < n i) ∧ (∀ i, (n i : ℝ) ≤ Real.exp ((q + C) ^ C)) ∧
        (Fintype.card (∀ i, Fin (n i)) : ℝ) ≤ Real.exp ((q + C) ^ C) ∧
        ∃ K : α → ℝ≥0, (∀ i, (K i : ℝ) ≤ Real.exp ((q + C) ^ C)) ∧
          ∃ ψ : ∀ i, Fin (n i) → (E i).Space → ℝ,
            (∀ i j x, 0 ≤ ψ i j x ∧ ψ i j x ≤ 1) ∧
            (∀ i x, ∑ j, ψ i j x = 1) ∧ (∀ i j, LipschitzWith (K i) (ψ i j)) ∧
            ∀ (u : I → D.Space → ℂ) (ell : ℝ≥0), (ell : ℝ) ≤ Real.exp q →
              (letI := D.metricSpace; ∀ k, LipschitzWith ell (u k)) →
              (∀ k x, ‖u k x‖ ≤ 1) →
              ∃ c : (∀ i, Fin (n i)) → EuclideanSpace ℂ I,
                (∀ j k, ‖c j k‖ ≤ 2) ∧ (∀ j, ‖c j‖ ≤ Real.exp (q + 2)) ∧
                ∀ x, ‖(WithLp.toLp 2 (fun k => u k (QuotientGroup.mk (realificationMap
                    (hnil := M.filtration.positivePolynomialMultidegree.ordinary.lowerCentralSeries_eq_bot)
                    (hM := D.filtration.lowerCentralSeries_eq_bot) M.filtration.positivePolynomialEvaluation x))) : EuclideanSpace ℂ I) -
                  ∑ j, (∏ i, (ψ i (j i) (productProjection E i
                    (QuotientGroup.mk (M.filtration.positivePolynomialQuotientProductRealMap J hJ x))) : ℂ)) • c j‖ ≤ epsilon := by
  obtain ⟨C, hC, happ⟩ := exists_positivePolynomial_factor_approximation t (a + 1)
  refine ⟨C, hC, ?_⟩
  intro I α σ L _ _ _ _ _ _ _ s d D bound M J _ hJ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    p q B hB hstable ht hM hpq hα hX hmap hcover epsilon hepsilon hscale hI
  classical
  let E := fun i => M.positivePolynomialDownsetModel (J i) (hJ i) p B hB hstable
  let : ∀ i, MetricSpace (E i).Space := fun i => (E i).metricSpace
  have hq : 0 ≤ q := (Nat.cast_nonneg _).trans hX.1
  obtain ⟨hprecision, hprecision_scale⟩ := vector_approximation_precision a hq hI hepsilon hscale
  obtain ⟨n, hn, hnb, hcount, K, hKb, ψ, hunit, hsum, hLip, happrox⟩ :=
    happ M J hJ p q B hB hstable ht hM hpq hα hX hmap hcover
      (epsilon / (Fintype.card I + 1 : ℝ)) hprecision hprecision_scale
  refine ⟨n, hn, hnb, hcount, K, hKb, ψ, hunit, hsum, hLip, ?_⟩
  intro u ell hell hu hub
  choose coeff hcoeff herr using (fun k => happrox (u k) ell hell (hu k) (hub k))
  let c (j : ∀ i, Fin (n i)) : EuclideanSpace ℂ I := WithLp.toLp 2 (fun k => coeff k j)
  have hc : ∀ j k, ‖c j k‖ ≤ 2 := fun j k => hcoeff k j
  refine ⟨c, hc, fun j => euclidean_coefficient_norm_le_exp hq hI (c j) (hc j), ?_⟩
  intro x
  apply euclidean_error_le_of_coordinate_errors _ hepsilon.le
  intro k
  simpa only [PiLp.sub_apply, PiLp.toLp_apply, WithLp.ofLp_sum, Finset.sum_apply,
    WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul, c, WithLp.ofLp_toLp] using herr k x

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure


namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open NilpotentLieBCHGroup VectorPolynomial
open scoped BigOperators TensorProduct NNReal

theorem exists_uniform_positivePolynomial_splitting (t a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {I α σ L : Type*} [Fintype I] [Fintype α] [DecidableEq α]
      [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
      {s d : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
      (M : D.MultidegreeStructure bound) (J : α → Set (σ →₀ ℕ))
      [∀ i, DecidablePred (· ∈ J i)] (hJ : ∀ i, IsLowerSet (J i))
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      [TopologicalSpace (ℝ ⊗[ℚ] M.filtration.positivePolynomialAlgebra)]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] M.filtration.positivePolynomialAlgebra)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] M.filtration.positivePolynomialAlgebra)]
      [T2Space (ℝ ⊗[ℚ] M.filtration.positivePolynomialAlgebra)]
      [∀ i, TopologicalSpace (ℝ ⊗[ℚ] (M.filtration.positivePolynomialAlgebra ⧸
        restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra (J i) (hJ i)))]
      [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] (M.filtration.positivePolynomialAlgebra ⧸
        restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra (J i) (hJ i)))]
      [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] (M.filtration.positivePolynomialAlgebra ⧸
        restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra (J i) (hJ i)))]
      [∀ i, T2Space (ℝ ⊗[ℚ] (M.filtration.positivePolynomialAlgebra ⧸
        restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra (J i) (hJ i)))]
      [TopologicalSpace (ℝ ⊗[ℚ] (∀ i, M.filtration.positivePolynomialAlgebra ⧸
        restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra (J i) (hJ i)))]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ i, M.filtration.positivePolynomialAlgebra ⧸
        restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra (J i) (hJ i)))]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] (∀ i, M.filtration.positivePolynomialAlgebra ⧸
        restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra (J i) (hJ i)))]
      [T2Space (ℝ ⊗[ℚ] (∀ i, M.filtration.positivePolynomialAlgebra ⧸
        restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra (J i) (hJ i)))]
      (p : ℝ), (∑ i, bound i) = t → M.ComplexityLE p →
      (Fintype.card α : ℝ) ≤ p + 2 →
      (∀ c, c ≠ 0 → (∀ i, c ∉ J i) → M.filtration.layer (fun j => c j) = ⊥) →
      ∀ g : M.filtration.realification.PolynomialOrbit,
      M.filtration.realification.polynomialOrbitEval 0 g = 1 →
      ∀ epsilon : ℝ, 0 < epsilon → 1 / epsilon ≤ Real.exp ((p + 2) ^ a) →
      (Fintype.card I : ℝ) ≤ Real.exp p →
      ∃ (B : ℕ) (hB : 0 < B) (hstable : M.PositivePolynomialGridStable p B),
        (∀ i, (M.positivePolynomialDownsetModelMultidegree (J i) (hJ i) p B hB hstable).ComplexityLE ((p + C) ^ C)) ∧
        ∃ h : M.filtration.positivePolynomialMultidegree.realification.PolynomialOrbit,
          M.filtration.positivePolynomialMultidegree.realification.polynomialOrbitEval 0 h = 1 ∧
          ∃ n : α → ℕ, (∀ i, 0 < n i) ∧
            (∀ i, (n i : ℝ) ≤ Real.exp ((p + C) ^ C)) ∧
            (Fintype.card (∀ i, Fin (n i)) : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
            ∃ T : ∀ i, Fin (n i) → (M.positivePolynomialDownsetModel (J i) (hJ i) p B hB hstable).Niltest (fun _ : σ => 1),
              (∀ i j, (T i j).normBound = 1) ∧ (∀ i j, (T i j).UnitIntervalValued) ∧
              (∀ i j, (T i j).ComplexityLE ((p + C) ^ C)) ∧
              (∀ i j, (T i j).orbit =
                (M.positivePolynomialDownsetModelMultidegree (J i) (hJ i) p B hB hstable).orbitToOrdinary
                  (M.filtration.positivePolynomialDownsetOrbit (J i) (hJ i) h)) ∧
              ∀ (u : I → D.Space → ℂ) (ell : ℝ≥0), (ell : ℝ) ≤ Real.exp p →
                (letI := D.metricSpace; ∀ k, LipschitzWith ell (u k)) →
                (∀ k x, ‖u k x‖ ≤ 1) →
                ∃ c : (∀ i, Fin (n i)) → EuclideanSpace ℂ I,
                  (∀ j k, ‖c j k‖ ≤ 2) ∧ (∀ j, ‖c j‖ ≤ Real.exp ((p + C) ^ C)) ∧
                  ∀ x, ‖(WithLp.toLp 2 (fun k => u k
                      (QuotientGroup.mk (M.filtration.realification.polynomialOrbitEval x g))) : EuclideanSpace ℂ I) -
                    ∑ j, (∏ i, (T i (j i)).eval x) • c j‖ ≤ epsilon := by
  let hmodels_exists := exists_positivePolynomial_model_uniform t
  let b := hmodels_exists.choose
  have hmodels := hmodels_exists.choose_spec
  let happ_exists := exists_positivePolynomial_vector_factor_approximation t a
  let c := happ_exists.choose
  have happ := happ_exists.choose_spec
  let Q : Polynomial ℕ := Polynomial.X + (Polynomial.X + Polynomial.C b) ^ b + 2
  let P : Polynomial ℕ := Q + (Q + Polynomial.C c) ^ c + 2
  let hbudget_exists := exists_natPolynomial_eval_budget P
  let C := hbudget_exists.choose
  have hC : 2 ≤ C := hbudget_exists.choose_spec.1
  have hbudget : ∀ p : ℝ, 0 ≤ p →
      P.eval₂ (Nat.castRingHom ℝ) p ≤ (p + C) ^ C := hbudget_exists.choose_spec.2
  refine ⟨C, hC, ?_⟩
  intro I α σ L _ _ _ _ _ _ _ s d D bound M J _ hJ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    p ht hM hα hcover g hg epsilon hepsilon hscale hI
  classical
  have hp : 0 ≤ p := (Nat.cast_nonneg d).trans hM.1.1
  let q := p + (p + b) ^ b + 2
  have hmodel_nonneg : 0 ≤ (p + b) ^ b := by positivity
  have hpq : p ≤ q := by dsimp [q]; linarith only [hmodel_nonneg]
  have hq : 0 ≤ q := hp.trans hpq
  have hαq : (Fintype.card α : ℝ) ≤ q := by dsimp [q]; linarith only [hα, hmodel_nonneg]
  have hcost : q + (q + c) ^ c + 2 ≤ (p + C) ^ C := by
    simpa [P, Q, q, Polynomial.eval₂_pow] using hbudget p hp
  have hpow : 0 ≤ (q + c) ^ c := by positivity
  have hpower_cost : (q + c) ^ c ≤ (p + C) ^ C := by linarith only [hcost, hq]
  have hq_cost : q + 2 ≤ (p + C) ^ C := by linarith only [hcost, hpow]
  let model := hmodels.2 M ht hM
  let B := model.choose
  let hB : 0 < B := model.choose_spec.choose
  let hstable : M.PositivePolynomialGridStable p B := model.choose_spec.choose_spec.choose
  have hmodel := model.choose_spec.choose_spec.choose_spec.1
  have hmap : M.positivePolynomialLattice p B hstable ≤
      D.lattice.comap (mapOfSteps M.filtration.positivePolynomialEvaluation) :=
    model.choose_spec.choose_spec.choose_spec.2
  have hX : (M.positivePolynomialModel p B hB hstable).GeometryComplexityLE q :=
    (hmodel.mono _ (by dsimp [q]; linarith only [hp])).1
  let E := fun i => M.positivePolynomialDownsetModel (J i) (hJ i) p B hB hstable
  let : ∀ i, MetricSpace (E i).Space := fun i => (E i).metricSpace
  have hE (i) := M.positivePolynomialDownsetModel_complexity (J i) (hJ i) p q B hB hstable hX
  let lift := M.filtration.exists_realPositivePolynomial_orbit g hg
  let h := lift.choose
  have hh := lift.choose_spec.1
  have hproj := lift.choose_spec.2
  have hscaleq : 1 / epsilon ≤ Real.exp ((q + 2) ^ a) :=
    hscale.trans (Real.exp_le_exp.mpr (pow_le_pow_left₀ (by linarith only [hp]) (by linarith only [hpq]) a))
  have hIq : (Fintype.card I : ℝ) ≤ Real.exp q := hI.trans (Real.exp_le_exp.mpr hpq)
  let approximation :=
    happ.2 M J hJ p q B hB hstable ht hM hpq hαq hX hmap hcover epsilon hepsilon hscaleq hIq
  let n := approximation.choose
  have hn := approximation.choose_spec.1
  have hnb := approximation.choose_spec.2.1
  have hcount := approximation.choose_spec.2.2.1
  let constants := approximation.choose_spec.2.2.2
  let K := constants.choose
  have hKb := constants.choose_spec.1
  let factors := constants.choose_spec.2
  let ψ := factors.choose
  have hunit := factors.choose_spec.1
  have hsum := factors.choose_spec.2.1
  have hLip := factors.choose_spec.2.2.1
  have happrox := factors.choose_spec.2.2.2
  let T (i) (j : Fin (n i)) :=
    M.positivePolynomialFactorNiltest (J i) (hJ i) p B hB hstable h (ψ i j) (hunit i j) (K i) (hLip i j)
  have hT (i) (j : Fin (n i)) : (T i j).ComplexityLE ((p + C) ^ C) := by
    have hgeometry := (hE i).1.mono (E i) (le_add_of_nonneg_right hpow)
    have hK : (K i : ℝ) ≤ Real.exp (q + (q + c) ^ c) :=
      (hKb i).trans (Real.exp_le_exp.mpr (le_add_of_nonneg_left hq))
    exact (M.positivePolynomialFactorNiltest_complexity (J i) (hJ i) p B hB hstable h
      (ψ i j) (hunit i j) (K i) (hLip i j) hgeometry hK).mono hcost
  refine ⟨B, hB, hstable, fun i => (hE i).mono _ (by linarith only [hq_cost]), h, hh, n, hn,
    fun i => (hnb i).trans (Real.exp_le_exp.mpr hpower_cost),
    hcount.trans (Real.exp_le_exp.mpr hpower_cost), T, fun _ _ => rfl,
    fun i j => M.positivePolynomialFactorNiltest_unit_interval (J i) (hJ i) p B hB hstable h
      (ψ i j) (hunit i j) (K i) (hLip i j), hT, fun _ _ => rfl, ?_⟩
  intro u ell hell hu hub
  let coefficients := happrox u ell (hell.trans (Real.exp_le_exp.mpr hpq)) hu hub
  let coeff := coefficients.choose
  have hcoeff := coefficients.choose_spec.1
  have hcoeffnorm := coefficients.choose_spec.2.1
  have herr := coefficients.choose_spec.2.2
  refine ⟨coeff, hcoeff, fun j => (hcoeffnorm j).trans (Real.exp_le_exp.mpr hq_cost), ?_⟩
  have horbit := M.positivePolynomial_vector_error_of_lift J hJ p B hB hstable g h hproj
    n ψ coeff u epsilon herr
  intro x
  simpa only [T, M.positivePolynomialFactorNiltest_eval] using horbit x

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure


namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open Module NilpotentLieBCHGroup VectorPolynomial
open scoped BigOperators TensorProduct NNReal

theorem exists_canonical_positivePolynomial_splitting (t a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {I α σ L : Type*} [Fintype I] [Fintype α] [DecidableEq α]
      [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
      {s d : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
      (M : D.MultidegreeStructure bound) (J : α → Set (σ →₀ ℕ))
      [∀ i, DecidablePred (· ∈ J i)] (hJ : ∀ i, IsLowerSet (J i))
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (p : ℝ), (∑ i, bound i) = t → M.ComplexityLE p →
      (Fintype.card α : ℝ) ≤ p + 2 →
      (∀ c, c ≠ 0 → (∀ i, c ∉ J i) → M.filtration.layer (fun j => c j) = ⊥) →
      ∀ g : M.filtration.realification.PolynomialOrbit,
      M.filtration.realification.polynomialOrbitEval 0 g = 1 →
      ∀ epsilon : ℝ, 0 < epsilon → 1 / epsilon ≤ Real.exp ((p + 2) ^ a) →
      (Fintype.card I : ℝ) ≤ Real.exp p →
      letI : ∀ i, TopologicalSpace (ℝ ⊗[ℚ] (M.filtration.positivePolynomialAlgebra ⧸
        restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra (J i) (hJ i))) :=
        fun _ => moduleTopology ℝ _
      letI : ∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] (M.filtration.positivePolynomialAlgebra ⧸
        restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra (J i) (hJ i))) :=
        fun _ => IsModuleTopology.topologicalAddGroup ℝ _
      letI : ∀ i, T2Space (ℝ ⊗[ℚ] (M.filtration.positivePolynomialAlgebra ⧸
        restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra (J i) (hJ i))) :=
        fun i => realification_moduleTopology_t2 (M.positivePolynomialDownsetFinBasis (J i) (hJ i) p)
      ∃ (B : ℕ) (hB : 0 < B) (hstable : M.PositivePolynomialGridStable p B),
        (∀ i, (M.positivePolynomialDownsetModelMultidegree (J i) (hJ i) p B hB hstable).ComplexityLE ((p + C) ^ C)) ∧
        ∃ h : M.filtration.positivePolynomialMultidegree.realification.PolynomialOrbit,
          M.filtration.positivePolynomialMultidegree.realification.polynomialOrbitEval 0 h = 1 ∧
          ∃ n : α → ℕ, (∀ i, 0 < n i) ∧
            (∀ i, (n i : ℝ) ≤ Real.exp ((p + C) ^ C)) ∧
            (Fintype.card (∀ i, Fin (n i)) : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
            ∃ T : ∀ i, Fin (n i) → (M.positivePolynomialDownsetModel (J i) (hJ i) p B hB hstable).Niltest (fun _ : σ => 1),
              (∀ i j, (T i j).normBound = 1) ∧ (∀ i j, (T i j).UnitIntervalValued) ∧
              (∀ i j, (T i j).ComplexityLE ((p + C) ^ C)) ∧
              (∀ i j, (T i j).orbit =
                (M.positivePolynomialDownsetModelMultidegree (J i) (hJ i) p B hB hstable).orbitToOrdinary
                  (M.filtration.positivePolynomialDownsetOrbit (J i) (hJ i) h)) ∧
              ∀ (u : I → D.Space → ℂ) (ell : ℝ≥0), (ell : ℝ) ≤ Real.exp p →
                (letI := D.metricSpace; ∀ k, LipschitzWith ell (u k)) →
                (∀ k x, ‖u k x‖ ≤ 1) →
                ∃ c : (∀ i, Fin (n i)) → EuclideanSpace ℂ I,
                  (∀ j k, ‖c j k‖ ≤ 2) ∧ (∀ j, ‖c j‖ ≤ Real.exp ((p + C) ^ C)) ∧
                  ∀ x, ‖(WithLp.toLp 2 (fun k => u k
                      (QuotientGroup.mk (M.filtration.realification.polynomialOrbitEval x g))) : EuclideanSpace ℂ I) -
                    ∑ j, (∏ i, (T i (j i)).eval x) • c j‖ ≤ epsilon := by
  obtain ⟨C, hC, hsplit⟩ := exists_uniform_positivePolynomial_splitting t a
  refine ⟨C, hC, ?_⟩
  intro I α σ L _ _ _ _ _ _ _ s d D bound M J _ hJ _ _ _ _
    p ht hM hα hcover g hg epsilon hepsilon hscale hI
  let : ∀ i, TopologicalSpace (ℝ ⊗[ℚ] (M.filtration.positivePolynomialAlgebra ⧸
        restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra (J i) (hJ i))) := fun _ => moduleTopology ℝ _
  let : ∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] (M.filtration.positivePolynomialAlgebra ⧸
        restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra (J i) (hJ i))) :=
    fun _ => IsModuleTopology.topologicalAddGroup ℝ _
  let : ∀ i, T2Space (ℝ ⊗[ℚ] (M.filtration.positivePolynomialAlgebra ⧸
        restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra (J i) (hJ i))) :=
    fun i => realification_moduleTopology_t2 (M.positivePolynomialDownsetFinBasis (J i) (hJ i) p)
  let := moduleTopology ℝ (ℝ ⊗[ℚ] M.filtration.positivePolynomialAlgebra)
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] M.filtration.positivePolynomialAlgebra) :=
    IsModuleTopology.topologicalAddGroup ℝ _
  let : T2Space (ℝ ⊗[ℚ] M.filtration.positivePolynomialAlgebra) :=
    realification_moduleTopology_t2 (M.positivePolynomialFinBasis p)
  let : ∀ i, FiniteDimensional ℚ (M.filtration.positivePolynomialAlgebra ⧸
      restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra (J i) (hJ i)) :=
    fun i => (M.positivePolynomialDownsetFinBasis (J i) (hJ i) p).finiteDimensional_of_finite
  let := moduleTopology ℝ (ℝ ⊗[ℚ] (∀ i, M.filtration.positivePolynomialAlgebra ⧸
    restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra (J i) (hJ i)))
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ i, M.filtration.positivePolynomialAlgebra ⧸
      restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra (J i) (hJ i))) :=
    IsModuleTopology.topologicalAddGroup ℝ _
  let : T2Space (ℝ ⊗[ℚ] (∀ i, M.filtration.positivePolynomialAlgebra ⧸
      restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra (J i) (hJ i))) :=
    realification_moduleTopology_t2 (Module.finBasis ℚ _)
  exact hsplit M J hJ p ht hM hα hcover g hg epsilon hepsilon hscale hI

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.TwoDownsetPrecision
namespace OAI


namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open Module NilpotentLieBCHGroup VectorPolynomial
open scoped BigOperators TensorProduct NNReal

theorem exists_multidegree_downset_splitting (s t a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ DownsetSplittingStatement s t a C := by
  obtain ⟨b, _, hnormalize⟩ := exists_controlled_multidegree_basepoint_normalization s
  obtain ⟨c, _, hsplit⟩ := exists_canonical_positivePolynomial_splitting t a
  let Q : Polynomial ℕ := Polynomial.X + (Polynomial.X + Polynomial.C b) ^ b + 2
  let P : Polynomial ℕ := Q + (Q + Polynomial.C c) ^ c + 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro I α σ L _ _ _ _ _ _ _ d D bound M J _ hJ _ _ _ _
    p ht hM hα hcover g epsilon hepsilon hscale hI
  let : ∀ i, TopologicalSpace (ℝ ⊗[ℚ] (M.filtration.positivePolynomialAlgebra ⧸
      restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra (J i) (hJ i))) :=
    fun _ => moduleTopology ℝ _
  let : ∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] (M.filtration.positivePolynomialAlgebra ⧸
      restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra (J i) (hJ i))) :=
    fun _ => IsModuleTopology.topologicalAddGroup ℝ _
  let : ∀ i, T2Space (ℝ ⊗[ℚ] (M.filtration.positivePolynomialAlgebra ⧸
      restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra (J i) (hJ i))) :=
    fun i => realification_moduleTopology_t2 (M.positivePolynomialDownsetFinBasis (J i) (hJ i) p)
  have hp : 0 ≤ p := (Nat.cast_nonneg d).trans hM.1.1
  let r := p + (p + b) ^ b + 2
  have hnormal_nonneg : 0 ≤ (p + b) ^ b := by positivity
  have hpr : p ≤ r := by dsimp [r]; linarith only [hnormal_nonneg]
  have hr : 0 ≤ r := hp.trans hpr
  have hcost : r + (r + c) ^ c + 2 ≤ (p + C) ^ C := by
    simpa [P, Q, r, Polynomial.eval₂_pow] using hbudget p hp
  have hpow : 0 ≤ (r + c) ^ c := by positivity
  have hr_cost : r ≤ (p + C) ^ C := by linarith only [hcost, hpow]
  have hpower_cost : (r + c) ^ c ≤ (p + C) ^ C := by linarith only [hcost, hr]
  obtain ⟨ε, A, hA, hLip, g', hg', heval⟩ := hnormalize M hp hM.1 g
  have hshift : p + 2 ≤ r + 2 := by linarith only [hpr]
  have hscale_r : 1 / epsilon ≤ Real.exp ((r + 2) ^ a) :=
    hscale.trans (Real.exp_le_exp.mpr (pow_le_pow_left₀ (by positivity) hshift a))
  obtain ⟨B, hB, hstable, hresult⟩ :=
    hsplit (I := I) (α := α) (σ := σ) (L := L) M J hJ r ht (hM.mono M hpr) (hα.trans hshift) hcover g' hg'
      epsilon hepsilon hscale_r (hI.trans (Real.exp_le_exp.mpr hpr))
  obtain ⟨hE, h, hh, hresult⟩ := hresult
  obtain ⟨n, hn, hnb, hcount, T, hresult⟩ := hresult
  obtain ⟨hTnorm, hTunit, hT, hTorbit, happrox⟩ := hresult
  have hdim (i) : Fintype.card (M.PositivePolynomialDownsetIndex (J i)) ≤ 2 ^ t * d := by
    apply (M.positivePolynomialDownsetIndex_card_le (J i)).trans
    simpa only [ht] using M.positivePolynomialBasisIndex_card_le r
  refine ⟨r, hpr, hr_cost, B, hB, hstable, fun i => (hE i).mono _ hpower_cost,
    hdim, h, hh, n, hn, fun i => (hnb i).trans (Real.exp_le_exp.mpr hpower_cost),
    hcount.trans (Real.exp_le_exp.mpr hpower_cost), T, hTnorm, hTunit,
    fun i j => (hT i j).mono hpower_cost, hTorbit, ?_⟩
  let := D.metricSpace
  have htranslated_bound : Real.exp p * (A : ℝ) ≤ Real.exp r := by
    calc
      _ ≤ Real.exp p * Real.exp ((p + b) ^ b) :=
        mul_le_mul_of_nonneg_left hA (Real.exp_nonneg _)
      _ = Real.exp (p + (p + b) ^ b) := (Real.exp_add _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by dsimp [r]; exact le_add_of_nonneg_right (by norm_num))
  exact vector_approximation_precompose (I := I) (J := ∀ i, Fin (n i))
    (S := σ → ℤ) (X := D.Space) (A := A) (p := p) (q := r)
    (B := Real.exp ((r + c) ^ c)) (B' := Real.exp ((p + C) ^ C))
    (epsilon := epsilon) (fun y : D.Space => ε • y)
    (fun x => QuotientGroup.mk (M.filtration.realification.polynomialOrbitEval x g'))
    (fun x => QuotientGroup.mk (M.filtration.realification.polynomialOrbitEval x g))
    (fun j x => ∏ i, (T i (j i)).eval x) hLip heval htranslated_bound
    (Real.exp_le_exp.mpr hpower_cost) happrox

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure


namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open Module VectorPolynomial
open scoped BigOperators TensorProduct

theorem exists_two_downset_splitting (s t a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ TwoDownsetSplittingStatement s t a C := by
  obtain ⟨b, _, hsplit⟩ := exists_multidegree_downset_splitting s t a
  let P : Polynomial ℕ := (Polynomial.X + Polynomial.C b) ^ b + 1
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro σ L _ _ _ _ d D bound M J _ hJ _ _ _ _ p ht hM hcover g epsilon hepsilon hscale
  classical
  let : ∀ i, TopologicalSpace (ℝ ⊗[ℚ] (M.filtration.positivePolynomialAlgebra ⧸
      restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra (J i) (hJ i))) :=
    fun _ => moduleTopology ℝ _
  let : ∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] (M.filtration.positivePolynomialAlgebra ⧸
      restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra (J i) (hJ i))) :=
    fun _ => IsModuleTopology.topologicalAddGroup ℝ _
  let : ∀ i, T2Space (ℝ ⊗[ℚ] (M.filtration.positivePolynomialAlgebra ⧸
      restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra (J i) (hJ i))) :=
    fun i => realification_moduleTopology_t2 (M.positivePolynomialDownsetFinBasis (J i) (hJ i) p)
  have hp : 0 ≤ p := (Nat.cast_nonneg d).trans hM.1.1
  have hcost : (p + b) ^ b + 1 ≤ (p + C) ^ C := by
    simpa [P, Polynomial.eval₂_pow] using hbudget p hp
  have hcost' : (p + b) ^ b ≤ (p + C) ^ C := by linarith only [hcost]
  have hfamily : (Fintype.card Bool : ℝ) ≤ p + 2 := by
    simp only [Fintype.card_bool, Nat.cast_ofNat]
    linarith only [hp]
  have hsupport : ∀ c, c ≠ 0 → (∀ i, c ∉ J i) → M.filtration.layer (fun j => c j) = ⊥ := by
    intro c hc hout
    apply hcover c hc
    rintro (hl | hr)
    · exact hout false hl
    · exact hout true hr
  obtain ⟨r, hpr, hr, B, hB, hstable, hresult⟩ :=
    hsplit (I := Unit) (α := Bool) (σ := σ) (L := L) M J hJ p ht hM hfamily hsupport
      g epsilon hepsilon hscale (by simpa using Real.one_le_exp hp)
  obtain ⟨hE, hdim, h, hh, hresult⟩ := hresult
  obtain ⟨n, hn, hnb, hcount, T, hresult⟩ := hresult
  obtain ⟨hTnorm, hTunit, hT, hTorbit, happrox⟩ := hresult
  let E := fun i => M.positivePolynomialDownsetModel (J i) (hJ i) r B hB hstable
  have hterminal : ∀ i c, c ∉ J i →
      (M.positivePolynomialDownsetModelMultidegree (J i) (hJ i) r B hB hstable).filtration.layer
        (fun j => c j) = ⊥ := by
    intro i c hc
    exact M.filtration.positivePolynomialDownsetQuotient_terminal (J i) (hJ i) c hc
  refine ⟨r, hpr, hr.trans hcost', B, hB, hstable,
    fun i => (hE i).mono _ hcost', hdim, hterminal, h, hh, ?_⟩
  intro u ell hell hu hub
  let coefficients := happrox (fun _ : Unit => u) ell hell (fun _ => hu) (fun _ => hub)
  let coeff := coefficients.choose
  have hcoeff := coefficients.choose_spec.1
  have herr := coefficients.choose_spec.2.2
  have hscalar := scalar_error_le_of_vector_error (I := Unit) (J := ∀ i, Fin (n i))
    (S := σ → ℤ) (epsilon := epsilon)
    (fun _ : Unit => fun x => u (QuotientGroup.mk (M.filtration.realification.polynomialOrbitEval x g)))
    (fun j x => ∏ i, (T i (j i)).eval x) coeff herr ()
  let : Nonempty (∀ i, Fin (n i)) := ⟨fun i => ⟨0, hn i⟩⟩
  let pairSum := exists_bounded_niltest_pair_sum (J := ∀ i, Fin (n i)) (σ := σ)
      (p := (p + b) ^ b) (E false) (E true) (fun _ : σ => 1)
      ((M.positivePolynomialDownsetModelMultidegree (J false) (hJ false) r B hB hstable).orbitToOrdinary
        (M.filtration.positivePolynomialDownsetOrbit (J false) (hJ false) h))
      ((M.positivePolynomialDownsetModelMultidegree (J true) (hJ true) r B hB hstable).orbitToOrdinary
        (M.filtration.positivePolynomialDownsetOrbit (J true) (hJ true) h))
      (fun j => T false (j false)) (fun j => T true (j true)) (fun j => coeff j ())
      (fun j => (hTnorm false (j false)).le) (fun j => (hTnorm true (j true)).le)
      (fun j => hT false (j false)) (fun j => hT true (j true))
      (fun j => hTorbit false (j false)) (fun j => hTorbit true (j true)) (fun j => hcoeff j ())
  let N := pairSum.choose
  have hNpos := pairSum.choose_spec.1
  have hN : N = 2 * Fintype.card (∀ i, Fin (n i)) := pairSum.choose_spec.2.1
  let leftTests := pairSum.choose_spec.2.2
  let A := leftTests.choose
  let rightTests := leftTests.choose_spec
  let B' := rightTests.choose
  have hdata := rightTests.choose_spec
  have hAnorm := hdata.1
  have hBnorm := hdata.2.1
  have hA := hdata.2.2.1
  have hB' := hdata.2.2.2.1
  have hAg := hdata.2.2.2.2.1
  have hBg := hdata.2.2.2.2.2.1
  have heval := hdata.2.2.2.2.2.2
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith only [Real.add_one_le_exp (1 : ℝ)]
  have hNbound : (N : ℝ) ≤ Real.exp ((p + C) ^ C) := by
    rw [hN, Nat.cast_mul, Nat.cast_ofNat]
    calc
      _ ≤ 2 * Real.exp ((p + b) ^ b) := mul_le_mul_of_nonneg_left hcount (by norm_num)
      _ = Real.exp ((p + b) ^ b) * 2 := mul_comm _ _
      _ ≤ Real.exp ((p + b) ^ b) * Real.exp 1 :=
        mul_le_mul_of_nonneg_left htwo (Real.exp_nonneg _)
      _ = Real.exp ((p + b) ^ b + 1) := (Real.exp_add _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr hcost
  refine ⟨N, hNpos, hNbound, A, B', hAnorm, hBnorm,
    fun j => (hA j).mono hcost', fun j => (hB' j).mono hcost', hAg, hBg, ?_⟩
  intro x
  rw [heval x]
  convert hscalar x using 1
  congr 2
  apply Finset.sum_congr rfl
  intro j _
  rw [Fintype.prod_bool, mul_comm ((T true (j true)).eval x) ((T false (j false)).eval x)]

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure


end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.TotalDegreeNiltestSplitting
namespace OAI

section

namespace Erdos3

open Module VectorPolynomial RationalFilteredNilmanifold
open RationalFilteredNilmanifold.MultidegreeStructure
open scoped TensorProduct BigOperators NNReal

theorem exists_totalDegree_niltest_splitting (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L : Type} [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {d : ℕ} {D : RationalFilteredNilmanifold L s d} {p : ℝ}
      (T : D.Niltest (fun _ : Fin 2 => 1)), T.ComplexityLE p → T.normBound ≤ 1 →
      ∀ epsilon : ℝ, 0 < epsilon → 1 / epsilon ≤ Real.exp ((p + 2) ^ a) →
      Nonempty (NativeTwoVariableSplit s d ((p + C) ^ C) epsilon T.eval) := by
  obtain ⟨C, hC, hsplit⟩ := exists_two_downset_splitting s (2 * s) a
  refine ⟨C, hC, ?_⟩
  intro L _ _ _ _ _ _ d D p T hT hnorm epsilon hepsilon hscale
  classical
  let M := D.totalDegreeMultidegree (Fin 2) hT.1
  let J := totalDegreeSplitDownset s
  have hJ : ∀ b, IsLowerSet (J b) := totalDegreeSplitDownset_lower s
  let K := fun b => M.filtration.positivePolynomialAlgebra ⧸
    restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra (J b) (hJ b)
  let : ∀ b, TopologicalSpace (ℝ ⊗[ℚ] K b) := fun _ => moduleTopology ℝ _
  let : ∀ b, IsTopologicalAddGroup (ℝ ⊗[ℚ] K b) :=
    fun _ => IsModuleTopology.topologicalAddGroup ℝ _
  let : ∀ b, T2Space (ℝ ⊗[ℚ] K b) :=
    fun b => realification_moduleTopology_t2 (M.positivePolynomialDownsetFinBasis (J b) (hJ b) p)
  let g := D.filtration.realTotalDegreeOrbit T.orbit
  have hsum : (∑ _ : Fin 2, s) = 2 * s := by simp
  have hM : M.ComplexityLE p := D.totalDegreeMultidegree_complexity (Fin 2) hT.1
  have hcover : ∀ c, c ≠ 0 → c ∉ J false ∪ J true →
      M.filtration.layer (fun i => c i) = ⊥ :=
    fun c _ hc => totalDegreeSplitDownset_terminal D.filtration c hc
  obtain ⟨r, _, _, B, hB, hstable, hresult⟩ :=
    hsplit M J hJ p hsum hM hcover g epsilon hepsilon hscale
  obtain ⟨hE, hdim, hterminal, h, _, happrox⟩ := hresult
  have hlip : (T.lipBound : ℝ) ≤ Real.exp p := by
    have hb := T.observable_budget hT
    have hn := T.normBound.coe_nonneg
    linarith
  have hub : ∀ x, ‖T.observable x‖ ≤ 1 := fun x =>
    (T.norm_le x).trans (show (T.normBound : ℝ) ≤ 1 from hnorm)
  obtain ⟨N, hN, hNbound, A, B', hAnorm, hBnorm, hA, hB', hAg, hBg, herr⟩ :=
    happrox T.observable T.lipBound hlip T.lipschitz hub
  let E := fun b => M.positivePolynomialDownsetModel (J b) (hJ b) r B hB hstable
  let F := fun b => M.positivePolynomialDownsetModelMultidegree (J b) (hJ b) r B hB hstable
  have hzero (b : Bool) (v : Fin 2 → ℕ) (hv : ¬v ≤ totalDegreeSplitBound s b) :
      (F b).filtration.layer v = ⊥ := by
    let c : Fin 2 →₀ ℕ := Finsupp.equivFunOnFinite.symm v
    exact hterminal b c hv
  let R := fun b => (F b).restrictBound (totalDegreeSplitBound s b)
    (totalDegreeSplitBound_le s b) (hzero b)
  let tests : ∀ b, Fin N → (E b).Niltest (fun _ : Fin 2 => 1) :=
    fun b => match b with
      | false => A
      | true => B'
  refine ⟨{
    count := N
    count_pos := hN
    count_bound := hNbound
    L := K
    dim := fun b => Fintype.card (M.PositivePolynomialDownsetIndex (J b))
    model := E
    multi := R
    complexity := fun b => (F b).restrictBound_complexity (totalDegreeSplitBound s b)
      (totalDegreeSplitBound_le s b) (hzero b) (hE b)
    dimension_bound := hdim
    orbit := fun b => (F b).filtration.restrictBoundRealOrbit (totalDegreeSplitBound s b)
      (hzero b) (M.filtration.positivePolynomialDownsetOrbit (J b) (hJ b) h)
    test := tests
    test_norm := ?_
    test_complexity := ?_
    test_orbit := ?_
    approximation := ?_ }⟩
  · intro b j
    cases b
    · exact hAnorm j
    · exact hBnorm j
  · intro b j
    cases b
    · exact hA j
    · exact hB' j
  · intro b j
    cases b
    · exact hAg j
    · exact hBg j
  · intro x
    change ‖T.eval x - ∑ j, (A j).eval x * (B' j).eval x‖ ≤ epsilon
    have heval : T.observable (QuotientGroup.mk (M.filtration.realification.polynomialOrbitEval x g)) =
        T.eval x := by
      change T.observable (QuotientGroup.mk
        ((D.filtration.totalDegreeMultifiltration (Fin 2)).realification.polynomialOrbitEval x
          (D.filtration.realTotalDegreeOrbit T.orbit))) = _
      rw [D.filtration.realTotalDegreeOrbit_eval]
      rfl
    simpa only [heval] using herr x

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeGlobalErrorSplitting
namespace OAI

section

namespace Erdos3.NativeCorrelationStructure

open scoped BigOperators TensorProduct

attribute [local instance] NativeVectorCorrelation.lie NativeVectorCorrelation.algebra
  NativeVectorCorrelation.topology NativeVectorCorrelation.topologicalAdd
  NativeVectorCorrelation.continuousSMul NativeVectorCorrelation.hausdorff

variable {s r N : ℕ} [NeZero N] {p : ℝ} {f : ZMod N → ℂ}
  (W : NativeCorrelationStructure s r N p f)

noncomputable def normalizedErrorCorrelator (b : ℝ) (m : ZMod N → ZMod N → ℂ)
    (h x : ZMod N) : ℂ :=
  multiplicativeDerivative f h x * star (m h x * W.normalizedLower b h x)

end Erdos3.NativeCorrelationStructure

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeDilationDescent
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open CircleFourier
open scoped TensorProduct BigOperators

variable {σ L I : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L] [Fintype I]
  {s d r : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  (M : D.MultidegreeStructure bound)

theorem unitVertical_dilation_top_invariant (q : ℤ) (hs : ∑ j, bound j = s)
    (E : RationalFilteredNilmanifold (M.filtration.ordinary.dilationPairSubalgebra (q : ℚ)) s r)
    (hEL : E.lattice = M.dilationPairLattice (q : ℚ))
    {p : ℝ} (V : D.UnitVerticalObservable (M.realSubgroup bound) I p)
    (ε : D.RealGroup) (a₀ : I) (a : Fin (q ^ s).natAbs → I) (k : E.RealGroup)
    (hk : k ∈ (M.filtration.ordinary.dilationPairFiltration (q : ℚ)).realification.subgroup s)
    (x : E.Space) :
    M.dilationObservable (q : ℚ) E hEL (q ^ s) ε (V.observable a₀)
        (fun j => V.observable (a j)) (k • x) =
      M.dilationObservable (q : ℚ) E hEL (q ^ s) ε (V.observable a₀)
        (fun j => V.observable (a j)) x := by
  apply M.dilationObservable_top_invariant (q : ℚ) E hEL (q ^ s) ε
    (V.observable a₀) (fun j => V.observable (a j))
    (fun z => (realifyFunctional V.frequency z.coord : CircleFourier.Circle)) ?_ ?_ k hk ?_ x
  · exact fun z hz y => M.unitVertical_top_action hs V a₀ z hz y
  · exact fun j z hz y => M.unitVertical_top_action hs V (a j) z hz y
  · exact M.filtration.ordinary.realDilationPair_frequency_phase q V.frequency ⟨k.coord⟩ hk

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open NilpotentLieBCHGroup
open scoped TensorProduct BigOperators NNReal

variable {σ L I : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
  [Fintype I] {s d r n : ℕ} {D : RationalFilteredNilmanifold L (s + 1) d} {bound : σ → ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  (M : D.MultidegreeStructure bound) (q : ℤ) (hs : ∑ j, bound j = s + 1)
  (E : RationalFilteredNilmanifold (M.filtration.ordinary.dilationPairSubalgebra (q : ℚ)) (s + 1) r)
  (hEF : E.filtration = M.filtration.ordinary.dilationPairFiltration (q : ℚ))
  (hEL : E.lattice = M.dilationPairLattice (q : ℚ))
  [TopologicalSpace (ℝ ⊗[ℚ] M.filtration.ordinary.dilationPairSubalgebra (q : ℚ))]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] M.filtration.ordinary.dilationPairSubalgebra (q : ℚ))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] M.filtration.ordinary.dilationPairSubalgebra (q : ℚ))]
  [T2Space (ℝ ⊗[ℚ] M.filtration.ordinary.dilationPairSubalgebra (q : ℚ))]
  (Q : RationalFilteredNilmanifold
    ((M.filtration.ordinary.dilationPairSubalgebra (q : ℚ)) ⧸ E.filtration.layerIdeal (s + 1)) s n)
  (hQF : Q.filtration = E.filtration.quotientTop)
  (hQL : Q.lattice = E.lattice.map
    (E.filtration.quotientStepHom (E.filtration.layerIdeal (s + 1)) (t := s) le_rfl))
  [TopologicalSpace (ℝ ⊗[ℚ]
    ((M.filtration.ordinary.dilationPairSubalgebra (q : ℚ)) ⧸ E.filtration.layerIdeal (s + 1)))]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ]
    ((M.filtration.ordinary.dilationPairSubalgebra (q : ℚ)) ⧸ E.filtration.layerIdeal (s + 1)))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ]
    ((M.filtration.ordinary.dilationPairSubalgebra (q : ℚ)) ⧸ E.filtration.layerIdeal (s + 1)))]
  [T2Space (ℝ ⊗[ℚ]
    ((M.filtration.ordinary.dilationPairSubalgebra (q : ℚ)) ⧸ E.filtration.layerIdeal (s + 1)))]

include hs hEF hQF hQL

omit [DecidableEq σ] in
theorem exists_unitVertical_dilation_quotient_niltest {τ : Type*} {w : τ → ℕ}
    {H : ℕ} (hH : 1 ≤ H)
    (hentries : ∀ j k, RationalHeightLE
      (Q.basis.repr (lieQuotientMap (E.filtration.layerIdeal (s + 1)) (E.basis k)) j) H)
    (hstructure : ∀ a b c, RationalHeightLE (lieStructureConstants Q.basis a b c) H)
    {p : ℝ} (V : D.UnitVerticalObservable (M.realSubgroup bound) I p)
    (ε : D.RealGroup) (a₀ : I) (a : Fin (q ^ (s + 1)).natAbs → I) (A : ℝ≥0)
    (hLip : letI := E.metricSpace
      LipschitzWith A (M.dilationObservable (q : ℚ) E hEL (q ^ (s + 1)) ε
        (V.observable a₀) (fun j => V.observable (a j))))
    (g : E.filtration.realification.PolynomialOrbit w) :
    ∃ T : Q.Niltest w, T.normBound = 1 ∧
      T.lipBound = rationalReconstructionLipschitzBound s r n H A 1 ∧
      T.orbit = E.topQuotientOrbit Q hQF g ∧
      ∀ x : τ → ℤ, T.eval x =
        M.dilationObservable (q : ℚ) E hEL (q ^ (s + 1)) ε
          (V.observable a₀) (fun j => V.observable (a j))
          (QuotientGroup.mk (E.filtration.realification.polynomialOrbitEval w x g)) := by
  let U : E.Niltest w :=
    { orbit := g
      observable := M.dilationObservable (q : ℚ) E hEL (q ^ (s + 1)) ε
        (V.observable a₀) (fun j => V.observable (a j))
      normBound := 1
      lipBound := A
      norm_le := M.dilationObservable_norm_le (q : ℚ) E hEL (q ^ (s + 1)) ε
        (V.observable a₀) (fun j => V.observable (a j)) (V.norm a₀) (fun j => V.norm (a j))
      lipschitz := hLip }
  have hinv : ∀ k ∈ E.filtration.realification.subgroup (s + 1), ∀ x,
      U.observable (k • x) = U.observable x := by
    intro k hk x
    have hk' : k ∈ (M.filtration.ordinary.dilationPairFiltration (q : ℚ)).realification.subgroup
        (s + 1) := by rw [← hEF]; exact hk
    exact M.unitVertical_dilation_top_invariant q hs E hEL V ε a₀ a k hk' x
  obtain ⟨T, hTo, hTn, hTl, hTe⟩ := E.exists_topInvariant_niltest Q hQF hQL U hinv H hH hentries hstructure
  exact ⟨T, hTn, hTl, hTo, hTe⟩

theorem exists_dilation_niltest_of_data {H : ℕ} (hH : 1 ≤ H)
    (hentries : ∀ j k, RationalHeightLE
      (Q.basis.repr (lieQuotientMap (E.filtration.layerIdeal (s + 1)) (E.basis k)) j) H)
    (hstructure : ∀ a b c, RationalHeightLE (lieStructureConstants Q.basis a b c) H)
    {p : ℝ} (V : D.UnitVerticalObservable (M.realSubgroup bound) I p)
    (g : M.filtration.realification.PolynomialOrbit) (ε γ : D.RealGroup)
    (hγ : γ ∈ D.realLattice) (hfactor : M.filtration.realification.polynomialOrbitEval 0 g = ε * γ)
    (a₀ : I) (a : Fin (q ^ (s + 1)).natAbs → I) (A : ℝ≥0)
    (hLip : letI := E.metricSpace
      LipschitzWith A (M.dilationObservable (q : ℚ) E hEL (q ^ (s + 1)) ε
        (V.observable a₀) (fun j => V.observable (a j)))) :
    ∃ T : Q.Niltest (fun _ : σ => 1), T.normBound = 1 ∧
      T.lipBound = rationalReconstructionLipschitzBound s r n H A 1 ∧
      Q.filtration.realification.polynomialOrbitEval _ 0 T.orbit = 1 ∧
      ∀ x, T.eval x =
        V.observable a₀ (QuotientGroup.mk (M.filtration.realification.polynomialOrbitEval
          (fun i => q * x i) g)) *
        star (signedTensorProduct (q ^ (s + 1)) (fun j => V.observable (a j)
          (QuotientGroup.mk (M.filtration.realification.polynomialOrbitEval x g)))) := by
  obtain ⟨h, hh0, hh⟩ := M.exists_native_dilation_orbit q E hEF g ε γ hγ hfactor
  obtain ⟨T, hTn, hTl, hTo, hTe⟩ := M.exists_unitVertical_dilation_quotient_niltest
    q hs E hEF hEL Q hQF hQL hH hentries hstructure V ε a₀ a A hLip h
  refine ⟨T, hTn, hTl, ?_, ?_⟩
  · rw [hTo, E.topQuotientOrbit_eval Q hQF, hh0, map_one]
  · intro x
    rw [hTe, M.dilationObservable_mk, (hh x).1, (hh x).2]

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.PreparedDilationNiltest
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open NilpotentLieBCHGroup
open scoped TensorProduct BigOperators NNReal

variable {σ L I : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
  [Fintype I] {s d r n : ℕ} {D : RationalFilteredNilmanifold L (s + 1) d} {bound : σ → ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  (M : D.MultidegreeStructure bound) (q : ℤ) (hs : ∑ j, bound j = s + 1)
  (E : RationalFilteredNilmanifold (M.filtration.ordinary.dilationPairSubalgebra (q : ℚ)) (s + 1) r)
  (hEF : E.filtration = M.filtration.ordinary.dilationPairFiltration (q : ℚ))
  (hEL : E.lattice = M.dilationPairLattice (q : ℚ))
  [TopologicalSpace (ℝ ⊗[ℚ] M.filtration.ordinary.dilationPairSubalgebra (q : ℚ))]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] M.filtration.ordinary.dilationPairSubalgebra (q : ℚ))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] M.filtration.ordinary.dilationPairSubalgebra (q : ℚ))]
  [T2Space (ℝ ⊗[ℚ] M.filtration.ordinary.dilationPairSubalgebra (q : ℚ))]
  (Q : RationalFilteredNilmanifold
    ((M.filtration.ordinary.dilationPairSubalgebra (q : ℚ)) ⧸ E.filtration.layerIdeal (s + 1)) s n)
  (hQF : Q.filtration = E.filtration.quotientTop)
  (hQL : Q.lattice = E.lattice.map
    (E.filtration.quotientStepHom (E.filtration.layerIdeal (s + 1)) (t := s) le_rfl))
  [TopologicalSpace (ℝ ⊗[ℚ]
    ((M.filtration.ordinary.dilationPairSubalgebra (q : ℚ)) ⧸ E.filtration.layerIdeal (s + 1)))]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ]
    ((M.filtration.ordinary.dilationPairSubalgebra (q : ℚ)) ⧸ E.filtration.layerIdeal (s + 1)))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ]
    ((M.filtration.ordinary.dilationPairSubalgebra (q : ℚ)) ⧸ E.filtration.layerIdeal (s + 1)))]
  [T2Space (ℝ ⊗[ℚ]
    ((M.filtration.ordinary.dilationPairSubalgebra (q : ℚ)) ⧸ E.filtration.layerIdeal (s + 1)))]

include hs hEF hEL hQF hQL

theorem exists_prepared_dilation_niltest {p : ℝ} (hp : 0 ≤ p)
    (hD : D.GeometryComplexityLE p) (hE : E.GeometryComplexityLE p)
    (hheight : ∀ j a k, rationalLogHeight
      (D.basis.repr (M.filtration.ordinary.dilationPairProjection (q : ℚ) j (E.basis a)) k) ≤ p)
    (hQ : Q.GeometryComplexityLE p)
    (hq : ∀ j k, rationalLogHeight
      (Q.basis.repr (lieQuotientMap (E.filtration.layerIdeal (s + 1)) (E.basis k)) j) ≤ p)
    (V : D.UnitVerticalObservable (M.realSubgroup bound) I p)
    (g : M.filtration.realification.PolynomialOrbit) (ε γ : D.RealGroup)
    (hγ : γ ∈ D.realLattice) (hfactor : M.filtration.realification.polynomialOrbitEval 0 g = ε * γ)
    (A : ℝ≥0) (hA : (A : ℝ) ≤ Real.exp p)
    (hε : letI := D.metricSpace; LipschitzWith A (fun x : D.Space => ε • x))
    (a₀ : I) (a : Fin (q ^ (s + 1)).natAbs → I) :
    ∃ T : Q.Niltest (fun _ : σ => 1), T.normBound = 1 ∧
      T.ComplexityLE (DilationBudget.total (s + 1) q (MultilinearityBudget.reconstructionExponent s) p) ∧
      Q.filtration.realification.polynomialOrbitEval _ 0 T.orbit = 1 ∧
      ∀ x, T.eval x =
        V.observable a₀ (QuotientGroup.mk (M.filtration.realification.polynomialOrbitEval
          (fun i => q * x i) g)) *
        star (signedTensorProduct (q ^ (s + 1)) (fun j => V.observable (a j)
          (QuotientGroup.mk (M.filtration.realification.polynomialOrbitEval x g)))) := by
  let H := ⌈Real.exp p⌉₊
  let B : ℝ≥0 := ((q ^ (s + 1)).natAbs + 1 : ℝ≥0) *
    (V.lipBound * (A * ⟨Real.exp ((p + 3) ^ 2), (Real.exp_pos _).le⟩))
  have hLip : letI := E.metricSpace
      LipschitzWith B (M.dilationObservable (q : ℚ) E hEL (q ^ (s + 1)) ε
        (V.observable a₀) (fun j => V.observable (a j))) :=
    M.dilationObservable_lipschitz (q : ℚ) E hEL hp hD hE hheight
      (q ^ (s + 1)) ε (V.observable a₀) (fun j => V.observable (a j)) V.lipBound A
      (V.norm a₀) (fun j => V.norm (a j)) (V.lipschitz a₀) (fun j => V.lipschitz (a j)) hε
  obtain ⟨T, hTn, hTl, hTzero, hTe⟩ := M.exists_dilation_niltest_of_data q hs E hEF hEL Q hQF hQL
    (one_le_ceil_exp p) (fun j k => rationalHeightLE_ceil_exp (hq j k))
    (fun j k l => rationalHeightLE_ceil_exp (hQ.2.2.1 j k l)) V g ε γ hγ hfactor a₀ a B hLip
  have hB : (B : ℝ) ≤ Real.exp (DilationBudget.reconstruction (s + 1) q p) := by
    change (((q ^ (s + 1)).natAbs : ℝ) + 1) *
      (V.lipBound * (A * Real.exp ((p + 3) ^ 2))) ≤ _
    exact DilationBudget.observable_bound (s + 1) q hp V.lipBound A V.lip_bound hA
  exact ⟨T, hTn, DilationBudget.niltest_complexity Q T (s + 1) q r H B hp hQ hE.1
    (ceil_exp_le_exp_add_one hp) hB hTn hTl, hTzero, hTe⟩

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeMultidegreeDilation
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open Module
open scoped TensorProduct BigOperators NNReal

theorem exists_controlled_dilation_family (s : ℕ) (q : ℤ) :
    ∃ Z : ℕ, 2 ≤ Z ∧ ∀ {σ I : Type*} {L : Type}
      [Fintype σ] [DecidableEq σ] [Fintype I] [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {t d : ℕ} {bound : σ → ℕ} (D : RationalFilteredNilmanifold L t d)
      (M : D.MultidegreeStructure bound) (_hs : ∑ j, bound j = t) (_ht : t = s + 1)
      {p : ℝ}, M.ComplexityLE p →
      ∀ (V : D.UnitVerticalObservable (M.realSubgroup bound) I p)
        (g : M.filtration.realification.PolynomialOrbit),
      ∃ R : NativeIntegerModelFamily (fun _ : σ => 1) s ((p + Z) ^ Z)
        (dilationTensorCrossProduct
          (fun j y => V.observable j
            (QuotientGroup.mk (M.filtration.realification.polynomialOrbitEval y g))) q t),
        R.dim ≤ 2 * d := by
  obtain ⟨C, _, hnormal⟩ := exists_controlled_group_normalization (s + 1)
  obtain ⟨Z, hZ, hbudget⟩ := DilationBudget.exists_full_bound (s + 1) q C
    (MultilinearityBudget.reconstructionExponent s)
  refine ⟨Z, hZ, ?_⟩
  intro σ I L _ _ _ _ _ _ _ _ _ t d bound D M hs ht p hM V g
  subst ht
  classical
  have hp : 0 ≤ p := (Nat.cast_nonneg d).trans hM.1.1
  have hshift := DilationBudget.shift_bounds q hp
  have hA := DilationBudget.ambient_bounds (s + 1) q hp
  have hQbound := DilationBudget.quotient_bounds (s + 1) q hp
  have hB := DilationBudget.common_bounds (s + 1) q C hp
  obtain ⟨E, hEF, hEL, hE, hdim, he⟩ := M.exists_dilationPair_model (q : ℚ)
    (hM.mono M hshift.2.1) hshift.2.2
  have hE' := hE.mono E hA.2.2.1
  obtain ⟨n, hn, Q, hQF, hQL, hQ, hq, _⟩ := E.exists_controlled_top_quotient hA.1 hE'
  obtain ⟨ε, γ, A, hγ, hfactor, _, hAnorm, hε⟩ := hnormal D p hp hM.1
    (M.filtration.realification.polynomialOrbitEval 0 g)
  let K := M.filtration.ordinary.dilationPairSubalgebra (q : ℚ)
  let J := K ⧸ E.filtration.layerIdeal (s + 1)
  let := moduleTopology ℝ (ℝ ⊗[ℚ] K)
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] K) := IsModuleTopology.topologicalAddGroup ℝ _
  let : T2Space (ℝ ⊗[ℚ] K) := realification_moduleTopology_t2 E.basis
  let := moduleTopology ℝ (ℝ ⊗[ℚ] J)
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] J) := IsModuleTopology.topologicalAddGroup ℝ _
  let : T2Space (ℝ ⊗[ℚ] J) := realification_moduleTopology_t2 Q.basis
  have he' (j : Fin 2) (a) (k) : rationalLogHeight
      (D.basis.repr (M.filtration.ordinary.dilationPairProjection (q : ℚ) j (E.basis a)) k) ≤
        DilationBudget.common (s + 1) q C p := by
    fin_cases j
    · exact (he a k).1.trans (hA.2.2.2.trans hB.2.2.1)
    · exact (he a k).2.trans (hA.2.2.2.trans hB.2.2.1)
  have hall (a : I × (Fin (q ^ (s + 1)).natAbs → I)) := M.exists_prepared_dilation_niltest
    q hs E hEF hEL Q hQF hQL hB.1 (hM.1.mono D hB.2.1) (hE'.mono E hB.2.2.1) he'
    (hQ.mono Q hB.2.2.2.1)
    (fun j k => (hq k j).trans (hQbound.2.2.trans hB.2.2.2.1))
    (V.mono hB.2.1) g ε γ hγ hfactor A (hAnorm.trans (Real.exp_le_exp.mpr hB.2.2.2.2)) hε a.1 a.2
  choose T hnorm hcomplex hzero heval using hall
  refine ⟨{
    L := J
    dim := n
    model := Q
    test := T
    norm := fun a => (hnorm a).le
    complexity := fun a => (hcomplex a).mono (hbudget p hp).1
    normalized := hzero
    eval := heval }, hn.trans hdim⟩

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.BoundedRootDegreeEquivalence
namespace OAI

section

namespace Erdos3.NativeMultidegreeNilcharacter

open RationalFilteredNilmanifold.MultidegreeStructure
open scoped BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff

theorem exists_uniform_dilation_degree_equivalence (s : ℕ) (q : ℤ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ : Type*} [Fintype σ] [DecidableEq σ]
      (bound : σ → ℕ), (∑ j, bound j) = s + 1 →
      ∀ {p : ℝ} (W : NativeMultidegreeNilcharacter bound p),
      NativeIntegerVectorEquivalence s ((p + C) ^ C)
        (integerDilationVector W.eval q) (signedTensorVector W.eval (q ^ (s + 1))) := by
  obtain ⟨a, _, hfamily⟩ := exists_controlled_dilation_family s q
  let n := (q ^ (s + 1)).natAbs
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((X + Polynomial.C a) ^ a + Polynomial.C (n + 1) * X + 2)
  refine ⟨C, hC, ?_⟩
  intro σ _ _ bound hs p W
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  have hpow : 0 ≤ (p + a) ^ a := by positivity
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
  have hb : (p + a) ^ a + (n + 1 : ℝ) * p + 2 ≤ (p + C) ^ C := by
    simpa [X, Polynomial.eval₂_pow, Nat.cast_add] using hbudget p hp
  have hpr : p ≤ (p + C) ^ C := by nlinarith [mul_nonneg hn hp]
  have hnpr : (n : ℝ) * p ≤ (p + C) ^ C := by nlinarith
  have har : (p + a) ^ a ≤ (p + C) ^ C := by nlinarith [mul_nonneg hn hp]
  obtain ⟨R, _⟩ := hfamily W.model W.multi rfl hs W.complexity W.vertical W.orbit
  have R' : NativeIntegerModelFamily (fun _ : σ => 1) s ((p + a) ^ a)
      (dilationTensorCrossProduct W.eval q (s + 1)) := by
    exact hs ▸ R
  exact NativeIntegerVectorEquivalence.of_dilation_family W.eval q (s + 1) R'
    (by simpa only [Fintype.card_fin] using W.output_bound) hpr hnpr har

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

theorem exists_uniform_root_degree_equivalence (s q : ℕ) (hq : 0 < q) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ : Type*} [Fintype σ] [DecidableEq σ]
      (bound : σ → ℕ), (∑ j, bound j) = s + 1 →
      ∀ {p : ℝ} (W : NativeMultidegreeNilcharacter bound p),
      ∃ R : NativeMultidegreeNilcharacter bound ((p + C) ^ C),
        R.dim = W.dim ∧ NativeIntegerVectorEquivalence s ((p + C) ^ C)
          W.eval (tensorVector R.eval q) := by
  obtain ⟨a, _, hdilation⟩ := exists_uniform_dilation_degree_equivalence s (q : ℤ)
  let n := q ^ s
  let X : Polynomial ℕ := Polynomial.X
  let B := Polynomial.C (n + 1) * (X + 1)
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((X + Polynomial.C a) ^ a + Polynomial.C (q + 1) * B + X + 2)
  refine ⟨C, hC, ?_⟩
  intro σ _ _ bound hs p W
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  have hA : 0 ≤ (p + a) ^ a := by positivity
  have hB : 0 ≤ tensorPowerBudget n p := by unfold tensorPowerBudget; positivity
  have hqB : 0 ≤ (q : ℝ) * tensorPowerBudget n p := mul_nonneg (Nat.cast_nonneg _) hB
  have hb : (p + a) ^ a + (q + 1 : ℝ) * tensorPowerBudget n p + p + 2 ≤ (p + C) ^ C := by
    simpa [X, B, tensorPowerBudget, Polynomial.eval₂_pow, Nat.cast_add] using hbudget p hp
  have hpr : p ≤ (p + C) ^ C := by nlinarith
  have hBr : tensorPowerBudget n p ≤ (p + C) ^ C := by nlinarith
  have hqBr : (q : ℝ) * tensorPowerBudget n p ≤ (p + C) ^ C := by nlinarith
  have hAr : (p + a) ^ a ≤ (p + C) ^ C := by nlinarith
  let V := W.rationalDilation ((q : ℚ)⁻¹)
  let R₀ := V.tensorPower n
  let R := R₀.mono hBr
  have hscale : (q : ℚ)⁻¹ * ((q : ℤ) : ℚ) = 1 := by
    rw [Int.cast_natCast]
    exact inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hq.ne')
  have hleft (i : Fin W.outputDim) (x : σ → ℤ) :
      W.eval i x = integerDilationVector V.eval (q : ℤ) i x :=
    (W.rationalDilation_eval_rescaled _ _ hscale i x).symm
  have hpos : 1 ≤ s + 1 := by omega
  have hright (b : Fin q → Fin R.outputDim) (x : σ → ℤ) :
      tensorVector R.eval q b x =
        signedTensorVector V.eval ((q : ℤ) ^ (s + 1))
          (rootTensorIndex W.outputDim q (s + 1) hpos b) x := by
    change tensorVector (V.tensorPower n).eval q b x = _
    exact V.tensorPower_tensor_eval q (s + 1) hpos b x
  have hdim : (Fintype.card (Fin q → Fin R.outputDim) : ℝ) ≤ Real.exp ((p + C) ^ C) := by
    simp only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
    have hroot : (R.outputDim : ℝ) ≤ Real.exp (tensorPowerBudget n p) := R₀.output_bound
    calc
      _ ≤ Real.exp (tensorPowerBudget n p) ^ q := pow_le_pow_left₀ (Nat.cast_nonneg _) hroot _
      _ = Real.exp ((q : ℝ) * tensorPowerBudget n p) := (Real.exp_nat_mul _ _).symm
      _ ≤ Real.exp ((p + C) ^ C) := Real.exp_le_exp.mpr hqBr
  refine ⟨R, rfl, ?_⟩
  exact (hdilation bound hs V).of_coordinate_maps W.eval (tensorVector R.eval q) id
    (rootTensorIndex W.outputDim q (s + 1) hpos) hleft hright
    (by simpa only [Fintype.card_fin] using W.output_bound.trans (Real.exp_le_exp.mpr hpr)) hdim hAr

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

theorem exists_bounded_root_degree_equivalence (s Q : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {q : ℕ}, 0 < q → q ≤ Q →
      ∀ {σ : Type} [Fintype σ] [DecidableEq σ]
        (bound : σ → ℕ), (∑ j, bound j) = s + 1 →
        ∀ {p : ℝ} (W : NativeMultidegreeNilcharacter bound p),
        ∃ R : NativeMultidegreeNilcharacter bound ((p + C) ^ C),
          R.dim = W.dim ∧ NativeIntegerVectorEquivalence s ((p + C) ^ C)
            W.eval (tensorVector R.eval q) := by
  classical
  let a : Fin Q → ℕ := fun i => Classical.choose
    (exists_uniform_root_degree_equivalence.{0} s (i.val + 1) (by omega))
  let C := 2 + ∑ i, a i
  refine ⟨C, by dsimp [C]; omega, ?_⟩
  intro q hq hqQ σ _ _ bound hs p W
  let i : Fin Q := ⟨q - 1, by omega⟩
  have hi : i.val + 1 = q := by dsimp [i]; omega
  have ha : 2 ≤ a i := (Classical.choose_spec
    (exists_uniform_root_degree_equivalence.{0} s (i.val + 1) (by omega))).1
  have hroot : ∀ {τ : Type} [Fintype τ] [DecidableEq τ]
      (b : τ → ℕ), (∑ j, b j) = s + 1 →
      ∀ {r : ℝ} (V : NativeMultidegreeNilcharacter b r),
      ∃ R : NativeMultidegreeNilcharacter b ((r + a i) ^ a i),
        R.dim = V.dim ∧ NativeIntegerVectorEquivalence s ((r + a i) ^ a i)
          V.eval (tensorVector R.eval (i.val + 1)) :=
    (Classical.choose_spec
      (exists_uniform_root_degree_equivalence.{0} s (i.val + 1) (by omega))).2
  rw [hi] at hroot
  obtain ⟨R, hdim, hE⟩ := hroot bound hs W
  have hsum : a i ≤ ∑ j, a j :=
    Finset.single_le_sum (fun j _ => Nat.zero_le (a j)) (Finset.mem_univ i)
  have haC : a i ≤ C := by dsimp [C]; omega
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  have hbudget := shifted_power_self_mono hp (by omega : 1 ≤ a i) haC
  exact ⟨R.mono hbudget, hdim, hE.mono hbudget⟩

end Erdos3.NativeMultidegreeNilcharacter

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CubicAntisymmetricTransfer
namespace OAI

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

theorem exists_symmetric_multilinearization (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ : Type} [Fintype σ] (bound : σ → ℕ),
      (∑ i, bound i) = s + 1 → ∀ {p : ℝ} (W : NativeMultidegreeNilcharacter bound p),
      ∃ V : NativeMultidegreeNilcharacter (fun _ : ReplicatedIndex bound => 1) ((p + C) ^ C),
        V.dim ≤ 2 ^ (s + 1) * W.dim ∧
        (∀ (e : ReplicatedPermutation bound) k x,
          V.eval k (fun j => x ((replicatedPermutation bound e).symm j)) = V.eval k x) ∧
        NativeIntegerVectorEquivalence s ((p + C) ^ C)
          W.eval (fun k x => V.eval k (fun j => x j.1)) := by
  obtain ⟨a, _, hroot⟩ := exists_bounded_root_degree_equivalence s (s + 1).factorial
  obtain ⟨b, _, hdiagonal⟩ := exists_factorial_diagonal s
  obtain ⟨c, _, htrans⟩ := NativeIntegerVectorEquivalence.exists_trans_budget
  let X : Polynomial ℕ := Polynomial.X
  let A₀ := (X + Polynomial.C a) ^ a
  let B₀ := (A₀ + Polynomial.C b) ^ b
  let R₀ := A₀ + B₀
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (B₀ + (R₀ + Polynomial.C c) ^ c)
  refine ⟨C, hC, ?_⟩
  intro σ _ bound hs p W
  classical
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  have hq : multidegreeFactorial bound ≤ (s + 1).factorial := by
    simpa only [hs] using multidegreeFactorial_le_total bound
  obtain ⟨R, hRdim, hER⟩ := hroot (multidegreeFactorial_pos bound) hq bound hs W
  obtain ⟨V, hVdim, hsymm, hEV⟩ := hdiagonal bound hs R
  let A := (p + a) ^ a
  let B := (A + b) ^ b
  let r := A + B
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hr : 0 ≤ r := add_nonneg hA hB
  have hAr : A ≤ r := le_add_of_nonneg_right hB
  have hBr : B ≤ r := le_add_of_nonneg_left hA
  have hE := htrans hr (hER.mono hAr) (hEV.mono hBr)
    (tensorVector_unit R.eval R.unit_eval (multidegreeFactorial bound))
  have hb : B + (r + c) ^ c ≤ (p + C) ^ C := by
    simpa [X, A₀, B₀, R₀, A, B, r, Polynomial.eval₂_pow] using hbudget p hp
  have hc : 0 ≤ (r + c) ^ c := by positivity
  have hBC : B ≤ (p + C) ^ C := by linarith
  have hEC : (r + c) ^ c ≤ (p + C) ^ C := by linarith
  exact ⟨V.mono hBC, hRdim ▸ hVdim, hsymm, hE.mono hEC⟩

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

attribute [local instance] NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff
  NativeVectorCorrelation.lie NativeVectorCorrelation.algebra
  NativeVectorCorrelation.topology NativeVectorCorrelation.topologicalAdd
  NativeVectorCorrelation.continuousSMul NativeVectorCorrelation.hausdorff

theorem exists_multilinearized_correlation (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {r N : ℕ} [NeZero N] {p : ℝ} {f : ZMod N → ℂ}
      (W : NativeCorrelationStructure s r N p f),
      ∃ V : NativeMultidegreeNilcharacter
          (fun _ : ReplicatedIndex (mixedCorrelationDegree s) => 1) ((p + C) ^ C),
        V.dim ≤ 2 ^ (s + 1) * W.mixed.dim ∧
        (∀ (e : ReplicatedPermutation (mixedCorrelationDegree s)) k x,
          V.eval k (fun j => x ((replicatedPermutation (mixedCorrelationDegree s) e).symm j)) =
            V.eval k x) ∧
        ∃ E : NativeIntegerVectorEquivalence s ((p + C) ^ C)
            W.mixed.eval (fun k x => V.eval k (fun j => x j.1)),
          ∀ h : W.shifts,
            ∃ (k : Fin V.outputDim)
              (a : Fin (E.selectedExpansion (W.selectedWitness h).coordinate.1 k).count),
              Real.exp (-(p + 2 * (p + C) ^ C)) ≤
                ‖𝔼 x, multiplicativeDerivative f h.val x * star
                  (V.eval k (fun j => correlationInput (h.val.val : ℤ) (x.val : ℤ) j.1) *
                    W.family.evalCyclic N (W.selectedWitness h).coordinate.2 h.val x *
                    (W.selectedWitness h).test.evalCyclic N (fun _ => x) *
                    ((E.selectedExpansion (W.selectedWitness h).coordinate.1 k).test a).eval
                      (correlationInput (h.val.val : ℤ) (x.val : ℤ)))‖ := by
  obtain ⟨C, hC, hmulti⟩ := NativeMultidegreeNilcharacter.exists_symmetric_multilinearization s
  refine ⟨C, hC, ?_⟩
  intro r N _ p f W
  have hsum : (∑ i, mixedCorrelationDegree s i) = s + 1 := by
    rw [Fin.sum_univ_two]
    change 1 + s = s + 1
    omega
  obtain ⟨V, hdim, hsymm, E⟩ := hmulti (mixedCorrelationDegree s) hsum W.mixed
  exact ⟨V, hdim, hsymm, E, fun h => W.mixed_correlation_transfer E
    (fun x => V.unit_eval (fun j => x j.1)) h⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeMultilinearQuadruples
namespace OAI

section

namespace Erdos3

open scoped TensorProduct BigOperators

attribute [local instance] NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff
  NativeVectorCorrelation.lie NativeVectorCorrelation.algebra
  NativeVectorCorrelation.topology NativeVectorCorrelation.topologicalAdd
  NativeVectorCorrelation.continuousSMul NativeVectorCorrelation.hausdorff

theorem exists_fixed_multilinearized_correlation (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {r N : ℕ} [NeZero N] {p : ℝ} {f : ZMod N → ℂ}
      (W : NativeCorrelationStructure s r N p f),
      ∃ V : NativeMultidegreeNilcharacter
          (fun _ : ReplicatedIndex (mixedCorrelationDegree s) => 1) ((p + C) ^ C),
        V.dim ≤ 2 ^ (s + 1) * W.mixed.dim ∧
        (∀ (e : ReplicatedPermutation (mixedCorrelationDegree s)) k x,
          V.eval k (fun j => x ((replicatedPermutation (mixedCorrelationDegree s) e).symm j)) =
            V.eval k x) ∧
        ∃ E : NativeIntegerVectorEquivalence s ((p + C) ^ C)
            W.mixed.eval (fun k x => V.eval k (fun j => x j.1)),
          ∃ (j : Fin W.mixed.outputDim) (k : Fin V.outputDim)
            (a : Fin (E.selectedExpansion j k).count) (i : Fin W.family.outputDim)
            (H : Finset (ZMod N)), H ⊆ W.shifts ∧ H.Nonempty ∧
            Real.exp (-(3 * p + 2 * (p + C) ^ C)) * Fintype.card (ZMod N) ≤ (H.card : ℝ) ∧
            ∀ h ∈ H, ∃ hh : h ∈ W.shifts,
              (W.selectedWitness ⟨h, hh⟩).coordinate = (j, i) ∧
              Real.exp (-(p + 2 * (p + C) ^ C)) ≤
                ‖𝔼 x, multiplicativeDerivative f h x * star
                  (V.eval k (fun l => correlationInput (h.val : ℤ) (x.val : ℤ) l.1) *
                    W.family.evalCyclic N i h x *
                    (W.selectedWitness ⟨h, hh⟩).test.evalCyclic N (fun _ => x) *
                    ((E.selectedExpansion j k).test a).eval
                      (correlationInput (h.val : ℤ) (x.val : ℤ)))‖ := by
  obtain ⟨C, hC, htransfer⟩ := exists_multilinearized_correlation s
  refine ⟨C, hC, ?_⟩
  intro r N _ p f W
  obtain ⟨V, hdim, hsymm, E, _⟩ := htransfer W
  exact ⟨V, hdim, hsymm, E, W.exists_fixed_transferred_correlation E
    (fun x => V.unit_eval (fun j => x j.1))⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeAbsorbedIntervals
namespace OAI

section

namespace Erdos3.NativeMultilinearIntervalFamily

attribute [local instance] NativeVectorCorrelation.lie NativeVectorCorrelation.algebra
  NativeVectorCorrelation.topology NativeVectorCorrelation.topologicalAdd
  NativeVectorCorrelation.continuousSMul NativeVectorCorrelation.hausdorff

noncomputable def lowerProductExpansion {s r N : ℕ} [NeZero N] {p q : ℝ}
    {f : ZMod N → ℂ} {W : NativeCorrelationStructure s r N p f}
    (B : NativeMultilinearIntervalFamily W q) (t : B.quadruples) :
    NativeIntegerExpansion (fun _ : Unit => 1) (s - 1) (mixedErrorBudget (q + 2))
      (fun x => B.lowerProduct t (x ())) := by
  have hq : 0 ≤ q := (Nat.cast_nonneg B.mixed.dim).trans B.mixed.complexity.1.1
  let h : Fin 4 → B.shifts :=
    ![⟨t.val.2.1, (B.interval t).first_mem⟩,
      ⟨t.val.2.1 - t.val.1, (B.interval t).second_mem⟩,
      ⟨t.val.2.2, (B.interval t).third_mem⟩,
      ⟨t.val.2.2 - t.val.1, (B.interval t).fourth_mem⟩]
  let v (i : Fin 4) := B.lower.integerLower (h i)
  let E (i : Fin 4) : NativeIntegerExpansion (fun _ : Unit => 1) (s - 1) (q + 2)
      (fun x => v i (x ())) :=
    NativeIntegerExpansion.ofTest (B.lower (h i)).test
      ((B.lower (h i)).complexity.mono (by linarith)) (fun _ => rfl)
  exact NativeIntegerExpansion.fourPoint v E (by linarith) (B.delta t)

end Erdos3.NativeMultilinearIntervalFamily

end

section

namespace Erdos3

namespace NativeMultilinearIntervalFamily

theorem rankProduct_norm {s r N : ℕ} [NeZero N] {p q : ℝ} {f : ZMod N → ℂ}
    {W : NativeCorrelationStructure s r N p f} (B : NativeMultilinearIntervalFamily W q)
    (t : B.quadruples) (n : ℤ) : ‖B.rankProduct t n‖ ≤ 1 := by
  simp only [rankProduct, fourPointProduct, norm_mul, norm_star]
  calc
    _ ≤ (1 : ℝ) * 1 * 1 * 1 := by
      gcongr <;> exact W.family.norm_eval _ _ _
    _ = 1 := by norm_num

end NativeMultilinearIntervalFamily

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.NativeCoefficientKernel
namespace OAI

section

namespace Erdos3.NativeRankInterval

open Module RationalFilteredNilmanifold
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {t : ZMod N × ZMod N × ZMod N} {branch : Bool}
  (I : NativeRankInterval W out H t branch p q) (i : Fin I.expansion.count)

theorem real_rankProjection_grid (l : ℕ)
    (x : ℝ ⊗[ℚ] (∀ k : Option (Fin 4), optionLieSpace (I.expansion.L i) (fun _ : Fin 4 => W.L) k))
    (hx : (fun j => ((pi (I.productModels i)).basis.baseChange ℝ).repr x j) ∈ realDenominatorGrid l) :
    (fun j => (W.fourRankBasis.baseChange ℝ).repr
      ((I.rankProjection i).toLinearMap.baseChange ℝ x) j) ∈ realDenominatorGrid l := by
  obtain ⟨a, ha⟩ := hx
  refine ⟨fun j => a ((Fintype.equivFin (Σ k : Option (Fin 4),
    Fin (optionDimension (I.expansion.dim i) (fun _ : Fin 4 => W.dim) k)))
      ⟨some ((![1, 2, 0, 3] : Fin 4 → Fin 4) j.1), j.2⟩), ?_⟩
  funext j
  exact (congrFun ha _).trans
    (congrArg (fun y : ℝ => (l : ℝ) * y) (I.real_rankProjection_coordinates i x j)).symm

end Erdos3.NativeRankInterval

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.CommonRankCoefficientCorrections
namespace OAI

section

namespace Erdos3

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

namespace NativeRankRelation

variable {s r N : ℕ} [NeZero N] {b p q : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)}

namespace CommonData

variable {R : NativeRankRelation W out H p q} {P Q : ℝ} (D : R.CommonData P)

theorem spaces_mem_candidates (hP : 0 ≤ P) (d : Fin (s + 1)) :
    D.spaces d ∈ heightBoundedSubspaces W.fourRankBasis (Fintype.card (Σ _ : Fin 4, Fin W.dim))
      ⌈Real.exp (refiltrationCoordinateBudget P)⌉₊ := by
  obtain ⟨t, ht⟩ := D.nonempty
  rw [← D.projection t ht d]
  exact (D.witness t ht).projection_mem_candidates hP d.val

end CommonData

end NativeRankRelation

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.CommonNativeCoordinateCorrections
namespace OAI

section

namespace Erdos3.NativeRankRelation.CommonData

open Module RationalFilteredNilmanifold

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {κ : Type*} [Fintype κ] {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)

noncomputable def coordinateSpace (d : Fin (s + 1))
    (f : Basis κ ℚ (W.L ⧸ W.rank.filtration.layer d.val 2)) :
    Submodule ℚ (Fin 4 → κ → ℚ) :=
  (D.horizontal d).map (W.rank.filtration.fourHorizontalCoordinates d.val f)

theorem coordinateSpace_eq_map (d : Fin (s + 1))
    (f : Basis κ ℚ (W.L ⧸ W.rank.filtration.layer d.val 2)) :
    D.coordinateSpace d f = (D.spaces d).map (W.rank.filtration.fourAmbientCoordinates d.val f) :=
  W.rank.filtration.horizontalImage_coordinates d.val f (D.spaces d) (D.spaces_le_fourHorizontalLayer d)

theorem exists_coordinate_generators (hP : 0 ≤ P) (d : Fin (s + 1))
    (f : Basis κ ℚ (W.L ⧸ W.rank.filtration.layer d.val 2)) {K : ℕ}
    (hf : ∀ i j, RationalHeightLE
      (f.repr ((W.rank.filtration.layer d.val 2).mkQ (W.model.basis j)) i) K) :
    ∃ v : Fin (Fintype.card (Σ _ : Fin 4, Fin W.dim)) → (Fin 4 → κ → ℚ),
      Submodule.span ℚ (Set.range v) = D.coordinateSpace d f ∧
      ∀ a k i, RationalHeightLE (v a k i)
        ((W.dim + 1) * (⌈Real.exp (refiltrationCoordinateBudget P)⌉₊ * K) ^ W.dim) := by
  obtain ⟨v, hspan, hv⟩ := (mem_heightBoundedSubspaces W.fourRankBasis _ _ _).mp
    (D.spaces_mem_candidates hP d)
  let φ := W.rank.filtration.fourAmbientCoordinates d.val f
  refine ⟨fun a => φ (v a), ?_, ?_⟩
  · rw [D.coordinateSpace_eq_map, ← hspan, Submodule.map_span, ← Set.range_comp]
    rfl
  · intro a k i
    have hv' (j : Fin 4) (l : Fin W.dim) :
        RationalHeightLE (W.model.basis.repr (v a j) l)
          ⌈Real.exp (refiltrationCoordinateBudget P)⌉₊ := by
      simpa only [NativeDegreeRankFamily.fourRankBasis, Pi.basis_repr] using hv a ⟨j, l⟩
    simpa only [Fintype.card_fin] using W.rank.filtration.fourAmbientCoordinates_height
      d.val f W.model.basis hf (v a) hv' k i

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3.NativeRankRelation.CommonData

open Module RationalFilteredNilmanifold

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q}

theorem exists_bounded_coordinate_generators (D : R.CommonData P) (hP : 0 ≤ P) (hbP : b ≤ P)
    (d : Fin (s + 1)) (hd : 1 ≤ d.val) :
    ∃ m : ℕ, m ≤ W.dim ∧ ∃ f : Basis (Fin m) ℚ (W.L ⧸ W.rank.filtration.layer d.val 2),
      (∀ i j, rationalLogHeight (f.repr ((W.rank.filtration.layer d.val 2).mkQ (W.model.basis j)) i) ≤
        (P + 3) ^ 7) ∧
      ∃ v : Fin (Fintype.card (Σ _ : Fin 4, Fin W.dim)) → (Fin 4 → Fin m → ℚ),
        Submodule.span ℚ (Set.range v) = D.coordinateSpace d f ∧
        ∀ a k i, rationalLogHeight (v a k i) ≤ horizontalCoordinateBudget P := by
  obtain ⟨K, hK, hKp, m, hm, f, hf⟩ :=
    W.rank.exists_horizontal_ambient_basis d hd hP (W.complexity.mono W.rank hbP)
  obtain ⟨v, hv, hheight⟩ := D.exists_coordinate_generators hP d f hf
  have hdim : (W.dim : ℝ) ≤ P := W.complexity.1.1.trans hbP
  have hbound := horizontalCoordinateHeight_bound hP W.dim
    ⌈Real.exp (refiltrationCoordinateBudget P)⌉₊ K hdim
    (ceil_exp_le_exp_add_one (refiltrationCoordinateBudget_nonneg hP)) hKp
  refine ⟨m, hm, f, (fun i j => rationalLogHeight_le_of_height (hf i j) hKp), v, hv, ?_⟩
  intro a k i
  exact rationalLogHeight_le_of_height (hheight a k i) hbound

end Erdos3.NativeRankRelation.CommonData

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.CommonRealDependentProjection
namespace OAI

section

namespace Erdos3.NativeRankRelation.CommonData

open Module RationalFilteredNilmanifold

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {κ : Type*} [Fintype κ] {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)
  (d : Fin (s + 1)) (f : Basis κ ℚ (W.L ⧸ W.rank.filtration.layer d.val 2))

theorem coordinateSpace_first :
    fourFirstProjection (D.coordinateSpace d f) =
      (fourFirstProjection (D.horizontal d)).map (W.rank.filtration.higherHorizontalCoordinates d.val f) :=
  fourFirstProjection_map (W.rank.filtration.higherHorizontalCoordinates d.val f) (D.horizontal d)

theorem coordinateSpace_dependent :
    fourDependentProjection (D.coordinateSpace d f) =
      (fourDependentProjection (D.horizontal d)).map
        (W.rank.filtration.higherHorizontalCoordinates d.val f) :=
  fourDependentProjection_map (W.rank.filtration.higherHorizontalCoordinates d.val f)
    (W.rank.filtration.higherHorizontalCoordinates_injective d.val f) (D.horizontal d)

end Erdos3.NativeRankRelation.CommonData

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CommonFreeSunflower
namespace OAI

section

namespace Erdos3.NativeRankRelation.CommonData

open Module VectorPolynomial
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)

theorem native_coefficient_mem_common {σ ι : Type*} (hs : 1 ≤ s)
    (c : Basis ι ℚ W.L) (τ : ι → ℕ)
    (hF : ∀ j, W.rank.filtration.associatedDegree.layer j =
      Submodule.span ℚ (c '' {i | j ≤ τ i}))
    (w : σ → ℕ) (α : σ →₀ ℕ) (hα : Finsupp.weight w α ≤ s)
    (g : W.model.filtration.realification.PolynomialOrbit w) :
    coefficients g.log α ∈
        (D.commonCoefficientSpace ⟨Finsupp.weight w α, Nat.lt_succ_of_le hα⟩).baseChange ℝ ↔
      Multiplicative.toAdd (W.rank.filtration.nativeHorizontalCoefficientHom
        hs c τ hF w α (W.rank.orbitEquiv w g)) ∈
        (fourFirstProjection (D.horizontal
          ⟨Finsupp.weight w α, Nat.lt_succ_of_le hα⟩)).baseChange ℝ := by
  unfold commonCoefficientSpace
  rw [← W.rank.orbitEquiv_log w g]
  exact W.rank.filtration.native_coefficient_mem_horizontalPreimage hs c τ hF w α
    (W.rank.orbitEquiv w g) (fourFirstProjection (D.horizontal
      ⟨Finsupp.weight w α, Nat.lt_succ_of_le hα⟩))

theorem native_coefficient_mem_dependent {σ ι : Type*} (hs : 1 ≤ s)
    (c : Basis ι ℚ W.L) (τ : ι → ℕ)
    (hF : ∀ j, W.rank.filtration.associatedDegree.layer j =
      Submodule.span ℚ (c '' {i | j ≤ τ i}))
    (w : σ → ℕ) (α : σ →₀ ℕ) (hα : Finsupp.weight w α ≤ s)
    (g : W.model.filtration.realification.PolynomialOrbit w) :
    coefficients g.log α ∈
        (D.dependentCoefficientSpace ⟨Finsupp.weight w α, Nat.lt_succ_of_le hα⟩).baseChange ℝ ↔
      Multiplicative.toAdd (W.rank.filtration.nativeHorizontalCoefficientHom
        hs c τ hF w α (W.rank.orbitEquiv w g)) ∈
        (fourDependentProjection (D.horizontal
          ⟨Finsupp.weight w α, Nat.lt_succ_of_le hα⟩)).baseChange ℝ := by
  unfold dependentCoefficientSpace
  rw [← W.rank.orbitEquiv_log w g]
  exact W.rank.filtration.native_coefficient_mem_horizontalPreimage hs c τ hF w α
    (W.rank.orbitEquiv w g) (fourDependentProjection (D.horizontal
      ⟨Finsupp.weight w α, Nat.lt_succ_of_le hα⟩))

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3.NativeRankRelation.CommonData

open Module
open scoped BigOperators

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)

def CoefficientBases.mono {Q Q' : ℝ} (B : D.CoefficientBases Q) (h : Q ≤ Q') :
    D.CoefficientBases Q' where
  common := B.common
  dependent := B.dependent
  common_height d i j := (B.common_height d i j).trans h
  dependent_height d i j := (B.dependent_height d i j).trans h

theorem coefficientAlphabet_card : Fintype.card D.CoefficientAlphabet ≤ 2 * s * W.dim := by
  classical
  let : FiniteDimensional ℚ W.L := W.model.basis.finiteDimensional_of_finite
  have hdim (U : Submodule ℚ W.L) : finrank ℚ U ≤ W.dim := by
    simpa only [finrank_eq_card_basis W.model.basis, Fintype.card_fin] using U.finrank_le
  change Fintype.card
    ((Σ d : Fin s, Fin (finrank ℚ (D.commonCoefficientSpace ⟨d.val + 1, by omega⟩))) ⊕
      (Σ d : Fin s, Fin (finrank ℚ (D.dependentCoefficientSpace ⟨d.val + 1, by omega⟩)))) ≤ _
  simp only [Fintype.card_sum, Fintype.card_sigma, Fintype.card_fin]
  calc
    _ ≤ (∑ _ : Fin s, W.dim) + ∑ _ : Fin s, W.dim :=
      Nat.add_le_add (Finset.sum_le_sum (fun _ _ => hdim _))
        (Finset.sum_le_sum (fun _ _ => hdim _))
    _ = 2 * s * W.dim := by simp; ring

theorem CoefficientBases.generator_height {Q : ℝ} (B : D.CoefficientBases Q)
    (x : D.CoefficientAlphabet) (i : Fin W.dim) :
    rationalLogHeight (W.model.basis.repr (B.generator D x) i) ≤ Q := by
  cases x with
  | inl x => exact B.common_height x.1 x.2 i
  | inr x => exact B.dependent_height x.1 x.2 i

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3.NativeRankRelation.CommonData

open Module

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)

theorem coefficientFreeGenerator_mem_layer (x : D.CoefficientAlphabet) :
    D.coefficientFreeGenerator x ∈ D.coefficientFreeFiltration.layer (D.coefficientWeight x) 1 :=
  FreeDegreeRankLieAlgebra.of_mem_layer _ _ _ _ _ W.rank.filtration.rank_le_degree x

theorem commonFreeSpan_le_layer (d : Fin s) :
    D.commonFreeSpan d ≤ D.coefficientFreeFiltration.layer (d.val + 1) 1 := by
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  exact D.coefficientFreeGenerator_mem_layer (Sum.inl ⟨d, i⟩)

theorem dependentFreeSpan_le_layer (d : Fin s) :
    D.dependentFreeSpan d ≤ D.coefficientFreeFiltration.layer (d.val + 1) 1 := by
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  exact D.coefficientFreeGenerator_mem_layer (Sum.inr ⟨d, i⟩)

variable {Q : ℝ} (B : D.CoefficientBases Q)

noncomputable def CoefficientBases.commonFreeLift (d : Fin s) :
    D.commonCoefficientSpace ⟨d.val + 1, by omega⟩ →ₗ[ℚ] D.CoefficientFreeLieAlgebra :=
  (B.common d).constr ℚ (fun i => D.coefficientFreeGenerator (Sum.inl ⟨d, i⟩))

noncomputable def CoefficientBases.dependentFreeLift (d : Fin s) :
    D.dependentCoefficientSpace ⟨d.val + 1, by omega⟩ →ₗ[ℚ] D.CoefficientFreeLieAlgebra :=
  (B.dependent d).constr ℚ (fun i => D.coefficientFreeGenerator (Sum.inr ⟨d, i⟩))

theorem CoefficientBases.commonFreeLift_range (d : Fin s) :
    LinearMap.range (B.commonFreeLift D d) = D.commonFreeSpan d :=
  (B.common d).constr_range ℚ

theorem CoefficientBases.dependentFreeLift_range (d : Fin s) :
    LinearMap.range (B.dependentFreeLift D d) = D.dependentFreeSpan d :=
  (B.dependent d).constr_range ℚ

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3.NativeRankRelation.CommonData

open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)
  {Q : ℝ} (B : D.CoefficientBases Q)

noncomputable def CoefficientBases.realCommonFreeLift (d : Fin s) :
    (D.commonCoefficientSpace ⟨d.val + 1, by omega⟩).baseChange ℝ →ₗ[ℝ]
      ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra :=
  ((B.commonFreeLift D d).baseChange ℝ).comp
    (realificationSubmoduleEquiv (D.commonCoefficientSpace ⟨d.val + 1, by omega⟩)).symm.toLinearMap

noncomputable def CoefficientBases.realDependentFreeLift (d : Fin s) :
    (D.dependentCoefficientSpace ⟨d.val + 1, by omega⟩).baseChange ℝ →ₗ[ℝ]
      ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra :=
  ((B.dependentFreeLift D d).baseChange ℝ).comp
    (realificationSubmoduleEquiv (D.dependentCoefficientSpace ⟨d.val + 1, by omega⟩)).symm.toLinearMap

theorem CoefficientBases.realCommonFreeLift_baseChange (d : Fin s)
    (x : ℝ ⊗[ℚ] D.commonCoefficientSpace ⟨d.val + 1, by omega⟩) :
    B.realCommonFreeLift D d (realificationSubmoduleEquiv _ x) =
      (B.commonFreeLift D d).baseChange ℝ x :=
  congrArg ((B.commonFreeLift D d).baseChange ℝ)
    ((realificationSubmoduleEquiv _).symm_apply_apply x)

theorem CoefficientBases.realDependentFreeLift_baseChange (d : Fin s)
    (x : ℝ ⊗[ℚ] D.dependentCoefficientSpace ⟨d.val + 1, by omega⟩) :
    B.realDependentFreeLift D d (realificationSubmoduleEquiv _ x) =
      (B.dependentFreeLift D d).baseChange ℝ x :=
  congrArg ((B.dependentFreeLift D d).baseChange ℝ)
    ((realificationSubmoduleEquiv _).symm_apply_apply x)

theorem CoefficientBases.realCommonFreeLift_mem (d : Fin s)
    (x : (D.commonCoefficientSpace ⟨d.val + 1, by omega⟩).baseChange ℝ) :
    B.realCommonFreeLift D d x ∈ (D.commonFreeSpan d).baseChange ℝ := by
  obtain ⟨v, rfl⟩ := (realificationSubmoduleEquiv _).surjective x
  rw [B.realCommonFreeLift_baseChange]
  induction v using TensorProduct.induction_on with
  | zero => simp
  | tmul a v =>
    rw [LinearMap.baseChange_tmul]
    exact Submodule.tmul_mem_baseChange_of_mem a
      ((B.commonFreeLift_range D d).le ⟨v, rfl⟩)
  | add v w hv hw => simpa only [map_add] using Submodule.add_mem _ hv hw

theorem CoefficientBases.realDependentFreeLift_mem (d : Fin s)
    (x : (D.dependentCoefficientSpace ⟨d.val + 1, by omega⟩).baseChange ℝ) :
    B.realDependentFreeLift D d x ∈ (D.dependentFreeSpan d).baseChange ℝ := by
  obtain ⟨v, rfl⟩ := (realificationSubmoduleEquiv _).surjective x
  rw [B.realDependentFreeLift_baseChange]
  induction v using TensorProduct.induction_on with
  | zero => simp
  | tmul a v =>
    rw [LinearMap.baseChange_tmul]
    exact Submodule.tmul_mem_baseChange_of_mem a
      ((B.dependentFreeLift_range D d).le ⟨v, rfl⟩)
  | add v w hv hw => simpa only [map_add] using Submodule.add_mem _ hv hw

end Erdos3.NativeRankRelation.CommonData

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.NativeFreePolynomialLifts
namespace OAI

section

namespace Erdos3.NativeRankRelation.CommonData

open VectorPolynomial
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)
  {Q : ℝ} (B : D.CoefficientBases Q)

noncomputable def coefficientFreeRealFiltration :
    NilpotentLieFiltration (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra) s :=
  D.coefficientFreeFiltration.associatedDegree.realification

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3.NativeRankRelation.CommonData

open VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N n : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)
  (F : RationalFilteredNilmanifold D.CoefficientFreeLieAlgebra s n)
  (T : F.DegreeRankStructure r) (hT : T.filtration = D.coefficientFreeFiltration)

include T hT

theorem coefficientFreeRealFiltration_eq_native :
    D.coefficientFreeRealFiltration = F.filtration.realification := by
  apply congrArg NilpotentLieFiltration.realification
  exact (congrArg DegreeRankLieFiltration.associatedDegree hT).symm.trans T.associated

end Erdos3.NativeRankRelation.CommonData

end

end OAI
end


