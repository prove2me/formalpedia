-- Prove2me | Definitions.Def_OAIE3v2B190
-- name    : OAIE3v2B190
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T11:53:08.611869+00:00
-- url     : https://prove2.me/theorems/4312db99-6d18-46c8-87cf-9b0741c95efb
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 193 of 311
-- statement:
--   Definitions bundle 193 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B161`, `OAIE3v2B162`, `OAIE3v2B164`, `OAIE3v2B167`, `OAIE3v2B171`, `OAIE3v2B172`, `OAIE3v2B173` of this split.
--
--   Modules: `Dynamics/ActualPathCurrentGradeReset.lean`, `Estimates/AllocatedCandidateCommonFastGeometry.lean`, `Estimates/CommonRefilteredMappedOrbitFactors.lean`, `Estimates/ControlledPrescribedMarkedNativeFactorization.lean`, `Estimates/FullMarkedNativeFactorization.lean`, `Estimates/GlobalMarkedOuterNormalization.lean`, `Estimates/HomogeneousComponentTopSubstitution.lean`, `Estimates/HomogeneousQuotientSymbolLiftBounds.lean`, `Estimates/HomogeneousRealSymbolPullback.lean`, `Estimates/NativeFrozenMarkedLocalMark.lean`, `Estimates/PreparedLayerFreezing.lean`, `Estimates/RealSymbolGradeQuotientSplitting.lean`, `Geometry/AllocatedRecoveredNormalizedTopChart.lean`, `Geometry/CommonRefilteredFactorsSymbolTransport.lean`, `Geometry/GlobalChartNativeFactorization.lean`, `Geometry/GlobalMarkedChartwiseNormalization.lean`, `Geometry/RestrictedChartPrefixControl.lean`, `Geometry/SymbolCoordinateFreezeBounds.lean`, `Linear/ActualMarkedSlowKernelCells.lean`, `Linear/ActualOrdinaryPointwiseSpanning.lean`, `Linear/ControlledMarkedKernelNormalization.lean`, `Nilpotent/AllocatedKeptCommonCurrentGradeLocalNiltest.lean`, `Nilpotent/LocalMajorDenseSliceNiltest.lean`, `Polynomial/BufferedSampledCurrentGradePhase.lean`, `Polynomial/MarkedPolynomialSectionSlow.lean`, `Polynomial/NativeMarkedPolynomialFreezing.lean`, `Polynomial/RefilteredPolynomialProjection.lean`, `Sampling/RationalHomogeneousSymbolPullbackGrid.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B161
import Definitions.Def_OAIE3v2B162
import Definitions.Def_OAIE3v2B164
import Definitions.Def_OAIE3v2B167
import Definitions.Def_OAIE3v2B171
import Definitions.Def_OAIE3v2B172
import Definitions.Def_OAIE3v2B173

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.LocalMajorDenseSliceNiltest
namespace OAI

section

namespace Erdos3.OrdinaryPolynomialPhase

open _root_.MvPolynomial PolynomialTranslationLie
open scoped TensorProduct NNReal

variable {s : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] weightedSubalgebra weight s)]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] weightedSubalgebra weight s)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] weightedSubalgebra weight s)]
    [T2Space (ℝ ⊗[ℚ] weightedSubalgebra weight s)]

attribute [local instance] OAI.Erdos3.OrdinaryPolynomialPhase.phaseBasisFintype
theorem exists_niltest {U : Type*} (hs : 0 < s)
    (P : MvPolynomial U ℝ) (hP : P.totalDegree ≤ s) :
    ∃ T : (nilmanifold s).Niltest (fun _ : U => 1),
      T.normBound = 1 ∧ T.ComplexityLE (budget s) ∧
      ∀ u : U → ℝ, T.evalReal u = (Real.fourierChar (eval u P) : ℂ) := by
  obtain ⟨q, hq⟩ := exists_phase_orbit s hs P hP
  let Ψ := localTentKernel 0 8 (by decide)
  let T := weightedTranslationBufferedNiltest weight s weight_pos (weight_le s)
    (fun _ : U => 1) hs Ψ 0 0 (by simp) (by simp [realPolynomialMass]) q
  refine ⟨T, rfl, ?_, ?_⟩
  · apply weightedTranslationBufferedNiltest_complexity
    · exact nilmanifold_geometry s
    · exact le_max_right _ _
  · intro u
    change bufferedTranslationPhase Ψ 0 (bchRealTranslationHom weight s (weight_le s)
      ((nilmanifold s).filtration.realification.polynomialOrbitRealEval
        (fun _ : U => 1) u q)) = _
    rw [hq u]
    rw [bufferedTranslationPhase_eq_chart Ψ 0 _ 0 (fun i => Fin.elim0 i)]
    have hd : ∀ x y : Fin 0 → ℝ, dist x y = 0 := by
      intro x y
      rw [Subsingleton.elim x y, dist_self]
    simp [bufferedTranslationTerm, translationPhaseArgument, Ψ, localTentKernel, hd]

theorem exists_niltest_of_degree {U : Type*}
    (P : MvPolynomial U ℝ) (hP : P.totalDegree ≤ s) :
    ∃ T : (nilmanifold s).Niltest (fun _ : U => 1),
      T.normBound = 1 ∧ T.ComplexityLE (budget s) ∧
      ∀ u : U → ℝ, T.evalReal u = (Real.fourierChar (eval u P) : ℂ) := by
  by_cases hs : 0 < s
  · exact exists_niltest hs P hP
  · have hs : s = 0 := by omega
    subst s
    let T := RationalFilteredNilmanifold.Niltest.const (nilmanifold 0)
      (fun _ : U => 1) (Real.fourierChar (P.coeff 0) : ℂ)
    have hn : T.normBound = 1 := by
      apply NNReal.eq
      exact Circle.norm_coe _
    refine ⟨T, hn, ⟨nilmanifold_geometry 0, ?_⟩, ?_⟩
    · rw [hn]
      change Real.log (2 + (1 : ℝ) + 0) ≤ budget 0
      have hl := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
      norm_num at hl ⊢
      exact hl.trans (two_le_budget 0)
    · intro u
      have heq : P = C (P.coeff 0) :=
        totalDegree_eq_zero_iff_eq_C.mp (Nat.eq_zero_of_le_zero hP)
      change (Real.fourierChar (P.coeff 0) : ℂ) = (Real.fourierChar (eval u P) : ℂ)
      conv_rhs => rw [heq, eval_C]

end Erdos3.OrdinaryPolynomialPhase

end

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators TensorProduct

variable {U : Type*} [Fintype U] [DecidableEq U] {n : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra
    OrdinaryPolynomialPhase.weight n)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra
    OrdinaryPolynomialPhase.weight n)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra
    OrdinaryPolynomialPhase.weight n)]
  [T2Space (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra
    OrdinaryPolynomialPhase.weight n)]

theorem exists_localMajor_slice_niltest
    (N : U → ℕ) (q : ℕ) (hq : 0 < q)
    (P E R : MvPolynomial U ℝ) (hP : P.totalDegree ≤ n + 1)
    (hE : E.totalDegree ≤ n + 1)
    (htop : homogeneousComponent (n + 1) P = E + R)
    (hR : realPolynomialCoefficientGrid q R)
    (M δ : ℝ) (hM : 0 ≤ M) (hδ : 0 < δ)
    (hcoeff : ∀ α, |E.coeff α| ≤ M / monomialScale (fun i => (N i : ℝ)) α)
    (f : (∀ i, Fin (N i)) → ℝ) :
    let K := ((n + 1 : ℕ) + 1 : ℝ) * ((Fintype.card U : ℝ) + 1) ^ (n + 1) *
      M * Fintype.card U * (n + 1)
    let ρ := min 1 (δ / (K + 1))
    (∀ i, 4 * (q : ℝ) ≤ ρ * N i) →
    ∃ A : ResidueBoxSlice N q,
      (∀ i, 0 < A.length i ∧ ρ * N i ≤ 4 * q * A.length i) ∧
      (𝔼 x, f x) ≤ (𝔼 j : (∀ i, Fin (A.length i)), f (A.point j)) ∧
      ∃ T : (OrdinaryPolynomialPhase.nilmanifold n).Niltest (fun _ : U => 1),
        T.normBound = 1 ∧ T.ComplexityLE (OrdinaryPolynomialPhase.budget n) ∧
        1 - 2 * Real.pi * δ ≤ ‖𝔼 j : (∀ i, Fin (A.length i)),
          (Real.fourierChar (eval (fun i => ((A.point j i).val : ℝ)) P) : ℂ) *
            star (T.eval (fun i => ((j i).val : ℤ)))‖ := by
  intro K ρ hlarge
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hρ : 0 < ρ := lt_min (by norm_num) (div_pos hδ (by linarith))
  have hKρ : K * ρ ≤ δ := by
    have hle := (le_div_iff₀ (by linarith : 0 < K + 1)).mp
      (min_le_right (1 : ℝ) (δ / (K + 1)))
    change ρ * (K + 1) ≤ δ at hle
    nlinarith
  obtain ⟨A, hA, hscore, hslow⟩ := exists_slowPolynomial_residueSlice N hq hρ
    (min_le_left _ _) hM hlarge E hE hcoeff f
  let r : U → ℤ := fun i => (A.start i : ℤ)
  let v : (∀ i, Fin (A.length i)) → U → ℤ := fun j i => ((j i).val : ℤ)
  let Q := localMajorLowerPhase n q r P
  obtain ⟨T, hnorm, hbudget, hT⟩ := OrdinaryPolynomialPhase.exists_niltest_of_degree
    Q (localMajorLowerPhase_totalDegree_le n q r P hP)
  refine ⟨A, hA, hscore, T, hnorm, hbudget, ?_⟩
  let : ∀ i, Nonempty (Fin (A.length i)) := fun i => ⟨⟨0, (hA i).1⟩⟩
  have hpoint (j : ∀ i, Fin (A.length i)) :
      (fun i => ((r i + (q : ℤ) * v j i : ℤ) : ℝ)) =
        (fun i => ((A.point j i).val : ℝ)) := by
    funext i
    simp only [r, v, ResidueBoxSlice.point, Int.cast_add, Int.cast_mul,
      Int.cast_natCast, Nat.cast_add, Nat.cast_mul]
  have hlocal := (localMajorPhaseCorrelation
    (FiniteProbabilityWeights.uniform (∀ i, Fin (A.length i))) v n q hq r P E R hP htop hR
    (eval (fun i => (A.start i : ℝ)) E) δ (by
      intro j _
      rw [hpoint j]
      exact (hslow j).trans (by simpa only [K, Nat.cast_add, Nat.cast_one] using hKρ))).2
  rw [FiniteProbabilityWeights.uniform_complexMean] at hlocal
  have heval (j : ∀ i, Fin (A.length i)) : T.eval (v j) =
      (Real.fourierChar (eval (fun i => (v j i : ℝ)) Q) : ℂ) := by
    rw [← T.evalReal_integer, hT]
  simpa only [hpoint, heval, Q, v] using hlocal

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators TensorProduct

variable {U : Type*} [Fintype U] [DecidableEq U] {n : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra
    OrdinaryPolynomialPhase.weight n)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra
    OrdinaryPolynomialPhase.weight n)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra
    OrdinaryPolynomialPhase.weight n)]
  [T2Space (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra
    OrdinaryPolynomialPhase.weight n)]

theorem exists_localMajor_dense_slice_niltest
    (N : U → ℕ) (q : ℕ) (hq : 0 < q)
    (P E R : MvPolynomial U ℝ) (hP : P.totalDegree ≤ n + 1)
    (hE : E.totalDegree ≤ n + 1)
    (htop : homogeneousComponent (n + 1) P = E + R)
    (hR : realPolynomialCoefficientGrid q R)
    (M δ : ℝ) (hM : 0 ≤ M) (hδ : 0 < δ)
    (hcoeff : ∀ α, |E.coeff α| ≤ M / monomialScale (fun i => (N i : ℝ)) α)
    (f : (U → ℤ) → ℝ) :
    let K := ((n + 1 : ℕ) + 1 : ℝ) * ((Fintype.card U : ℝ) + 1) ^ (n + 1) *
      M * Fintype.card U * (n + 1)
    let ρ := min 1 (δ / (K + 1))
    (∀ i, 4 * (q : ℝ) ≤ ρ * N i) →
    ∃ A : ResidueBoxSlice N q,
      IsDenseCommonStrideBox N (Real.log (4 * (q : ℝ) / ρ)) A.integerPoints ∧
      (𝔼 x : (∀ i, Fin (N i)), f (fun i => ((x i).val : ℤ))) ≤
        (𝔼 x ∈ A.integerPoints, f x) ∧
      ∃ T : (OrdinaryPolynomialPhase.nilmanifold n).Niltest (fun _ : U => 1),
        T.normBound = 1 ∧ T.ComplexityLE (OrdinaryPolynomialPhase.budget n) ∧
        1 - 2 * Real.pi * δ ≤ ‖𝔼 x ∈ A.integerPoints,
          (Real.fourierChar (eval (fun i => (x i : ℝ)) P) : ℂ) *
            star (T.eval (commonStrideIndex (fun i => (A.start i : ℤ)) q x))‖ := by
  intro K ρ hlarge
  obtain ⟨A, hA, hscore, T, hnorm, hbudget, hcorr⟩ := exists_localMajor_slice_niltest
    N q hq P E R hP hE htop hR M δ hM hδ hcoeff
    (fun x => f (fun i => ((x i).val : ℤ))) hlarge
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hρ : 0 < ρ := lt_min (by norm_num) (div_pos hδ (by linarith))
  refine ⟨A, A.isDenseCommonStrideBox hq hρ (fun i => (hA i).1)
    (fun i => (hA i).2), ?_, T, hnorm, hbudget, ?_⟩
  · rw [A.expect_integerPoints hq]
    exact hscore
  · rw [A.expect_integerPoints hq]
    simp only [A.commonStrideIndex_integerPoint hq, ResidueBoxSlice.integerPoint,
      Int.cast_natCast]
    exact hcorr

theorem exists_localMajor_dense_slice_niltest_nine_tenths
    (N : U → ℕ) (q : ℕ) (hq : 0 < q)
    (P E R : MvPolynomial U ℝ) (hP : P.totalDegree ≤ n + 1)
    (hE : E.totalDegree ≤ n + 1)
    (htop : homogeneousComponent (n + 1) P = E + R)
    (hR : realPolynomialCoefficientGrid q R)
    (M : ℝ) (hM : 0 ≤ M)
    (hcoeff : ∀ α, |E.coeff α| ≤ M / monomialScale (fun i => (N i : ℝ)) α)
    (f : (U → ℤ) → ℝ) :
    let K := ((n + 1 : ℕ) + 1 : ℝ) * ((Fintype.card U : ℝ) + 1) ^ (n + 1) *
      M * Fintype.card U * (n + 1)
    let ρ := min 1 ((1 / (20 * Real.pi)) / (K + 1))
    (∀ i, 4 * (q : ℝ) ≤ ρ * N i) →
    ∃ A : ResidueBoxSlice N q,
      IsDenseCommonStrideBox N (Real.log (4 * (q : ℝ) / ρ)) A.integerPoints ∧
      (𝔼 x : (∀ i, Fin (N i)), f (fun i => ((x i).val : ℤ))) ≤
        (𝔼 x ∈ A.integerPoints, f x) ∧
      ∃ T : (OrdinaryPolynomialPhase.nilmanifold n).Niltest (fun _ : U => 1),
        T.normBound = 1 ∧ T.ComplexityLE (OrdinaryPolynomialPhase.budget n) ∧
        (9 / 10 : ℝ) ≤ ‖𝔼 x ∈ A.integerPoints,
          (Real.fourierChar (eval (fun i => (x i : ℝ)) P) : ℂ) *
            star (T.eval (commonStrideIndex (fun i => (A.start i : ℤ)) q x))‖ := by
  simpa only [major_phase_nine_tenths] using exists_localMajor_dense_slice_niltest
    N q hq P E R hP hE htop hR M (1 / (20 * Real.pi)) hM (by positivity) hcoeff f

theorem exists_localMajor_dense_slice_niltest_early
    (N : U → ℕ) (q : ℕ) (hq : 0 < q)
    (P E R : MvPolynomial U ℝ) (hP : P.totalDegree ≤ n + 1)
    (hE : E.totalDegree ≤ n + 1)
    (htop : homogeneousComponent (n + 1) P = E + R)
    (hR : realPolynomialCoefficientGrid q R)
    (M p : ℝ) (hM : 0 ≤ M) (hp : 1 ≤ p)
    (hdim : (Fintype.card U : ℝ) ≤ p) (hMexp : M ≤ Real.exp p)
    (hqexp : (q : ℝ) ≤ Real.exp p)
    (hcoeff : ∀ α, |E.coeff α| ≤ M / monomialScale (fun i => (N i : ℝ)) α)
    (f : (U → ℤ) → ℝ)
    (hN : ∀ i, Real.exp ((p + (n + 401 : ℕ)) ^ (n + 401)) ≤ (N i : ℝ)) :
    ∃ A : ResidueBoxSlice N q,
      IsDenseCommonStrideBox N ((p + (n + 401 : ℕ)) ^ (n + 401)) A.integerPoints ∧
      (𝔼 x : (∀ i, Fin (N i)), f (fun i => ((x i).val : ℤ))) ≤
        (𝔼 x ∈ A.integerPoints, f x) ∧
      ∃ T : (OrdinaryPolynomialPhase.nilmanifold n).Niltest (fun _ : U => 1),
        T.normBound = 1 ∧ T.ComplexityLE (OrdinaryPolynomialPhase.budget n) ∧
        (9 / 10 : ℝ) ≤ ‖𝔼 x ∈ A.integerPoints,
          (Real.fourierChar (eval (fun i => (x i : ℝ)) P) : ℂ) *
            star (T.eval (commonStrideIndex (fun i => (A.start i : ℤ)) q x))‖ := by
  let ρ := slowPolynomialSliceRadius (n + 1) (Fintype.card U) M
  have hρ : 0 < ρ := slowPolynomialSliceRadius_pos _ _ hM
  have hcost : Real.log (4 * (q : ℝ) / ρ) ≤ (p + (n + 401 : ℕ)) ^ (n + 401) := by
    simpa only [Nat.add_assoc, Nat.reduceAdd] using slowPolynomialSlice_log_cost
      (n + 1) (Fintype.card U) hp hdim hM hMexp (by exact_mod_cast hq) hqexp
  have hlarge : ∀ i, 4 * (q : ℝ) ≤ ρ * N i := by
    intro i
    have hratio : 4 * (q : ℝ) / ρ ≤ Real.exp ((p + (n + 401 : ℕ)) ^ (n + 401)) :=
      (Real.log_le_iff_le_exp (by positivity)).mp hcost
    simpa only [mul_comm] using (div_le_iff₀ hρ).mp (hratio.trans (hN i))
  obtain ⟨A, hA, hscore, hT⟩ := exists_localMajor_dense_slice_niltest_nine_tenths
    N q hq P E R hP hE htop hR M hM hcoeff f (by
      simpa only [ρ, slowPolynomialSliceRadius, slowPolynomialSliceSlope,
        Nat.cast_add, Nat.cast_one] using hlarge)
  have hA' : IsDenseCommonStrideBox N (Real.log (4 * (q : ℝ) / ρ)) A.integerPoints := by
    simpa only [ρ, slowPolynomialSliceRadius, slowPolynomialSliceSlope,
      Nat.cast_add, Nat.cast_one] using hA
  exact ⟨A, hA'.mono hcost, hscore, hT⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.RefilteredPolynomialProjection
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration
open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

variable {σ L M : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s t : ℕ}
    (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M t)
    (w : σ → ℕ)

theorem filteredRealPolynomialSection_value (S : M →ₗ[ℚ] L)
    (hS : ∀ j, ∀ y ∈ G.layer j, S y ∈ F.layer j)
    (g : (G.realification.adaptedPolynomialFiltration w).Group) (z : σ → ℝ) :
    F.adaptedPolynomialRealValueHom w z (F.filteredRealPolynomialSection G w S hS g) =
      ⟨S.baseChange ℝ (G.adaptedPolynomialRealValueHom w z g).coord⟩ := by
  apply NilpotentLieBCHGroup.ext
  exact eval₂_map (S.baseChange ℝ) z (g.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] M))

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.ControlledMarkedKernelNormalization
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι κ L M : Type*} [Fintype κ] [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s t : ℕ}
    (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M t)
    (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j)
    (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (w : σ → ℕ)

theorem exists_marked_kernel_normalized_factors
    (H : Submodule ℚ L) (hH : F.layer 2 ≤ H)
    (bk : Basis κ ℚ (LinearMap.ker φ.toLinearMap))
    (e p r : (F.realification.adaptedPolynomialFiltration w).Group)
    (hp : realificationLieHom φ
      (coefficients (p.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0) ∈
        (H.map φ.toLinearMap).baseChange ℝ) :
    ∃ (a : ℝ ⊗[ℚ] LinearMap.ker φ.toLinearMap)
      (c : LinearMap.ker φ.toLinearMap)
      (e' p' r' : (F.realification.adaptedPolynomialFiltration w).Group),
      (∀ i, 0 ≤ (bk.baseChange ℝ).repr a i ∧ (bk.baseChange ℝ).repr a i < 1) ∧
      (∀ i, ∃ z : ℤ, bk.repr c i = z) ∧
      e' = e * F.realification.adaptedConstantGroupHom w
        ⟨(LinearMap.ker φ.toLinearMap).subtype.baseChange ℝ a⟩ ∧
      r' = F.realification.adaptedConstantGroupHom w ⟨(1 : ℝ) ⊗ₜ[ℚ] (c : L)⟩ * r ∧
      e' * p' * r' = e * p * r ∧
      F.realPolynomialSymbolHom b ω hF w e' = F.realPolynomialSymbolHom b ω hF w e ∧
      F.realPolynomialSymbolHom b ω hF w p' = F.realPolynomialSymbolHom b ω hF w p ∧
      F.realPolynomialSymbolHom b ω hF w r' = F.realPolynomialSymbolHom b ω hF w r ∧
      F.realPolynomialGroupMap G φ hφ w e' = F.realPolynomialGroupMap G φ hφ w e ∧
      F.realPolynomialGroupMap G φ hφ w p' = F.realPolynomialGroupMap G φ hφ w p ∧
      F.realPolynomialGroupMap G φ hφ w r' = F.realPolynomialGroupMap G φ hφ w r ∧
      coefficients (p'.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 ∈ H.baseChange ℝ := by
  obtain ⟨a, c, ha, hc, hka, hkc, hmid⟩ :=
    F.exists_kernel_constant_factors G φ H hH bk
      (F.realification.adaptedPolynomialConstantHom w p)
      (by simpa only [F.realification.adaptedPolynomialConstantHom_coord] using hp)
  let ka : F.realification.Group := ⟨(LinearMap.ker φ.toLinearMap).subtype.baseChange ℝ a⟩
  let kc : F.realification.Group := ⟨(1 : ℝ) ⊗ₜ[ℚ] (c : L)⟩
  let C := F.realification.adaptedConstantGroupHom w
  let p' := (C ka)⁻¹ * p * (C kc)⁻¹
  have hma : F.realPolynomialGroupMap G φ hφ w (C ka) = 1 := by
    rw [F.realPolynomialGroupMap_constant, hka, map_one]
  have hmc : F.realPolynomialGroupMap G φ hφ w (C kc) = 1 := by
    rw [F.realPolynomialGroupMap_constant, hkc, map_one]
  refine ⟨a, c, e * C ka, p', C kc * r, ha, hc, rfl, rfl, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_⟩
  · dsimp only [p']; group
  · simp only [map_mul, C, F.realPolynomialSymbolHom_constant, mul_one]
  · simp only [p', map_mul, map_inv, C, F.realPolynomialSymbolHom_constant,
      inv_one, one_mul, mul_one]
  · simp only [map_mul, C, F.realPolynomialSymbolHom_constant, one_mul]
  · rw [map_mul, hma, mul_one]
  · simp only [p', map_mul, map_inv, hma, hmc, inv_one, one_mul, mul_one]
  · rw [map_mul, hmc, one_mul]
  · rw [← F.realification.adaptedPolynomialConstantHom_coord]
    simpa only [p', map_mul, map_inv, C,
      F.realification.adaptedPolynomialConstantHom_constant] using hmid

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

theorem exists_controlled_marked_kernel_normalization (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {σ ι κ L M : Type*} [Fintype σ] [Fintype ι] [Fintype κ]
      [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
      {t : ℕ} (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M t)
      (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j)
      (b : Basis ι ℚ L) (ω : ι → ℕ)
      (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (w : σ → ℕ), (∀ i, 0 < w i) →
      ∀ (bk : Basis κ ℚ (LinearMap.ker φ.toLinearMap))
        (H l : ℕ) (p : ℝ), 1 ≤ H → 0 < l → 0 ≤ p →
      (Fintype.card ι : ℝ) ≤ p → (Fintype.card κ : ℝ) ≤ p →
      (Fintype.card σ : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p → (l : ℝ) ≤ Real.exp p →
      (∀ i j k, RationalHeightLE (b.repr ⁅b i, b j⁆ k) H) →
      (∀ i j, RationalHeightLE (b.repr (bk j : L) i) H) →
      ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ l ∣ m ∧
        ∀ (S : Submodule ℚ L), F.layer 2 ≤ S →
        ∀ (T : σ → ℝ), (∀ i, 0 < T i) →
        ∀ e middle r : (F.realification.adaptedPolynomialFiltration w).Group,
        F.PolynomialSlowBound b w T (Real.exp ((p + 2) ^ a)) e →
        F.PolynomialRationalGrid b w l r →
        realificationLieHom φ
          (coefficients (middle.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0) ∈
            (S.map φ.toLinearMap).baseChange ℝ →
        ∃ (u : ℝ ⊗[ℚ] LinearMap.ker φ.toLinearMap)
          (v : LinearMap.ker φ.toLinearMap)
          (e' middle' r' : (F.realification.adaptedPolynomialFiltration w).Group),
          (∀ i, 0 ≤ (bk.baseChange ℝ).repr u i ∧ (bk.baseChange ℝ).repr u i < 1) ∧
          (∀ i, ∃ z : ℤ, bk.repr v i = z) ∧
          e' = e * F.realification.adaptedConstantGroupHom w
            ⟨(LinearMap.ker φ.toLinearMap).subtype.baseChange ℝ u⟩ ∧
          r' = F.realification.adaptedConstantGroupHom w ⟨(1 : ℝ) ⊗ₜ[ℚ] (v : L)⟩ * r ∧
          e' * middle' * r' = e * middle * r ∧
          F.realPolynomialSymbolHom b ω hF w e' = F.realPolynomialSymbolHom b ω hF w e ∧
          F.realPolynomialSymbolHom b ω hF w middle' =
            F.realPolynomialSymbolHom b ω hF w middle ∧
          F.realPolynomialSymbolHom b ω hF w r' = F.realPolynomialSymbolHom b ω hF w r ∧
          F.realPolynomialGroupMap G φ hφ w e' = F.realPolynomialGroupMap G φ hφ w e ∧
          F.realPolynomialGroupMap G φ hφ w middle' =
            F.realPolynomialGroupMap G φ hφ w middle ∧
          F.realPolynomialGroupMap G φ hφ w r' = F.realPolynomialGroupMap G φ hφ w r ∧
          coefficients (middle'.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 ∈
            S.baseChange ℝ ∧
          F.PolynomialSlowBound b w T (Real.exp ((p + C) ^ C)) e' ∧
          F.PolynomialRationalGrid b w m r' := by
  obtain ⟨ce, _, hslow⟩ := exists_polynomial_slow_product_bound s 1 2
  obtain ⟨cr, _, hrational⟩ := exists_polynomial_rational_product_bound s 2
  let Q : Polynomial ℕ := (Polynomial.X + 2) ^ a + (Polynomial.X + 2) ^ 4
  let B : Polynomial ℕ := (Q + Polynomial.C ce) ^ ce + (Q + Polynomial.C cr) ^ cr
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget B
  refine ⟨C, hC, ?_⟩
  intro σ ι κ L M _ _ _ _ _ _ _ t F G φ hφ b ω hF w hw bk H l p hH hl hp
    hι hκ hσ hHp hlp hbracket hkernel
  obtain ⟨q, hq, hqbound, hkb, hkg⟩ := exists_basis_image_bounds_of_height b bk
    (LinearMap.ker φ.toLinearMap).subtype H hkernel
  let P : ℝ := (p + 2) ^ a + (p + 2) ^ 4
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hp4 : p ≤ (p + 2) ^ 4 := by
    apply (show p ≤ p + 2 by linarith).trans
    simpa only [pow_one] using
      pow_le_pow_right₀ (show (1 : ℝ) ≤ p + 2 by linarith) (show 1 ≤ 4 by omega)
  have hpP : p ≤ P := hp4.trans (le_add_of_nonneg_left (by positivity))
  have hden : ((q * l : ℕ) : ℝ) ≤ Real.exp P :=
    (kernel_inclusion_denominator_mul_le_exp (Fintype.card ι) (Fintype.card κ)
      H q l hp hι hκ hHp hqbound hlp).trans
      (Real.exp_le_exp.mpr (le_add_of_nonneg_left (by positivity)))
  have hbudgetP : (P + ce) ^ ce + (P + cr) ^ cr ≤ (p + C) ^ C := by
    simpa [B, Q, P, Polynomial.eval₂_pow] using hbudget p hp
  have heBudget : (P + ce) ^ ce ≤ (p + C) ^ C :=
    (le_add_of_nonneg_right (by positivity)).trans hbudgetP
  have hrBudget : (P + cr) ^ cr ≤ (p + C) ^ C :=
    (le_add_of_nonneg_left (by positivity)).trans hbudgetP
  obtain ⟨m, hm, hmp, hqlm, hprod⟩ := hrational F b ω hF w hw H P hH hP
    (hι.trans hpP) (hσ.trans hpP) (hHp.trans (Real.exp_le_exp.mpr hpP)) hbracket
    (q * l) (Nat.mul_pos hq hl) hden
  refine ⟨m, hm, hmp.trans (Real.exp_le_exp.mpr hrBudget),
    (dvd_mul_left l q).trans hqlm, ?_⟩
  intro S hS T hT e middle r he hr hmiddle
  obtain ⟨u, v, e', middle', r', hu, hv, he', hr', hproduct, hsymE, hsymP, hsymR,
    hmarkE, hmarkP, hmarkR, hconstant⟩ :=
    F.exists_marked_kernel_normalized_factors G φ hφ b ω hF w S hS bk
      e middle r hmiddle
  refine ⟨u, v, e', middle', r', hu, hv, he', hr', hproduct, hsymE, hsymP, hsymR,
    hmarkE, hmarkP, hmarkR, hconstant, ?_, ?_⟩
  · let ku : F.realification.Group :=
      ⟨(LinearMap.ker φ.toLinearMap).subtype.baseChange ℝ u⟩
    have hku : ∀ i, |(b.baseChange ℝ).repr ku.coord i| ≤ Real.exp (P + 2) := by
      intro i
      have hcoord := scalarExtension_fractional_coordinates_bound b bk
        (LinearMap.ker φ.toLinearMap).subtype H hkb u hu i
      have hfactor := kernel_coordinate_factor_le_exp (Fintype.card κ) H hp hκ hHp
      have h24 : (p + 2) ^ 2 ≤ (p + 2) ^ 4 :=
        pow_le_pow_right₀ (by linarith) (by omega)
      exact hcoord.trans (hfactor.trans (Real.exp_le_exp.mpr
        (h24.trans (by dsimp [P]; have := pow_nonneg (by linarith : 0 ≤ p + 2) a; linarith))))
    have hcs := F.polynomialSlowBound_constant b w T hT (Real.exp_nonneg _) ku hku
    have hes := F.polynomialSlowBound_mono b w T hT
      (Real.exp_le_exp.mpr (show (p + 2) ^ a ≤ P + 2 by
        dsimp [P]; have := pow_nonneg (by linarith : 0 ≤ p + 2) 4; linarith)) e he
    have hout := hslow F b ω hF w hw H P hH hP (hι.trans hpP) (hσ.trans hpP)
      (hHp.trans (Real.exp_le_exp.mpr hpP)) hbracket T hT
      [e, F.realification.adaptedConstantGroupHom w ku] (by simp)
      (by
        intro z hz
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
        rcases hz with rfl | rfl
        · simpa only [pow_one] using hes
        · simpa only [pow_one] using hcs)
    have hout' : F.PolynomialSlowBound b w T (Real.exp ((P + ce) ^ ce)) e' := by
      simpa only [List.prod_cons, List.prod_nil, mul_one, ← he', ku] using hout
    exact F.polynomialSlowBound_mono b w T hT (Real.exp_le_exp.mpr heBudget) e' hout'
  · let kv : F.realification.Group := ⟨(1 : ℝ) ⊗ₜ[ℚ] (v : L)⟩
    have hkv := integral_basis_image_realDenominatorGrid b bk
      (LinearMap.ker φ.toLinearMap).subtype q hkg v hv
    have hcs := F.polynomialRationalGrid_constant b w q kv hkv
    have hcs' := F.polynomialRationalGrid_of_dvd b w hq (dvd_mul_right q l) _ hcs
    have hrs := F.polynomialRationalGrid_of_dvd b w hl (dvd_mul_left l q) r hr
    have hout := hprod [F.realification.adaptedConstantGroupHom w kv, r] (by simp)
      (by
        intro z hz
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
        rcases hz with rfl | rfl
        · exact hcs'
        · exact hrs)
    simpa only [List.prod_cons, List.prod_nil, mul_one, ← hr', kv] using hout

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FullMarkedNativeFactorization
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L)

theorem exists_fractional_integral_constant_normalization (g : F.realification.Group) :
    ∃ (a : ℝ ⊗[ℚ] L) (v : L),
      (∀ i, 0 ≤ (b.baseChange ℝ).repr a i ∧ (b.baseChange ℝ).repr a i < 1) ∧
      (∀ i, ∃ z : ℤ, b.repr v i = z) ∧
      ((⟨a⟩ : F.realification.Group)⁻¹ * g *
        (⟨(1 : ℝ) ⊗ₜ[ℚ] v⟩ : F.realification.Group)⁻¹).coord ∈ F.realification.layer 2 := by
  obtain ⟨a, v, hav, ha, hv⟩ := realification_fractional_integer_split b g.coord
  refine ⟨a, v, ha, hv, ?_⟩
  have h := F.realification.bch_triple_sub_sum_mem_next_layer 1 (-a) g.coord
    (-(1 : ℝ) ⊗ₜ[ℚ] v)
    (by rw [F.realification.one_eq_top]; trivial)
    (by rw [F.realification.one_eq_top]; trivial)
  have hz : -a + g.coord + -(1 : ℝ) ⊗ₜ[ℚ] v = 0 := by rw [hav]; abel
  simpa only [hz, sub_zero, NilpotentLieBCHGroup.coord_mul,
    NilpotentLieBCHGroup.coord_inv] using h

theorem exists_fractional_integral_polynomial_normalization
    (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (w : σ → ℕ) (e p r : (F.realification.adaptedPolynomialFiltration w).Group) :
    ∃ (a : ℝ ⊗[ℚ] L) (v : L)
      (e' p' r' : (F.realification.adaptedPolynomialFiltration w).Group),
      (∀ i, 0 ≤ (b.baseChange ℝ).repr a i ∧ (b.baseChange ℝ).repr a i < 1) ∧
      (∀ i, ∃ z : ℤ, b.repr v i = z) ∧
      e' = e * F.realification.adaptedConstantGroupHom w ⟨a⟩ ∧
      r' = F.realification.adaptedConstantGroupHom w ⟨(1 : ℝ) ⊗ₜ[ℚ] v⟩ * r ∧
      e' * p' * r' = e * p * r ∧
      F.realPolynomialSymbolHom b ω hF w e' = F.realPolynomialSymbolHom b ω hF w e ∧
      F.realPolynomialSymbolHom b ω hF w p' = F.realPolynomialSymbolHom b ω hF w p ∧
      F.realPolynomialSymbolHom b ω hF w r' = F.realPolynomialSymbolHom b ω hF w r ∧
      coefficients (p'.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 ∈ F.realification.layer 2 := by
  obtain ⟨a, v, ha, hv, hmid⟩ := F.exists_fractional_integral_constant_normalization b
    (F.realification.adaptedPolynomialConstantHom w p)
  let C := F.realification.adaptedConstantGroupHom w
  let ka : F.realification.Group := ⟨a⟩
  let kr : F.realification.Group := ⟨(1 : ℝ) ⊗ₜ[ℚ] v⟩
  let p' := (C ka)⁻¹ * p * (C kr)⁻¹
  refine ⟨a, v, e * C ka, p', C kr * r, ha, hv, rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp only [p']; group
  · simp only [map_mul, C, F.realPolynomialSymbolHom_constant, mul_one]
  · simp only [p', map_mul, map_inv, C, F.realPolynomialSymbolHom_constant,
      inv_one, one_mul, mul_one]
  · simp only [map_mul, C, F.realPolynomialSymbolHom_constant, one_mul]
  · rw [← F.realification.adaptedPolynomialConstantHom_coord]
    simpa only [p', map_mul, map_inv, C,
      F.realification.adaptedPolynomialConstantHom_constant] using hmid

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.HomogeneousQuotientSymbolLiftBounds
namespace OAI

section

namespace Erdos3

open Module VectorPolynomial
open scoped BigOperators TensorProduct

namespace VectorPolynomial

theorem weightedHomogeneousPart_coordinateBound {σ ι V : Type*}
    [AddCommGroup V] [Module ℚ V] [Module ℝ V]
    (b : Basis ι ℝ V) (T : σ → ℝ) (hT : ∀ j, 0 < T j)
    {M : ℝ} (hM : 0 ≤ M) (p : VectorPolynomial σ ℚ V)
    (hp : ∀ α i, |b.repr (coefficients p α) i| ≤ M / monomialScale T α)
    (w : σ → ℕ) (k : ℕ) :
    ∀ α i, |b.repr (coefficients (weightedHomogeneousPart w k p) α) i| ≤
      M / monomialScale T α := by
  intro α i
  rw [coefficients_weightedHomogeneousPart]
  split_ifs
  · exact hp α i
  · simpa using div_nonneg hM (monomialScale_pos T hT α).le

theorem weightedHomogeneousPart_coordinateGrid {σ ι V : Type*}
    [AddCommGroup V] [Module ℚ V] [Module ℝ V]
    (b : Basis ι ℝ V) (p : VectorPolynomial σ ℚ V) (q : ℕ)
    (hp : ∀ α, (fun i => b.repr (coefficients p α) i) ∈ realDenominatorGrid q)
    (w : σ → ℕ) (k : ℕ) :
    ∀ α, (fun i => b.repr (coefficients (weightedHomogeneousPart w k p) α) i) ∈
      realDenominatorGrid q := by
  intro α
  rw [coefficients_weightedHomogeneousPart]
  split_ifs
  · exact hp α
  · refine ⟨0, ?_⟩
    ext i
    simp

end VectorPolynomial

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RealSymbolGradeQuotientSplitting
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (w : σ → ℕ)

theorem realGradedSymbolPolynomial_gradeProjection_eq_weightedHomogeneousPart
    (k : ℕ) (x : F.RealPolynomialSymbol w) :
    F.realGradedSymbolPolynomial b ω hF w
      (basisGradeProjection ((F.polynomialSymbolBasis b ω hF w).baseChange ℝ)
        (fun z => ω z.val.2) k x) =
      weightedHomogeneousPart w k (F.realGradedSymbolPolynomial b ω hF w x) := by
  apply coefficients.injective
  ext α
  rw [F.realGradedSymbolPolynomial_gradeProjection_coefficient,
    coefficients_weightedHomogeneousPart]
  apply ((F.associatedGradedBasis b ω hF).baseChange ℝ).repr.injective
  ext i
  rw [basisGradeProjection_repr]
  by_cases hi : ω i = k
  · rw [if_pos hi]
    by_cases hα : Finsupp.weight w α = k
    · rw [if_pos hα]
    · rw [if_neg hα, map_zero, Finsupp.zero_apply]
      exact F.realGradedSymbolPolynomial_coordinate_of_ne b ω hF w x α i
        (by simpa only [hi] using hα)
  · rw [if_neg hi]
    by_cases hα : Finsupp.weight w α = k
    · rw [if_pos hα]
      exact (F.realGradedSymbolPolynomial_coordinate_of_ne b ω hF w x α i
        (fun h => hi (h.symm.trans hα))).symm
    · rw [if_neg hα, map_zero, Finsupp.zero_apply]

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.RestrictedChartPrefixControl
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped TensorProduct

variable {σ τ V : Type*} [AddCommGroup V] [Module ℚ V] [Module ℝ V]
  [IsScalarTower ℚ ℝ V]

theorem realChartSubstitute_map
    {W : Type*} [AddCommGroup W] [Module ℚ W] [Module ℝ W] [IsScalarTower ℚ ℝ W]
    (f : σ → MvPolynomial τ ℝ) (S : V →ₗ[ℝ] W) (p : VectorPolynomial σ ℚ V) :
    realChartSubstitute f (map (S.restrictScalars ℚ) p) =
      map (S.restrictScalars ℚ) (realChartSubstitute f p) := by
  have hmap : realCoefficientEquiv (map (S.restrictScalars ℚ) p) =
      map S (realCoefficientEquiv p) := by
    apply coefficients.injective
    ext α
    simp only [coefficients_realCoefficientEquiv, coefficients_map,
      LinearMap.restrictScalars_apply]
  have hsymm (q : VectorPolynomial τ ℝ V) :
      realCoefficientEquiv.symm (map S q) =
        map (S.restrictScalars ℚ) (realCoefficientEquiv.symm q) := by
    apply coefficients.injective
    ext α
    simp only [coefficients_realCoefficientEquiv_symm, coefficients_map,
      LinearMap.restrictScalars_apply]
  simp only [realChartSubstitute, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearMap.restrictScalars_apply, hmap, ← map_substitute, hsymm]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

attribute [local irreducible] realChartSubstitute realPolynomialChartSubstitution

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}

noncomputable def polynomialChartOuterIteration (F : NilpotentLieFiltration L s)
    (f : σ → MvPolynomial σ ℝ)
    (a r : ℕ → PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot) :
    ℕ → PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot ×
      PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot
  | 0 => (1, 1)
  | n + 1 =>
    let previous := polynomialChartOuterIteration F f a r n
    (previous.1 * realPolynomialChartSubstitution F.realification.lowerCentralSeries_eq_bot f (a n),
      r n * previous.2)

theorem polynomialChartOuterIteration_eq_products (F : NilpotentLieFiltration L s)
    (f : σ → MvPolynomial σ ℝ)
    (a r : ℕ → PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot) (n : ℕ) :
    F.polynomialChartOuterIteration f a r n =
      (realPolynomialChartSubstitution F.realification.lowerCentralSeries_eq_bot f
        ((List.range n).map a).prod, ((List.range n).map r).reverse.prod) := by
  induction n with
  | zero => simp only [polynomialChartOuterIteration, List.range_zero, List.map_nil,
      List.prod_nil, List.reverse_nil, map_one]
  | succ n ih =>
    simp only [polynomialChartOuterIteration, ih, List.range_succ, List.map_append,
      List.map_singleton, List.prod_append, List.prod_singleton, List.reverse_append,
      List.reverse_singleton, map_mul]

theorem exists_polynomial_chart_outer_iteration_bounds (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {σ ι L : Type*} [Fintype σ] [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
      (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
      (_hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (H : ℕ) (p : ℝ), 1 ≤ H → 0 ≤ p →
      (Fintype.card ι : ℝ) ≤ p → (Fintype.card σ : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p →
      (∀ i j z, RationalHeightLE (b.repr ⁅b i, b j⁆ z) H) →
      ∀ l : ℕ, 0 < l → (l : ℝ) ≤ Real.exp p →
      ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ l ∣ m ∧
        ∀ (f : σ → MvPolynomial σ ℝ)
          (q r : ℕ → PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot),
        (∀ j < s, (q j).coord ∈ F.realification.adaptedLieSubalgebra (fun _ => 1)) →
        (∀ j < s, (r j).coord ∈ F.realification.adaptedLieSubalgebra (fun _ => 1)) →
        (∀ j < s, CoefficientBound (b.baseChange ℝ) (fun _ => 1)
          (Real.exp ((p + 2) ^ a)) (q j).coord) →
        (∀ j < s, CoefficientGrid (b.baseChange ℝ) l (r j).coord) →
        ∀ n ≤ s, ∃ Echart : PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot,
          (F.polynomialChartOuterIteration f q r n).1 =
            realPolynomialChartSubstitution F.realification.lowerCentralSeries_eq_bot f Echart ∧
          CoefficientBound (b.baseChange ℝ) (fun _ => 1)
            (Real.exp ((p + C) ^ C)) Echart.coord ∧
          CoefficientGrid (b.baseChange ℝ) m (F.polynomialChartOuterIteration f q r n).2.coord := by
  obtain ⟨C, hC, hproducts⟩ := exists_outer_polynomial_product_bounds s a s
  refine ⟨C, hC, ?_⟩
  intro σ ι L _ _ _ _ F b ω hF H p hH hp hι hσ hHp hstructure l hl hlp
  obtain ⟨m, hm, hmp, hlm, hprod⟩ := hproducts F b ω hF H p hH hp hι hσ hHp hstructure l hl hlp
  refine ⟨m, hm, hmp, hlm, ?_⟩
  intro f q r hqa hra hqb hrb n hn
  have hmem (v : ℕ → PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot)
      (g : PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot)
      (hg : g ∈ (List.range n).map v) :
      ∃ j, j < s ∧ v j = g := by
    obtain ⟨j, hj, heq⟩ := List.mem_map.mp hg
    exact ⟨j, lt_of_lt_of_le (List.mem_range.mp hj) hn, heq⟩
  obtain ⟨hs, hr⟩ := hprod ((List.range n).map q) ((List.range n).map r)
    (by simpa using hn) (by simpa using hn)
    (fun g hg => by obtain ⟨j, hj, rfl⟩ := hmem q g hg; exact hqa j hj)
    (fun g hg => by obtain ⟨j, hj, rfl⟩ := hmem r g hg; exact hra j hj)
    (fun g hg => by obtain ⟨j, hj, rfl⟩ := hmem q g hg; exact hqb j hj)
    (fun g hg => by obtain ⟨j, hj, rfl⟩ := hmem r g hg; exact hrb j hj)
  refine ⟨((List.range n).map q).prod, ?_, hs, ?_⟩
  · rw [F.polynomialChartOuterIteration_eq_products]
  · rw [F.polynomialChartOuterIteration_eq_products]
    exact hr

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.HomogeneousRealSymbolPullback
namespace OAI

section

namespace Erdos3
open Module VectorPolynomial
open scoped TensorProduct BigOperators

namespace NilpotentLieFiltration
variable {σ τ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (w : σ → ℕ) (v : τ → ℕ) (β : σ → MvPolynomial τ ℝ)

attribute [local irreducible] realSymbolHomogeneousPullback realSymbolOfGradedPolynomial
  realChartSubstitute realGradedSymbolPolynomial gradedPolynomialSubmodule

theorem realSymbolGradeEvaluation_homogeneousPullback
    (hβ : ∀ i, (β i).IsWeightedHomogeneous v (w i))
    (x : F.RealPolynomialSymbol w) (j : ℕ) (u : τ → ℝ) :
    F.realSymbolGradeEvaluation b ω hF v j u
      (F.realSymbolHomogeneousPullback b ω hF w v β x) =
    F.realSymbolGradeEvaluation b ω hF w j (fun i => MvPolynomial.eval u (β i)) x := by
  rw [F.realSymbolGradeEvaluation_eq_projection,
    F.realGradedSymbolPolynomial_homogeneousPullback b ω hF w v β hβ,
    eval₂_realChartSubstitute, F.realSymbolGradeEvaluation_eq_projection]

theorem homogeneousPullback_quotient_mem_of_restricted_grade_values
    (hβ : ∀ i, (β i).IsWeightedHomogeneous v (w i))
    (U : LieSubalgebra ℚ F.AssociatedGraded) (K : Set (σ → ℝ))
    (hK : ∀ u : τ → ℝ, (fun i => MvPolynomial.eval u (β i)) ∈ K)
    (x : F.RealPolynomialSymbol w) (k : ℕ)
    (hx : ∀ t ∈ K, ∀ j < k,
      F.realSymbolGradeEvaluation b ω hF w j t x ∈ realificationLieSubalgebra U) :
    F.realSymbolGradeQuotientHom v k
      ⟨F.realSymbolHomogeneousPullback b ω hF w v β x⟩ ∈
      (NilpotentLieBCHGroup.realificationSubgroup
        (hnil := F.polynomialSymbol_lowerCentralSeries_eq_bot v)
        (F.symbolPointwiseSubalgebra b ω hF v U)).map (F.realSymbolGradeQuotientHom v k) := by
  exact F.realSymbolGradeQuotient_mem_of_restricted_path b ω hF w v U K β hK x
    ⟨F.realSymbolHomogeneousPullback b ω hF w v β x⟩ k hx
    (fun u j _ => F.realSymbolGradeEvaluation_homogeneousPullback b ω hF w v β hβ x j u)

theorem homogeneousPullback_residual_quotient_mem
    (hβ : ∀ i, (β i).IsWeightedHomogeneous v (w i))
    (U : LieSubalgebra ℚ F.AssociatedGraded) (K : Set (σ → ℝ))
    (hK : ∀ u : τ → ℝ, (fun i => MvPolynomial.eval u (β i)) ∈ K)
    (E Z R : F.RealPolynomialSymbolGroup w) (k : ℕ)
    (hx : ∀ t ∈ K, ∀ j < k,
      F.realSymbolGradeEvaluation b ω hF w j t (E⁻¹ * Z * R⁻¹).coord ∈
        realificationLieSubalgebra U) :
    let pull := F.realSymbolHomogeneousPullbackHom b ω hF w v β hβ
    F.realSymbolGradeQuotientHom v k ((pull E)⁻¹ * pull Z * (pull R)⁻¹) ∈
      (NilpotentLieBCHGroup.realificationSubgroup
        (hnil := F.polynomialSymbol_lowerCentralSeries_eq_bot v)
        (F.symbolPointwiseSubalgebra b ω hF v U)).map (F.realSymbolGradeQuotientHom v k) := by
  dsimp only
  rw [← map_inv, ← map_inv, ← map_mul, ← map_mul]
  exact F.homogeneousPullback_quotient_mem_of_restricted_grade_values
    b ω hF w v β hβ U K hK (E⁻¹ * Z * R⁻¹).coord k hx

end NilpotentLieFiltration
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.GlobalChartNativeFactorization
namespace OAI

section

namespace Erdos3

namespace NilpotentLieFiltration
open VectorPolynomial
open scoped TensorProduct

variable {σ τ υ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s)

attribute [local irreducible] realChartSubstitute weightedAdaptedRealChartLie weightedAdaptedRealChartHom

theorem weightedAdaptedRealChartHom_comp
    (w : σ → ℕ) (v : τ → ℕ) (u : υ → ℕ)
    (β : σ → MvPolynomial τ ℝ) (γ : τ → MvPolynomial υ ℝ)
    (hβ : ∀ i, β i ∈ weightedSupportLE v (w i))
    (hγ : ∀ i, γ i ∈ weightedSupportLE u (v i))
    (hcomp : ∀ i, MvPolynomial.aeval γ (β i) ∈ weightedSupportLE u (w i))
    (g : (F.realification.adaptedPolynomialFiltration w).Group) :
    F.weightedAdaptedRealChartHom w u (fun i => MvPolynomial.aeval γ (β i)) hcomp g =
      F.weightedAdaptedRealChartHom v u γ hγ (F.weightedAdaptedRealChartHom w v β hβ g) := by
  apply NilpotentLieBCHGroup.ext
  apply Subtype.ext
  simp only [weightedAdaptedRealChartHom_coord]
  exact (realChartSubstitute_comp β γ _).symm

end NilpotentLieFiltration
end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration
open Module VectorPolynomial _root_.MvPolynomial

variable {σ τ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

theorem realSymbolHomogeneousPullback_mem_pointwise
    (w : σ → ℕ) (v : τ → ℕ) (β : σ → MvPolynomial τ ℝ)
    (hβ : ∀ i, (β i).IsWeightedHomogeneous v (w i))
    (U : LieSubalgebra ℚ F.AssociatedGraded) (P : F.RealPolynomialSymbolGroup w)
    (hP : P.coord ∈ realificationLieSubalgebra (F.symbolPointwiseSubalgebra b ω hF w U)) :
    (F.realSymbolHomogeneousPullbackHom b ω hF w v β hβ P).coord ∈
      realificationLieSubalgebra (F.symbolPointwiseSubalgebra b ω hF v U) := by
  apply (F.mem_real_symbolPointwiseSubalgebra_iff_values b ω hF v U _).mpr
  intro t
  rw [F.realSymbolHomogeneousPullbackHom_coord,
    F.realGradedSymbolPolynomial_homogeneousPullback b ω hF w v β hβ,
    eval₂_realChartSubstitute]
  exact (F.mem_real_symbolPointwiseSubalgebra_iff_values b ω hF w U P.coord).mp hP _

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial _root_.MvPolynomial
open scoped TensorProduct

attribute [local irreducible] weightedAdaptedRealChartHom realPolynomialSymbolHom
  realSymbolHomogeneousPullbackHom realPolynomialSymbolLift

variable {σ τ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

theorem adaptedPolynomialRealValueHom_weightedChart
    (w : σ → ℕ) (v : τ → ℕ) (β : σ → MvPolynomial τ ℝ)
    (hβ : ∀ i, β i ∈ weightedSupportLE v (w i))
    (g : (F.realification.adaptedPolynomialFiltration w).Group) (t : τ → ℝ) :
    F.adaptedPolynomialRealValueHom v t (F.weightedAdaptedRealChartHom w v β hβ g) =
      F.adaptedPolynomialRealValueHom w (fun i => MvPolynomial.eval t (β i)) g := by
  apply NilpotentLieBCHGroup.ext
  rw [F.adaptedPolynomialRealValueHom_coord, F.weightedAdaptedRealChartHom_coord,
    eval₂_realChartSubstitute, F.adaptedPolynomialRealValueHom_coord]

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.ActualPathCurrentGradeReset
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration
open Module VectorPolynomial
open scoped TensorProduct

variable {σ τ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

theorem symbolPointwiseSubalgebra_basisGraded [Fintype τ] [Fintype ι]
    (v : τ → ℕ) (hv : ∀ i, 0 < v i) (U : LieSubalgebra ℚ F.AssociatedGraded) :
    BasisGradedSubmodule (F.polynomialSymbolBasis b ω hF v)
      (fun z => ω z.val.2) (F.symbolPointwiseSubalgebra b ω hF v U).toSubmodule := by
  let : Fintype (SymbolBasisIndex v ω) :=
    symbolBasisIndexFintype v ω s hv (F.adaptedBasis_weight_le_step b ω hF)
  have h := (F.symbolPointwiseSubalgebra_blockInvariant b ω hF v U).graded
    (F.polynomialSymbolBasis b ω hF v) (fun z => z.val.1)
    (F.symbolPointwiseSubalgebra b ω hF v U).toSubmodule (Finsupp.weight v)
  have he : (fun z : SymbolBasisIndex v ω => Finsupp.weight v z.val.1) =
      (fun z => ω z.val.2) := funext (fun z => z.property)
  rw [he] at h
  exact h

theorem exists_restricted_path_common_quotient_splitting
    (w : σ → ℕ) (v : τ → ℕ) (β : σ → MvPolynomial τ ℝ)
    (hβ : ∀ i, (β i).IsWeightedHomogeneous v (w i))
    (U : LieSubalgebra ℚ F.AssociatedGraded) (K : Set (σ → ℝ))
    (hK : ∀ u : τ → ℝ, (fun i => MvPolynomial.eval u (β i)) ∈ K)
    (E Z R : F.RealPolynomialSymbolGroup w) (k : ℕ)
    (hx : ∀ t ∈ K, ∀ j < k,
      F.realSymbolGradeEvaluation b ω hF w j t (E⁻¹ * Z * R⁻¹).coord ∈
        realificationLieSubalgebra U)
    (El Pl Rl : F.RealPolynomialSymbolGroup v)
    (hlocal : El * Pl * Rl = F.realSymbolHomogeneousPullbackHom b ω hF w v β hβ Z) :
    let pull := F.realSymbolHomogeneousPullbackHom b ω hF w v β hβ
    ∃ P₀ : F.RealPolynomialSymbolGroup v,
      F.realSymbolGradeQuotientHom v k P₀ ∈
        (NilpotentLieBCHGroup.realificationSubgroup
          (hnil := F.polynomialSymbol_lowerCentralSeries_eq_bot v)
          (F.symbolPointwiseSubalgebra b ω hF v U)).map (F.realSymbolGradeQuotientHom v k) ∧
      pull E * P₀ * pull R = El * Pl * Rl := by
  let pull := F.realSymbolHomogeneousPullbackHom b ω hF w v β hβ
  refine ⟨(pull E)⁻¹ * pull Z * (pull R)⁻¹,
    F.homogeneousPullback_residual_quotient_mem b ω hF w v β hβ U K hK E Z R k hx, ?_⟩
  rw [hlocal]
  change pull E * ((pull E)⁻¹ * pull Z * (pull R)⁻¹) * pull R = pull Z
  group

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.ActualOrdinaryPointwiseSpanning
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {ι κ γ L M : Type*} [LieRing L] [LieAlgebra ℚ L]
  [LieRing M] [LieAlgebra ℚ M] {s t : ℕ}
  (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M t)
  (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j)

variable (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
  (c : Basis κ ℚ M) (ν : κ → ℕ)
  (hG : ∀ j, G.layer j = Submodule.span ℚ (c '' {i | j ≤ ν i}))

theorem gradedImage_bounded_spanning [Fintype ι]
    (W : LieSubalgebra ℚ F.AssociatedGraded) (v : γ → F.AssociatedGraded)
    (hv : Submodule.span ℚ (Set.range v) = W.toSubmodule)
    (hW : BasisGradedSubmodule (F.associatedGradedBasis e ω hF) ω W.toSubmodule)
    {p : ℝ} (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p)
    (hvH : ∀ a i, rationalLogHeight ((F.associatedGradedBasis e ω hF).repr (v a) i) ≤ p)
    (hφH : ∀ i j, rationalLogHeight (c.repr (φ (e i)) j) ≤ p) :
    Submodule.span ℚ (Set.range (F.gradedImageSpanningFamily G φ hφ v)) =
      (W.map (F.associatedGradedMap G φ hφ)).toSubmodule ∧
    BasisGradedSubmodule (G.associatedGradedBasis c ν hG) ν
      (W.map (F.associatedGradedMap G φ hφ)).toSubmodule ∧
    ∀ a j, rationalLogHeight ((G.associatedGradedBasis c ν hG).repr
      (F.gradedImageSpanningFamily G φ hφ v a) j) ≤ (p + 2) ^ 4 := by
  exact ⟨F.gradedImageSpanningFamily_span G φ hφ W v hv,
    F.associatedGradedMap_image_graded G e ω hF c ν hG φ hφ W hW,
    F.gradedImageSpanningFamily_logHeight G φ hφ e ω hF c ν hG v hp hι hvH hφH⟩

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedCandidateCommonFastGeometry
namespace OAI

section

namespace Erdos3

open Module
open scoped Classical TensorProduct

namespace NilpotentLieFiltration

variable {ι κ γ L M : Type*} [Fintype ι] [Fintype κ] [Fintype γ]
    [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M] {s t : ℕ}
    (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M t)
    (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j)
    (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (c : Basis κ ℚ M) (ν : κ → ℕ)
    (hG : ∀ j, G.layer j = Submodule.span ℚ (c '' {i | j ≤ ν i}))
    (W : LieSubalgebra ℚ F.AssociatedGraded)
    (v : γ → F.AssociatedGraded)
    (hv : Submodule.span ℚ (Set.range v) = W.toSubmodule)
    (hW : BasisGradedSubmodule (F.associatedGradedBasis b ω hF) ω W.toSubmodule)

local notation "fast" => W.map (F.associatedGradedMap G φ hφ)
local notation "bg" => G.associatedGradedBasis c ν hG

include hv hW in

theorem exists_allocatedCandidateCommonFastGeometry
    {p : ℝ} (hp : 0 ≤ p)
    (hι : (Fintype.card ι : ℝ) ≤ p) (hκ : (Fintype.card κ : ℝ) ≤ p)
    (hγ : (Fintype.card γ : ℝ) ≤ p)
    (hvH : ∀ a i, rationalLogHeight ((F.associatedGradedBasis b ω hF).repr (v a) i) ≤ p)
    (hφH : ∀ i j, rationalLogHeight (c.repr (φ (b i)) j) ≤ p) :
    ∃ d : ℕ, d ≤ Fintype.card κ ∧
      ∃ (eQ : Basis (Fin d) ℚ (G.AssociatedGraded ⧸ (fast).toSubmodule))
        (lift : (G.AssociatedGraded ⧸ (fast).toSubmodule) →ₗ[ℚ] G.AssociatedGraded)
        (qS : ℕ),
        BasisGradedSubmodule bg ν (fast).toSubmodule ∧
        Function.RightInverse lift (fast).toSubmodule.mkQ ∧
        Function.RightInverse (lift.baseChange ℝ) ((fast).toSubmodule.mkQ.baseChange ℝ) ∧
        0 < qS ∧ (qS : ℝ) ≤ Real.exp (allocatedCandidateCommonFastGeometryLog p) ∧
        (∀ i j, |((bg).baseChange ℝ).repr
          (lift.baseChange ℝ ((eQ.baseChange ℝ) j)) i| ≤
            Real.exp (allocatedCandidateCommonFastGeometryLog p)) ∧
        (∀ j, (fun i => ((bg).baseChange ℝ).repr
          (lift.baseChange ℝ ((eQ.baseChange ℝ) j)) i) ∈ realDenominatorGrid qS) ∧
        (∀ j i, RationalHeightLE (((eQ.coord j).comp (fast).toSubmodule.mkQ) (bg i))
          (allocatedCandidateCommonFastCoordinateHeight p)) ∧
        1 ≤ allocatedCandidateCommonFastCoordinateHeight p ∧
        (allocatedCandidateCommonFastCoordinateHeight p : ℝ) ≤
          Real.exp (allocatedCandidateCommonFastGeometryLog p) := by
  classical
  obtain ⟨hspan, hfast, hheight⟩ :=
    F.gradedImage_bounded_spanning G φ hφ b ω hF c ν hG W v hv hW hp hι hvH hφH
  have hq0 := (allocatedCandidateCommonFastSectionInput_bounds hp).1
  have hpq := (allocatedCandidateCommonFastSectionInput_bounds hp).2
  obtain ⟨d, hd, eQ, lift, qS, hsection, hsectionR, hqS, hqSbound, hentry, hgrid, hθ⟩ :=
    exists_bounded_submodule_quotient_section_with_coordinates bg (fast).toSubmodule
      (F.gradedImageSpanningFamily G φ hφ v) hspan
      (one_le_ceil_exp ((p + 2) ^ 4))
      (fun i a => rationalHeightLE_ceil_exp (hheight a i))
      hq0 (hκ.trans hpq) (hγ.trans hpq)
      (ceil_exp_le_exp_add_one (by positivity : 0 ≤ (p + 2) ^ 4))
  refine ⟨d, hd, eQ, lift, qS, hfast, hsection, hsectionR, hqS, ?_, ?_, hgrid,
    hθ, allocatedCandidateCommonFastCoordinateHeight_bounds hp⟩
  · exact hqSbound.trans (Real.exp_le_exp.mpr (le_add_of_nonneg_right (by norm_num)))
  · intro i j
    apply (hentry i j).trans
    apply Real.exp_le_exp.mpr
    apply (pow_le_pow_right₀ (by linarith :
      1 ≤ allocatedCandidateCommonFastSectionInput p + 2) (by omega : 45 ≤ (47 : ℕ))).trans
    exact le_add_of_nonneg_right (by norm_num)

end NilpotentLieFiltration
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CommonRefilteredMappedOrbitFactors
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration
open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

theorem PolynomialSlowBound.to_symbol (w : σ → ℕ) (T : σ → ℝ) (M : ℝ)
    (g : (F.realification.adaptedPolynomialFiltration w).Group)
    (hg : F.PolynomialSlowBound b w T M g) :
    F.SymbolSlowBound b ω hF w T M (F.realPolynomialSymbolHom b ω hF w g) := by
  intro z
  change |((F.polynomialSymbolBasis b ω hF w).baseChange ℝ).repr
    (F.realSymbolOfPolynomial b ω hF w g.coord) z| ≤ _
  rw [F.realSymbolOfPolynomial_coordinate]
  exact hg z.val.1 z.val.2

theorem PolynomialRationalGrid.to_symbol (w : σ → ℕ) (l : ℕ)
    (g : (F.realification.adaptedPolynomialFiltration w).Group)
    (hg : F.PolynomialRationalGrid b w l g) :
    F.SymbolRationalGrid b ω hF w l (F.realPolynomialSymbolHom b ω hF w g) := by
  obtain ⟨a, ha⟩ := hg
  refine ⟨fun z => a z.val, ?_⟩
  funext z
  change (a z.val : ℝ) = (l : ℝ) *
    ((F.polynomialSymbolBasis b ω hF w).baseChange ℝ).repr
      (F.realSymbolOfPolynomial b ω hF w g.coord) z
  rw [F.realSymbolOfPolynomial_coordinate]
  exact congrFun ha z.val

theorem HasCommonRefilteredOrbitFactors.symbolFactors [Fintype σ] [Fintype ι]
    (T : σ → ℝ) (q : ℝ) (l : ℕ) (W : LieSubalgebra ℚ F.AssociatedGraded)
    (g : (F.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group)
    (h : F.HasCommonRefilteredOrbitFactors b ω hF T q l W g) :
    ∃ El Pl Rl : F.RealPolynomialSymbolGroup (fun _ : σ => 1),
      El * Pl * Rl = F.realPolynomialSymbolHom b ω hF (fun _ => 1) g ∧
      Pl.coord ∈ realificationLieSubalgebra
        (F.symbolPointwiseSubalgebra b ω hF (fun _ => 1) W) ∧
      F.SymbolSlowBound b ω hF (fun _ => 1) T (Real.exp q) El ∧
      F.SymbolRationalGrid b ω hF (fun _ => 1) l Rl := by
  obtain ⟨e, p, r, hprod, hmid, he, hr, _, _, _⟩ := h
  refine ⟨F.realPolynomialSymbolHom b ω hF (fun _ => 1) e,
    F.realPolynomialSymbolHom b ω hF (fun _ => 1) p,
    F.realPolynomialSymbolHom b ω hF (fun _ => 1) r, ?_, ?_, ?_, ?_⟩
  · simpa only [map_mul] using congrArg (F.realPolynomialSymbolHom b ω hF (fun _ => 1)) hprod
  · exact (F.mem_real_symbolPointwiseSubalgebra_iff_values b ω hF (fun _ => 1) W _).mpr hmid
  · exact he.to_symbol F b ω hF (fun _ => 1) T (Real.exp q) e
  · exact hr.to_symbol F b ω hF (fun _ => 1) l r

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι κ L M : Type*} [Fintype ι] [Fintype κ]
    [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M] {s t : ℕ}
    (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M t)
    (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (c : Basis κ ℚ M) (ν : κ → ℕ)
    (hG : ∀ j, G.layer j = Submodule.span ℚ (c '' {i | j ≤ ν i}))
    (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j)

theorem realPolynomialGroupMap_coefficient (w : σ → ℕ)
    (g : (F.realification.adaptedPolynomialFiltration w).Group) (α : σ →₀ ℕ) :
    coefficients ((F.realPolynomialGroupMap G φ hφ w g).coord :
      VectorPolynomial σ ℚ (ℝ ⊗[ℚ] M)) α =
      realificationLieHom φ (coefficients
        (g.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) α) := by
  rw [F.realPolynomialGroupMap_log, coefficients_map]
  rfl

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.NativeMarkedPolynomialFreezing
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration
open Module NilpotentLieBCHGroup
open scoped TensorProduct
variable {σ L M : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s t : ℕ}
    (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M t)

variable (w : σ → ℕ)

noncomputable def frozenMarkedRight (S : M →ₗ[ℚ] L)
    (hS : ∀ j, ∀ y ∈ G.layer j, S y ∈ F.layer j)
    (RF : (G.realification.adaptedPolynomialFiltration w).Group)
    (kR : F.realification.Group) :
    (F.realification.adaptedPolynomialFiltration w).Group :=
  F.filteredRealPolynomialSection G w S hS RF *
    F.realification.adaptedConstantGroupHom w kR

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeFrozenMarkedLocalMark
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ κ L M : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s t : ℕ}
    (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M t)

theorem exists_formal_marked_orbit_restoration
    (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j)
    (c : Basis κ ℚ M) (v : κ → ℕ)
    (hG : ∀ j, G.layer j = Submodule.span ℚ (c '' {k | j ≤ v k}))
    (hsurj : ∀ j, ∀ y ∈ G.layer j, ∃ x ∈ F.layer j, φ x = y)
    (w : σ → ℕ) (g : F.realification.PolynomialOrbit w)
    (q : G.realification.PolynomialOrbit w) :
    ∃ restored : F.realification.PolynomialOrbit w,
      map ((realificationLieHom φ).toLinearMap.restrictScalars ℚ) restored.log = q.log ∧
      (∀ z : σ → ℝ, NilpotentLieBCHGroup.realificationMap
        (hnil := F.lowerCentralSeries_eq_bot) (hM := G.lowerCentralSeries_eq_bot) φ
          (F.realification.polynomialOrbitRealEval w z restored) =
            G.realification.polynomialOrbitRealEval w z q) ∧
      ∀ z : σ → ℝ, NilpotentLieBCHGroup.realificationMap
        (hnil := F.lowerCentralSeries_eq_bot) (hM := G.lowerCentralSeries_eq_bot) φ
          (F.realification.polynomialOrbitRealEval w z g) =
            G.realification.polynomialOrbitRealEval w z q →
        F.realification.polynomialOrbitRealEval w z restored =
          F.realification.polynomialOrbitRealEval w z g := by
  obtain ⟨S, hS, hSlayer⟩ := F.exists_filtered_linear_section G c v hG φ.toLinearMap hsurj
  let P := sectionCorrectedPolynomial φ.toLinearMap S g.log q.log
  have hP : F.realification.Adapted w P := by
    apply (F.realification.adapted_iff_coefficients w P).mpr
    intro a
    rw [show P = sectionCorrectedPolynomial φ.toLinearMap S g.log q.log from rfl,
      sectionCorrectedPolynomial_coefficients]
    apply Submodule.sub_mem
    · exact (F.realification.adapted_iff_coefficients w g.log).mp g.adapted a
    · apply baseChange_mem_of_mapsTo (G.layer (Finsupp.weight w a))
        (F.layer (Finsupp.weight w a)) S (hSlayer _)
      apply Submodule.sub_mem
      · exact F.realificationLieHom_mem_layer G φ hφ _ _
          ((F.realification.adapted_iff_coefficients w g.log).mp g.adapted a)
      · exact (G.realification.adapted_iff_coefficients w q.log).mp q.adapted a
  let restored := polynomialOrbitOfLog P hP
  have hm : map ((realificationLieHom φ).toLinearMap.restrictScalars ℚ) restored.log = q.log :=
    sectionCorrectedPolynomial_map φ.toLinearMap S hS g.log q.log
  refine ⟨restored, hm, ?_, ?_⟩
  · intro z
    apply NilpotentLieBCHGroup.ext
    change realificationLieHom φ (eval₂ z P) = eval₂ z q.log
    rw [← hm]
    exact (eval₂_map (realificationLieHom φ).toLinearMap z P).symm
  · intro z hz
    have hc := congrArg NilpotentLieBCHGroup.coord hz
    change φ.toLinearMap.baseChange ℝ (eval₂ z g.log) = eval₂ z q.log at hc
    apply NilpotentLieBCHGroup.ext
    change eval₂ z P = eval₂ z g.log
    dsimp only [P, sectionCorrectedPolynomial]
    rw [map_sub, eval₂_map, map_sub, eval₂_map, hc, sub_self, map_zero, sub_zero]

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L]

theorem externalCandidate_stepZero_group_eq_one (F : NilpotentLieFiltration L 0)
    (g : F.Group) : g = 1 := by
  apply NilpotentLieBCHGroup.ext
  exact F.externalCandidate_stepZero_coord_eq_zero g.coord

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ControlledPrescribedMarkedNativeFactorization
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped Matrix TensorProduct NNReal

variable {σ ι κ L M : Type*} [LieRing L] [LieAlgebra ℚ L]
  [LieRing M] [LieAlgebra ℚ M] {s : ℕ}
  (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M s)
  (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (c : Basis κ ℚ M) (ν : κ → ℕ)
  (hG : ∀ j, G.layer j = Submodule.span ℚ (c '' {i | j ≤ ν i}))
  (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j)
  (w : σ → ℕ)
  [Fintype (SymbolBasisIndex w ω)] [Fintype (SymbolBasisIndex w ν)]

theorem realFilteredSymbolGroupMap_slow
    {H : ℕ} (hH : 1 ≤ H)
    (hentries : ∀ i j, RationalHeightLE (c.repr (φ (b j)) i) H)
    (T : σ → ℝ) (hT : ∀ i, 0 < T i) {A : ℝ} (hA : 0 ≤ A)
    (g : F.RealPolynomialSymbolGroup w)
    (hg : F.SymbolSlowBound b ω hF w T A g) :
    G.SymbolSlowBound c ν hG w T
      (((Fintype.card (SymbolBasisIndex w ω) : ℝ) + 1) * (H + 1) * A)
      (F.realFilteredSymbolGroupMap G φ hφ w g) := by
  classical
  let B := F.polynomialSymbolBasis b ω hF w
  let C := G.polynomialSymbolBasis c ν hG w
  let ψ := (F.filteredPolynomialSymbolMap G φ hφ w).toLinearMap
  let D := LinearMap.toMatrix B C ψ
  have hblock : ∀ i j, i.val.1 ≠ j.val.1 → D i j = 0 := by
    intro i j hij
    simpa only [D, B, C, ψ, LinearMap.toMatrix_apply, LieHom.coe_toLinearMap] using
      F.filteredPolynomialSymbolMap_monomial_blocks G b ω hF c ν hG φ hφ w j i hij
  have hheight : ∀ i j, RationalHeightLE (D i j) H := by
    intro i j
    simpa only [D, B, C, ψ, LinearMap.toMatrix_apply, LieHom.coe_toLinearMap] using
      F.filteredPolynomialSymbolMap_basis_height G b ω hF c ν hG φ hφ w hH hentries j i
  intro i
  have h := rational_coordinate_map_weighted (B.baseChange ℝ) (C.baseChange ℝ)
    (ψ.baseChange ℝ) D (realified_linear_coordinate_matrix B C ψ)
    (fun j => j.val.1) (fun j => j.val.1) hblock (H : ℝ≥0)
    (fun i j => by exact_mod_cast (hheight i j).1)
    (monomialScale T) (monomialScale_pos T hT) hA g.coord hg i
  exact h

theorem realFilteredSymbolGroupMap_slow_exp
    {H : ℕ} (hH : 1 ≤ H)
    (hentries : ∀ i j, RationalHeightLE (c.repr (φ (b j)) i) H)
    {p : ℝ} (hp : 0 ≤ p)
    (hdim : (Fintype.card (SymbolBasisIndex w ω) : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p)
    (T : σ → ℝ) (hT : ∀ i, 0 < T i) {A : ℝ} (hA : 0 ≤ A)
    (g : F.RealPolynomialSymbolGroup w)
    (hg : F.SymbolSlowBound b ω hF w T A g) :
    G.SymbolSlowBound c ν hG w T (Real.exp ((p + 2) ^ 3) * A)
      (F.realFilteredSymbolGroupMap G φ hφ w g) := by
  have hbound := F.realFilteredSymbolGroupMap_slow G b ω hF c ν hG φ hφ w
    hH hentries T hT hA g hg
  have hfac : ((Fintype.card (SymbolBasisIndex w ω) : ℝ) + 1) * (H + 1) ≤
      Real.exp ((p + 2) ^ 3) := by
    apply le_trans _ (matrix_weighted_factor_le_exp_power _ hp hdim 1 (by omega))
    gcongr
    exact hHp.trans (Real.exp_le_exp.mpr (by simp))
  intro i
  exact (hbound i).trans (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right hfac hA) (monomialScale_pos T hT _).le)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration
open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι κ L M : Type*}
    [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M] {s : ℕ}
    (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M s)
    (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (c : Basis κ ℚ M) (ν : κ → ℕ)
    (hG : ∀ j, G.layer j = Submodule.span ℚ (c '' {i | j ≤ ν i}))
    (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j)

theorem realFilteredSymbolGroupMap_symbol [Fintype σ] [Fintype ι] [Fintype κ] (w : σ → ℕ)
    (g : (F.realification.adaptedPolynomialFiltration w).Group) :
    F.realFilteredSymbolGroupMap G φ hφ w (F.realPolynomialSymbolHom b ω hF w g) =
      G.realPolynomialSymbolHom c ν hG w (F.realPolynomialGroupMap G φ hφ w g) := by
  apply NilpotentLieBCHGroup.ext
  exact F.realFilteredPolynomialSymbolMap_polynomial G φ hφ b ω hF c ν hG w g.coord

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.GlobalMarkedOuterNormalization
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial _root_.MvPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}

structure GlobalMarkedNativeFactors
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (w : σ → ℕ) (W : LieSubalgebra ℚ F.AssociatedGraded)
    (g : (F.realification.adaptedPolynomialFiltration w).Group)
    (E R : F.RealPolynomialSymbolGroup w) where
  left : (F.realification.adaptedPolynomialFiltration w).Group
  middle : (F.realification.adaptedPolynomialFiltration w).Group
  right : (F.realification.adaptedPolynomialFiltration w).Group
  markedMiddle : (F.gradedRefiltration W).realification.PolynomialOrbit w
  product : left * middle * right = g
  left_symbol : F.realPolynomialSymbolHom b ω hF w left = E
  right_symbol : F.realPolynomialSymbolHom b ω hF w right = R
  constant_second : coefficients (middle.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 ∈
    F.realification.layer 2
  middle_log : VectorPolynomial.map
    (realLieHomToRat (realificationLieHom (F.gradedRefiltrationSubalgebra W).incl)).toLinearMap
    markedMiddle.log = (middle.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))

variable (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (w : σ → ℕ) (W : LieSubalgebra ℚ F.AssociatedGraded)
  (g : (F.realification.adaptedPolynomialFiltration w).Group)
  (E R : F.RealPolynomialSymbolGroup w)

namespace GlobalMarkedNativeFactors
variable {F b ω hF w W g E R}
  (A : GlobalMarkedNativeFactors F b ω hF w W g E R)

theorem middle_values (t : σ → ℝ) :
    NilpotentLieBCHGroup.realificationMap
      (hnil := (F.gradedRefiltration W).lowerCentralSeries_eq_bot)
      (hM := F.lowerCentralSeries_eq_bot) (F.gradedRefiltrationSubalgebra W).incl
      ((F.gradedRefiltration W).realification.polynomialOrbitRealEval w t A.markedMiddle) =
        F.adaptedPolynomialRealValueHom w t A.middle :=
  F.native_refiltered_orbit_real_value W w A.markedMiddle _ A.middle_log t

end GlobalMarkedNativeFactors
end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (w : σ → ℕ) (W : LieSubalgebra ℚ F.AssociatedGraded)

theorem exists_globalMarkedNativeFactors_of_outer_lifts [Fintype ι]
    (hw : ∀ i, 0 < w i)
    (g e₀ r₀ : (F.realification.adaptedPolynomialFiltration w).Group)
    (E R : F.RealPolynomialSymbolGroup w)
    (he : F.realPolynomialSymbolHom b ω hF w e₀ = E)
    (hr : F.realPolynomialSymbolHom b ω hF w r₀ = R)
    (hfast : (E⁻¹ * F.realPolynomialSymbolHom b ω hF w g * R⁻¹).coord ∈
      realificationLieSubalgebra (F.symbolPointwiseSubalgebra b ω hF w W)) :
    ∃ (a : ℝ ⊗[ℚ] L) (v : L) (A : GlobalMarkedNativeFactors F b ω hF w W g E R),
      (∀ i, 0 ≤ (b.baseChange ℝ).repr a i ∧ (b.baseChange ℝ).repr a i < 1) ∧
      (∀ i, ∃ z : ℤ, b.repr v i = z) ∧
      A.left = e₀ * F.realification.adaptedConstantGroupHom w ⟨a⟩ ∧
      A.right = F.realification.adaptedConstantGroupHom w ⟨(1 : ℝ) ⊗ₜ[ℚ] v⟩ * r₀ := by
  obtain ⟨a, v, e, middle, r, ha, hv, he', hr', hprod, hesym, hp, hrsym, hc⟩ :=
    F.exists_fractional_integral_polynomial_normalization b ω hF w
      e₀ (e₀⁻¹ * g * r₀⁻¹) r₀
  have hprod' : e * middle * r = g := hprod.trans (by group)
  have hpfast : (F.realPolynomialSymbolHom b ω hF w middle).coord ∈
      realificationLieSubalgebra (F.symbolPointwiseSubalgebra b ω hF w W) := by
    rw [hp, map_mul, map_mul, map_inv, map_inv, he, hr]
    exact hfast
  rw [F.realPolynomialSymbolHom_coord] at hpfast
  have hfirst := Submodule.baseChange_mono ℝ
    (F.layer_succ_le_gradedRefiltrationLayer W 1) hc
  obtain ⟨q, hq, _⟩ := F.exists_native_pointwise_refiltered_orbit_of_constant W
    b ω hF w hw middle.coord hfirst
    ((F.mem_real_symbolPointwiseSubalgebra_iff_values b ω hF w W _).mp hpfast)
  exact ⟨a, v, ⟨e, middle, r, q, hprod', hesym.trans he, hrsym.trans hr, hc, hq⟩,
    ha, hv, he', hr'⟩

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.HomogeneousComponentTopSubstitution
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial

variable {σ τ R : Type*} [CommRing R]

theorem weightedTop_aeval (w : σ → ℕ) (v : τ → ℕ)
    (β : σ → MvPolynomial τ R)
    (hβ : ∀ i, β i ∈ weightedSupportLE v (w i))
    (p : MvPolynomial σ R) (n : ℕ) (hp : p ∈ weightedSupportLE w n) :
    weightedHomogeneousComponent v n (aeval β p) =
      aeval (fun i => weightedHomogeneousComponent v (w i) (β i))
        (weightedHomogeneousComponent w n p) := by
  classical
  let top : σ → MvPolynomial τ R :=
    fun i => weightedHomogeneousComponent v (w i) (β i)
  have hdiff : aeval β p - aeval top p ∈ weightedSupportLT v n := by
    apply weightedComparison_difference w v (aeval β) (aeval top) _ _ _ hp
    · intro i
      simpa only [aeval_X] using hβ i
    · intro i
      simpa only [aeval_X, top] using weightedTopPart_preserves_degree v v (w i) (hβ i)
    · intro i
      simpa only [aeval_X, top] using weightedTopPart_remainder_lt v (hβ i)
  have hzero : weightedHomogeneousComponent v n (aeval β p - aeval top p) = 0 := by
    ext α
    rw [coeff_weightedHomogeneousComponent, MvPolynomial.coeff_zero]
    split_ifs with hα
    · by_contra hc
      have hlt := hdiff (mem_support_iff.mpr hc)
      change Finsupp.weight v α < n at hlt
      omega
    · rfl
  rw [map_sub, sub_eq_zero] at hzero
  exact hzero.trans (aeval_weightedHomogeneousComponent w v top
    (fun i => weightedHomogeneousComponent_isWeightedHomogeneous _ _) n p).symm

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedLayerFreezing
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial

namespace PolynomialPatch.LowestLayerModel

variable {σ : Type*} {s D E h : ℕ} {A : PolynomialPatch σ s (D + E)}
    (L : A.LowestLayerModel h)

noncomputable def integerChange : Matrix (Fin D) (Fin D) ℤ :=
  triangularReductionMatrix (1 - L.matrix)

end PolynomialPatch.LowestLayerModel
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.BufferedSampledCurrentGradePhase
namespace OAI

section

namespace Erdos3
open _root_.MvPolynomial _root_.OAI.MvPolynomial
section ScalarTop
variable {σ τ R : Type*} [CommRing R]

theorem sampledTopPhase_remainder (w : σ → ℕ) (v : τ → ℕ)
    (β : σ → MvPolynomial τ R)
    (hβ : ∀ i, β i ∈ weightedSupportLE v (w i))
    {P : MvPolynomial σ R} {k : ℕ}
    (hP : P.IsWeightedHomogeneous w k) :
    aeval β P - aeval (fun i => weightedHomogeneousComponent v (w i) (β i)) P ∈
      weightedSupportLT v k := by
  apply weightedComparison_difference w v
    (aeval β) (aeval (fun i => weightedHomogeneousComponent v (w i) (β i)))
  · intro i
    simpa only [aeval_X] using hβ i
  · intro i
    simpa only [aeval_X] using weightedTopPart_preserves_degree v v (w i) (hβ i)
  · intro i
    simpa only [aeval_X] using weightedTopPart_remainder_lt v (hβ i)
  · exact fun _ ha => (hP (mem_support_iff.mp ha)).le

theorem sampledTopPhase_remainder_totalDegree (w : σ → ℕ)
    (β : σ → MvPolynomial τ R)
    (hβ : ∀ i, β i ∈ weightedSupportLE (fun _ : τ => 1) (w i))
    {P : MvPolynomial σ R} {n : ℕ}
    (hP : P.IsWeightedHomogeneous w (n + 1)) :
    (aeval β P - aeval (fun i => homogeneousComponent (w i) (β i)) P).totalDegree ≤ n := by
  apply (mem_weightedSupportLE_one_iff _ _).mp
  exact weightedSupportLT_succ_le
    (sampledTopPhase_remainder w (fun _ : τ => 1) β hβ hP)

end ScalarTop

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.AllocatedRecoveredNormalizedTopChart
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial _root_.OAI.MvPolynomial

theorem normalizedRealPolynomialChart_top_inr
    {X Tags K : Type*} (weight : Tags → ℕ) (N : X → ℝ)
    (poly : Tags → MvPolynomial X ℝ)
    (hp : ∀ i, poly i ∈ weightedSupportLE (fun _ : X => 1) (weight i))
    (β : X ⊕ Tags → MvPolynomial K ℝ)
    (hβ : ∀ z, β z ∈ weightedSupportLE (fun _ : K => 1)
      (Sum.elim (fun _ : X => 1) weight z)) (i : Tags) :
    aeval (fun z => homogeneousComponent (Sum.elim (fun _ : X => 1) weight z) (β z))
        (normalizedRealPolynomialChart N (fun i => homogeneousComponent (weight i) (poly i))
          (Sum.inr i)) =
      homogeneousComponent (weight i) (β (Sum.inr i) - aeval (fun x => β (Sum.inl x)) (poly i)) := by
  rw [normalizedRealPolynomialChart_inr, map_sub, aeval_X, aeval_rename, map_sub]
  congr 1
  exact (weightedTop_aeval (fun _ : X => 1) (fun _ : K => 1)
    (fun x => β (Sum.inl x)) (fun x => hβ (Sum.inl x)) (poly i) (weight i) (hp i)).symm

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.SymbolCoordinateFreezeBounds
namespace OAI

section

namespace Erdos3
open _root_.MvPolynomial _root_.OAI.MvPolynomial

variable {I R : Type*} [CommRing R]

theorem coeff_freezePolynomial_zero (keep : I → Prop) (P : MvPolynomial I R)
    (α : {i // keep i} →₀ ℕ) :
    (freezePolynomial keep (0 : {i // ¬keep i} → R) P).coeff α =
      P.coeff (α.mapDomain Subtype.val) := by
  rw [freezePolynomial_zero_eq_killCompl]
  exact MvPolynomial.coeff_killCompl Subtype.val_injective

theorem coeff_aeval_frozenCoordinate_zero (keep : I → Prop) (P : MvPolynomial I R)
    (α : {i // keep i} →₀ ℕ) :
    (aeval (frozenCoordinate keep (0 : {i // ¬keep i} → R)) P).coeff α =
      P.coeff (α.mapDomain Subtype.val) :=
  coeff_freezePolynomial_zero keep P α

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.CommonRefilteredFactorsSymbolTransport
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped Classical

variable {σ R : Type*} [CommRing R]

theorem nestedFrozenCoordinate_support
    (keepLong keepLater : σ → Prop)
    (fixed : {i : {i // keepLong i} // ¬keepLater i.val} → R)
    (i : {i // keepLong i}) :
    nestedFrozenCoordinate keepLong keepLater fixed i ∈ weightedSupportLE (fun _ : {i : σ // keepLater i} => 1) 1 := by
  by_cases hi : keepLater i.val
  · simp only [nestedFrozenCoordinate, dif_pos hi]
    exact weightedSupportLE_X (R := R) (fun _ : {i : σ // keepLater i} => 1) ⟨i.val, hi⟩
  · simp only [nestedFrozenCoordinate, dif_neg hi]
    exact weightedSupportLE_C (fun _ : {i : σ // keepLater i} => 1) 1 (fixed ⟨i, hi⟩)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.GlobalMarkedChartwiseNormalization
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial _root_.MvPolynomial
open scoped TensorProduct

attribute [local irreducible] weightedAdaptedRealChartHom realChartSubstitute

variable {σ τ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

theorem weightedAdaptedRealChartHom_constant
    (w : σ → ℕ) (v : τ → ℕ) (γ : σ → MvPolynomial τ ℝ)
    (hγ : ∀ i, γ i ∈ weightedSupportLE v (w i)) (a : F.realification.Group) :
    F.weightedAdaptedRealChartHom w v γ hγ (F.realification.adaptedConstantGroupHom w a) =
      F.realification.adaptedConstantGroupHom v a := by
  apply NilpotentLieBCHGroup.ext
  apply Subtype.ext
  rw [F.weightedAdaptedRealChartHom_coord, F.realification.adaptedConstantGroupHom_log,
    F.realification.adaptedConstantGroupHom_log]
  apply sub_eq_zero.mp
  apply eq_zero_of_eval₂_zero (K := ℝ)
  intro t
  simp only [map_sub, eval₂_realChartSubstitute, VectorPolynomial.eval₂_monomial,
    Finsupp.prod_zero_index, one_smul, sub_self]

theorem exists_chartwise_controlled_globalMarkedNativeFactors (s a : ℕ) :
    ∃ Ce Cr : ℕ, 2 ≤ Ce ∧ 2 ≤ Cr ∧
    ∀ {σ ι L : Type*} [Fintype σ] [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
      (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
      (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (w : σ → ℕ), (∀ i, 0 < w i) →
      ∀ (H l : ℕ) (p : ℝ), 1 ≤ H → 0 < l → 0 ≤ p →
      (Fintype.card ι : ℝ) ≤ p → (Fintype.card σ : ℝ) ≤ p →
      (H : ℝ) ≤ Real.exp p → (l : ℝ) ≤ Real.exp p →
      (∀ i j k, RationalHeightLE (b.repr ⁅b i, b j⁆ k) H) →
      ∃ n : ℕ, 0 < n ∧ (n : ℝ) ≤ Real.exp ((p + Cr) ^ Cr) ∧ l ∣ n ∧
      ∀ (W : LieSubalgebra ℚ F.AssociatedGraded)
        (g e₀ r₀ : (F.realification.adaptedPolynomialFiltration w).Group)
        (E R : F.RealPolynomialSymbolGroup w),
      F.realPolynomialSymbolHom b ω hF w e₀ = E →
      F.realPolynomialSymbolHom b ω hF w r₀ = R →
      (E⁻¹ * F.realPolynomialSymbolHom b ω hF w g * R⁻¹).coord ∈
        realificationLieSubalgebra (F.symbolPointwiseSubalgebra b ω hF w W) →
      F.PolynomialRationalGrid b w l r₀ →
      ∃ A : GlobalMarkedNativeFactors F b ω hF w W g E R,
        F.PolynomialRationalGrid b w n A.right ∧
        ∀ {τ : Type*} [Fintype τ] (v : τ → ℕ), (∀ i, 0 < v i) →
          (Fintype.card τ : ℝ) ≤ p →
          ∀ (γ : σ → MvPolynomial τ ℝ)
            (hγ : ∀ i, γ i ∈ weightedSupportLE v (w i))
            (T : τ → ℝ), (∀ i, 0 < T i) →
          F.PolynomialSlowBound b v T (Real.exp ((p + 2) ^ a))
            (F.weightedAdaptedRealChartHom w v γ hγ e₀) →
          F.PolynomialSlowBound b v T (Real.exp ((p + Ce) ^ Ce))
            (F.weightedAdaptedRealChartHom w v γ hγ A.left) := by
  obtain ⟨Ce, hCe, hslow⟩ := exists_polynomial_slow_product_bound s a 2
  obtain ⟨Cr, hCr, hrat⟩ := exists_polynomial_rational_product_bound s 2
  refine ⟨Ce, Cr, hCe, hCr, ?_⟩
  intro σ ι L _ _ _ _ F b ω hF w hw H l p hH hl hp hι hσ hHp hlp hbracket
  obtain ⟨n, hn, hnp, hln, hproduct⟩ :=
    hrat F b ω hF w hw H p hH hp hι hσ hHp hbracket l hl hlp
  refine ⟨n, hn, hnp, hln, ?_⟩
  intro W g e₀ r₀ E R he hr hfast hrGrid
  obtain ⟨u, z, A, hu, hz, hleft, hright⟩ :=
    F.exists_globalMarkedNativeFactors_of_outer_lifts b ω hF w W hw g e₀ r₀ E R he hr hfast
  have hzGrid : (fun i => (b.baseChange ℝ).repr ((1 : ℝ) ⊗ₜ[ℚ] z) i) ∈
      realDenominatorGrid 1 := by
    classical
    choose k hk using hz
    refine ⟨k, ?_⟩
    funext i
    change (k i : ℝ) = (1 : ℕ) * (b.baseChange ℝ).repr ((1 : ℝ) ⊗ₜ[ℚ] z) i
    rw [Basis.baseChange_repr_tmul (S := ℝ), hk]
    simp only [Rat.smul_def, Rat.cast_intCast, mul_one, Nat.cast_one, one_mul]
  have hzPolynomial := F.polynomialRationalGrid_constant b w 1
    (⟨(1 : ℝ) ⊗ₜ[ℚ] z⟩ : F.realification.Group) hzGrid
  have hzPolynomial' := F.polynomialRationalGrid_of_dvd b w
    (by decide : 0 < 1) (one_dvd l) _ hzPolynomial
  have hrFinal := hproduct
    [F.realification.adaptedConstantGroupHom w ⟨(1 : ℝ) ⊗ₜ[ℚ] z⟩, r₀] (by simp)
    (by
      intro t ht
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl
      · exact hzPolynomial'
      · exact hrGrid)
  refine ⟨A, ?_, ?_⟩
  · simpa only [List.prod_cons, List.prod_nil, mul_one, ← hright] using hrFinal
  · intro τ _ v hv hτ γ hγ T hT heSlow
    have huBound : ∀ i, |(b.baseChange ℝ).repr u i| ≤ Real.exp ((p + 2) ^ a) := by
      intro i
      rw [abs_of_nonneg (hu i).1]
      exact (hu i).2.le.trans (Real.one_le_exp (by positivity))
    have huSlow := F.polynomialSlowBound_constant b v T hT (Real.exp_nonneg _)
      (⟨u⟩ : F.realification.Group) huBound
    have heFinal := hslow F b ω hF v hv H p hH hp hι hτ hHp hbracket T hT
      [F.weightedAdaptedRealChartHom w v γ hγ e₀,
        F.realification.adaptedConstantGroupHom v ⟨u⟩] (by simp)
      (by
        intro t ht
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
        rcases ht with rfl | rfl
        · exact heSlow
        · exact huSlow)
    rw [hleft, map_mul, F.weightedAdaptedRealChartHom_constant]
    simpa only [List.prod_cons, List.prod_nil, mul_one] using heFinal

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.MarkedPolynomialSectionSlow
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration
open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

variable {σ ι κ L M : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s t : ℕ}
    (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M t)
    (b : Basis ι ℚ L) (c : Basis κ ℚ M) (w : σ → ℕ)

theorem polynomialSlowBound_filteredRealPolynomialSection [Fintype κ]
    (S : M →ₗ[ℚ] L) (hS : ∀ j, ∀ y ∈ G.layer j, S y ∈ F.layer j)
    (T : σ → ℝ) (hT : ∀ i, 0 < T i) {A B : ℝ} (hA : 0 ≤ A)
    (hB : ∀ i j, |(b.baseChange ℝ).repr (S.baseChange ℝ ((c.baseChange ℝ) j)) i| ≤ B)
    (g : (G.realification.adaptedPolynomialFiltration w).Group)
    (hg : G.PolynomialSlowBound c w T A g) :
    F.PolynomialSlowBound b w T ((Fintype.card κ : ℝ) * B * A)
      (F.filteredRealPolynomialSection G w S hS g) := by
  intro α i
  change |(b.baseChange ℝ).repr (coefficients (map ((S.baseChange ℝ).restrictScalars ℚ)
    (g.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] M))) α) i| ≤ _
  rw [coefficients_map]
  exact (linearMap_abs_repr_le (c.baseChange ℝ) (b.baseChange ℝ) (S.baseChange ℝ)
    (div_nonneg hA (monomialScale_pos T hT α).le) hB _ (hg α) i).trans
    (le_of_eq (by ring))

theorem polynomialSlowBound_filteredRealPolynomialSection_exp [Fintype κ]
    (S : M →ₗ[ℚ] L) (hS : ∀ j, ∀ y ∈ G.layer j, S y ∈ F.layer j)
    (T : σ → ℝ) (hT : ∀ i, 0 < T i) (a : ℕ) (p : ℝ) (hp : 0 ≤ p)
    (hκ : (Fintype.card κ : ℝ) ≤ p)
    (hB : ∀ i j, |(b.baseChange ℝ).repr (S.baseChange ℝ ((c.baseChange ℝ) j)) i| ≤
      Real.exp ((p + 2) ^ a))
    (g : (G.realification.adaptedPolynomialFiltration w).Group)
    (hg : G.PolynomialSlowBound c w T (Real.exp ((p + 2) ^ a)) g) :
    F.PolynomialSlowBound b w T (Real.exp ((p + 2) ^ (a + 2)))
      (F.filteredRealPolynomialSection G w S hS g) := by
  exact F.polynomialSlowBound_mono b w T hT
    (section_exponential_budget a hp hκ) _
    (F.polynomialSlowBound_filteredRealPolynomialSection G b c w S hS T hT
      (Real.exp_nonneg _) hB g hg)

theorem exists_marked_polynomial_kernel_slow_bound (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {σ ι κ L M : Type*} [Fintype σ] [Fintype ι] [Fintype κ]
      [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M] {t : ℕ}
      (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M t)
      (b : Basis ι ℚ L) (c : Basis κ ℚ M) (ω : ι → ℕ)
      (_hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (w : σ → ℕ), (∀ i, 0 < w i) →
      ∀ (H : ℕ) (p : ℝ), 1 ≤ H → 0 ≤ p →
      (Fintype.card ι : ℝ) ≤ p → (Fintype.card κ : ℝ) ≤ p →
      (Fintype.card σ : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p →
      (∀ i j z, RationalHeightLE (b.repr ⁅b i, b j⁆ z) H) →
      ∀ (S : M →ₗ[ℚ] L) (hS : ∀ j, ∀ y ∈ G.layer j, S y ∈ F.layer j),
      (∀ i j, |(b.baseChange ℝ).repr (S.baseChange ℝ ((c.baseChange ℝ) j)) i| ≤
        Real.exp ((p + 2) ^ a)) →
      ∀ T : σ → ℝ, (∀ i, 0 < T i) →
      ∀ (E : (F.realification.adaptedPolynomialFiltration w).Group)
        (EF : (G.realification.adaptedPolynomialFiltration w).Group),
      F.PolynomialSlowBound b w T (Real.exp ((p + 2) ^ a)) E →
      G.PolynomialSlowBound c w T (Real.exp ((p + 2) ^ a)) EF →
      F.PolynomialSlowBound b w T (Real.exp ((p + C) ^ C))
        (E * (F.filteredRealPolynomialSection G w S hS EF)⁻¹) ∧
      F.PolynomialSlowBound b w T (Real.exp ((p + C) ^ C))
        ((F.filteredRealPolynomialSection G w S hS EF)⁻¹ * E) := by
  obtain ⟨C, hC, hprod⟩ := exists_polynomial_slow_product_bound s (a + 2) 2
  refine ⟨C, hC, ?_⟩
  intro σ ι κ L M _ _ _ _ _ _ _ t F G b c ω hF w hw H p hH hp hι hκ hσ hHp hb
    S hS hB T hT E EF hE hEF
  let V := F.filteredRealPolynomialSection G w S hS EF
  have hV : F.PolynomialSlowBound b w T (Real.exp ((p + 2) ^ (a + 2))) V :=
    F.polynomialSlowBound_filteredRealPolynomialSection_exp G b c w S hS T hT a p hp hκ hB EF hEF
  have hVi := (F.polynomialSlowBound_inv_iff b w T _ V).mpr hV
  have hE' : F.PolynomialSlowBound b w T (Real.exp ((p + 2) ^ (a + 2))) E :=
    F.polynomialSlowBound_mono b w T hT (Real.exp_le_exp.mpr
      (pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ p + 2) (by omega : a ≤ a + 2))) E hE
  have hleft := hprod F b ω hF w hw H p hH hp hι hσ hHp hb T hT [E, V⁻¹]
    (by simp) (by
      intro r hr
      rcases List.mem_cons.mp hr with rfl | hr
      · exact hE'
      · have heq := List.mem_singleton.mp hr
        simpa only [heq] using hVi)
  have hright := hprod F b ω hF w hw H p hH hp hι hσ hHp hb T hT [V⁻¹, E]
    (by simp) (by
      intro r hr
      rcases List.mem_cons.mp hr with rfl | hr
      · exact hVi
      · have heq := List.mem_singleton.mp hr
        simpa only [heq] using hE')
  exact ⟨by simpa only [List.prod_cons, List.prod_nil, mul_one] using hleft,
    by simpa only [List.prod_cons, List.prod_nil, mul_one] using hright⟩

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.ActualMarkedSlowKernelCells
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal

variable {σ ι L G : Type*} [Fintype σ] [DecidableEq σ] [Fintype ι] [DecidableEq ι]
  [LieRing L] [LieAlgebra ℚ L]
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)] [_root_.Group G] {s : ℕ}

theorem exists_slow_kernel_cells
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (w : σ → ℕ)
    (hw : ∀ i, 0 < w i) (π : F.realification.Group →* G)
    (H : ℕ) (hc : ∀ i j k, RationalHeightLE (lieStructureConstants b i j k) H)
    (T : σ → ℝ) (hT : ∀ i, 0 < T i) {A : ℝ} (hA : 0 ≤ A)
    (B : ℝ≥0) (hB : 1 ≤ B)
    (hAB : ((s : ℝ) + 1) * ((Fintype.card σ : ℝ) + 1) ^ s * A ≤ B)
    {ε p : ℝ} (hε : 0 < ε) (hp : 0 ≤ p)
    (hd : (Fintype.card ι : ℝ) ≤ p) (hn : (Fintype.card σ : ℝ) ≤ p)
    (hBp : (B : ℝ) ≤ Real.exp p)
    (hK : (bchBoxMetricConstant s (Fintype.card ι) H B : ℝ) ≤ Real.exp p)
    (hmove : (bchBoxMetricConstant s (Fintype.card ι) H B : ℝ) *
      (((s : ℝ) + 1) * ((Fintype.card σ : ℝ) + 1) ^ s * A * Fintype.card σ * s) ≤
        Real.exp p)
    (hεinv : 1 / ε ≤ Real.exp p) :
    letI := rightMetricSpace (hnil := F.realification.lowerCentralSeries_eq_bot) (b.baseChange ℝ)
    ∃ N M : ℕ, 0 < N ∧ 0 < M ∧
      (Fintype.card (ι → Fin (N + 1)) : ℝ) ≤ Real.exp ((p + 2) * (3 * (p + 2) + 4)) ∧
      (Fintype.card (σ → Fin (M + 1)) : ℝ) ≤ Real.exp ((p + 1) * (3 * (p + 1) + 4)) ∧
      ∃ center : (ι → Fin (N + 1)) → F.realification.Group,
        (∀ j, π (center j) = 1) ∧
        (∀ j i, |(b.baseChange ℝ).repr (center j).coord i| ≤ B) ∧
        ∀ g : (F.realification.adaptedPolynomialFiltration w).Group,
          F.PolynomialSlowBound b w T A g →
          (∀ z, π (F.adaptedPolynomialRealValueHom w z g) = 1) →
          ∃ label : (σ → Fin (M + 1)) → (ι → Fin (N + 1)),
            ∀ j (v : σ → ℝ), (∀ i, |v i| ≤ T i) →
              (∀ i, |v i - normalizedRealBoxGrid T M j i| ≤ T i * (2 / M)) →
              dist (F.adaptedPolynomialRealValueHom w v g) (center (label j)) ≤ ε := by
  classical
  let := rightMetricSpace (hnil := F.realification.lowerCentralSeries_eq_bot) (b.baseChange ℝ)
  have hhalf : 0 < ε / 2 := by positivity
  have hexp : Real.exp p ≤ Real.exp (p + 1) := Real.exp_le_exp.mpr (by linarith)
  have hinv : 1 / (ε / 2) ≤ Real.exp (p + 1) := by
    have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    calc
      _ = 2 * (1 / ε) := by ring
      _ ≤ 2 * Real.exp p := mul_le_mul_of_nonneg_left hεinv (by norm_num)
      _ ≤ Real.exp 1 * Real.exp p := mul_le_mul_of_nonneg_right htwo (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add, add_comm]
  obtain ⟨N, hN, hNcard, center, hmark, hbound, hnet⟩ :=
    exists_bounded_kernel_net_with_budget (b.baseChange ℝ) (lieStructureConstants b)
      (fun i j k => (realLieBasis_structure b i j k).symm) hc π B hB hhalf
      (by linarith : 0 ≤ p + 1) (by linarith : (Fintype.card ι : ℝ) ≤ p + 1)
      (hBp.trans hexp) (hK.trans hexp) hinv
  let K : ℝ≥0 := ⟨(bchBoxMetricConstant s (Fintype.card ι) H B : ℝ) *
    (((s : ℝ) + 1) * ((Fintype.card σ : ℝ) + 1) ^ s * A * Fintype.card σ * s),
      by positivity⟩
  let M := boxCoverMeshCount 1 K (ε / 2)
  have hM : 0 < M := boxCoverMeshCount_pos _ _ _
  have hMcard := boxCoverCount_dimension_bound (Fintype.card σ) K
    (by norm_num : (0 : ℝ) ≤ 1) hhalf (by linarith : 0 ≤ p + 1)
    (by linarith : (Fintype.card σ : ℝ) ≤ p + 1)
    (Real.one_le_exp (by linarith)) (hmove.trans hexp) hinv
  refine ⟨N, M, hN, hM, ?_, ?_, center, hmark, hbound, ?_⟩
  · simpa only [add_assoc, one_add_one_eq_two] using hNcard
  · simpa only [Fintype.card_fun, Fintype.card_fin] using hMcard
  · intro g hg hker
    have hz (j : σ → Fin (M + 1)) (i : σ) :
        |normalizedRealBoxGrid T M j i| ≤ T i := normalizedRealBoxGrid_bound T hT hM j i
    choose label hlabel using fun j : σ → Fin (M + 1) =>
      hnet (F.adaptedPolynomialRealValueHom w (normalizedRealBoxGrid T M j) g)
        (hker _) (fun i =>
          (F.polynomialSlowBound_value b w hw T hT hA g hg _ (hz j) i).trans hAB)
    refine ⟨label, ?_⟩
    intro j v hv hvz
    have hm := F.polynomialSlowBound_dist_le b w hw H hc T hT hA
      (by positivity : (0 : ℝ) ≤ 2 / M) B hB hAB g hg v
      (normalizedRealBoxGrid T M j) hv (hz j) hvz
    have herr : dist (F.adaptedPolynomialRealValueHom w v g)
        (F.adaptedPolynomialRealValueHom w (normalizedRealBoxGrid T M j) g) ≤ ε / 2 := by
      apply hm.trans
      have he := boxCoverMeshCount_error (B := (1 : ℝ)) K hhalf
      change (K : ℝ) * (2 / (M : ℝ)) ≤ ε / 2
      simpa only [mul_one] using he
    calc
      _ ≤ dist (F.adaptedPolynomialRealValueHom w v g)
          (F.adaptedPolynomialRealValueHom w (normalizedRealBoxGrid T M j) g) +
        dist (F.adaptedPolynomialRealValueHom w (normalizedRealBoxGrid T M j) g)
          (center (label j)) := dist_triangle _ _ _
      _ ≤ ε / 2 + ε / 2 := add_le_add herr (hlabel j)
      _ = ε := by ring

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration
open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal

theorem exists_uniform_slow_kernel_cells (s r : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ ι L G : Type*}
      [Fintype σ] [DecidableEq σ] [Fintype ι] [DecidableEq ι]
      [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)] [_root_.Group G]
      (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (w : σ → ℕ),
      (∀ i, 0 < w i) → ∀ (π : F.realification.Group →* G) (H : ℕ) (p : ℝ),
      0 ≤ p → (Fintype.card ι : ℝ) ≤ p → (Fintype.card σ : ℝ) ≤ p →
      (H : ℝ) ≤ Real.exp p →
      (∀ i j k, RationalHeightLE (lieStructureConstants b i j k) H) →
      ∀ T : σ → ℝ, (∀ i, 0 < T i) →
      letI := rightMetricSpace (hnil := F.realification.lowerCentralSeries_eq_bot) (b.baseChange ℝ)
      ∃ N M : ℕ, 0 < N ∧ 0 < M ∧
        (Fintype.card (ι → Fin (N + 1)) : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        (Fintype.card (σ → Fin (M + 1)) : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∃ center : (ι → Fin (N + 1)) → F.realification.Group,
          (∀ j, π (center j) = 1) ∧
          (∀ j i, |(b.baseChange ℝ).repr (center j).coord i| ≤ Real.exp ((p + C) ^ C)) ∧
          ∀ g : (F.realification.adaptedPolynomialFiltration w).Group,
            F.PolynomialSlowBound b w T (Real.exp ((p + 2) ^ r)) g →
            (∀ z, π (F.adaptedPolynomialRealValueHom w z g) = 1) →
            ∃ label : (σ → Fin (M + 1)) → (ι → Fin (N + 1)),
              ∀ j (v : σ → ℝ), (∀ i, |v i| ≤ T i) →
                (∀ i, |v i - normalizedRealBoxGrid T M j i| ≤ T i * (2 / M)) →
                dist (F.adaptedPolynomialRealValueHom w v g) (center (label j)) ≤
                  Real.exp (-((p + 2) ^ r)) := by
  obtain ⟨a, ha, hgeometry⟩ := exists_slow_kernel_net_geometry_budget s r
  let X : Polynomial ℕ := Polynomial.X
  let Q := X + (X + Polynomial.C a) ^ a + (X + 2) ^ r
  let P := Q + (Q + 2) * (3 * (Q + 2) + 4)
  obtain ⟨C, hC, hP⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro σ ι L G _ _ _ _ _ _ _ _ _ _ _ F b w hw π H p hp hd hn hH hc T hT
  let := rightMetricSpace (hnil := F.realification.lowerCentralSeries_eq_bot) (b.baseChange ℝ)
  obtain ⟨B, hB, hAB, hBcap, hK, hmove⟩ := hgeometry
    (Fintype.card ι) (Fintype.card σ) H p (Real.exp ((p + 2) ^ r))
    hp hd hn hH (Real.exp_nonneg _) le_rfl
  let q : ℝ := p + (p + a) ^ a + (p + 2) ^ r
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have ha0 : 0 ≤ (p + a) ^ a := by positivity
  have hr0 : 0 ≤ (p + 2) ^ r := by positivity
  have hpq : p ≤ q := by dsimp [q]; linarith
  have haq : (p + a) ^ a ≤ q := by dsimp [q]; linarith
  have hrq : (p + 2) ^ r ≤ q := by dsimp [q]; linarith
  have hinv : 1 / Real.exp (-((p + 2) ^ r)) ≤ Real.exp q := by
    rw [Real.exp_neg]
    simpa only [one_div, inv_inv] using Real.exp_le_exp.mpr hrq
  obtain ⟨N, M, hN, hM, hNcard, hMcard, center, hmark, hbound, hfreeze⟩ :=
    F.exists_slow_kernel_cells b w hw π H hc T hT (Real.exp_nonneg _) B hB hAB
      (Real.exp_pos _) hq (hd.trans hpq) (hn.trans hpq)
      (hBcap.trans (Real.exp_le_exp.mpr haq))
      (hK.trans (Real.exp_le_exp.mpr haq))
      (hmove.trans (Real.exp_le_exp.mpr haq)) hinv
  have hbudget : q + (q + 2) * (3 * (q + 2) + 4) ≤ (p + C) ^ C := by
    simpa [P, Q, X, q, Polynomial.eval₂_pow] using hP p hp
  have hcard : (q + 2) * (3 * (q + 2) + 4) ≤ (p + C) ^ C := by linarith
  have hqcap : q ≤ (p + C) ^ C := by
    have : 0 ≤ (q + 2) * (3 * (q + 2) + 4) := by positivity
    linarith
  refine ⟨N, M, hN, hM, hNcard.trans (Real.exp_le_exp.mpr hcard),
    hMcard.trans (Real.exp_le_exp.mpr ?_), center, hmark, ?_, hfreeze⟩
  · exact (show (q + 1) * (3 * (q + 1) + 4) ≤ (q + 2) * (3 * (q + 2) + 4) by
      nlinarith).trans hcard
  · intro j i
    exact (hbound j i).trans (hBcap.trans (Real.exp_le_exp.mpr (haq.trans hqcap)))

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration
open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct NNReal

theorem exists_actual_marked_slow_kernel_cells (s a u : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ ι κ L M : Type*}
      [Fintype σ] [DecidableEq σ] [Fintype ι] [DecidableEq ι] [Fintype κ]
      [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)] {t : ℕ}
      (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M t)
      (b : Basis ι ℚ L) (c : Basis κ ℚ M) (ω : ι → ℕ),
      (∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})) →
      ∀ (w : σ → ℕ), (∀ i, 0 < w i) →
      ∀ (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j)
        (S : M →ₗ[ℚ] L) (hS : ∀ j, ∀ y ∈ G.layer j, S y ∈ F.layer j),
      Function.RightInverse S φ →
      ∀ (H : ℕ) (p : ℝ), 1 ≤ H → 0 ≤ p →
      (Fintype.card ι : ℝ) ≤ p → (Fintype.card κ : ℝ) ≤ p →
      (Fintype.card σ : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p →
      (∀ i j k, RationalHeightLE (lieStructureConstants b i j k) H) →
      (∀ i j, |(b.repr (S (c j)) i : ℝ)| ≤ Real.exp ((p + 2) ^ a)) →
      ∀ T : σ → ℝ, (∀ i, 0 < T i) →
      letI := rightMetricSpace (hnil := F.realification.lowerCentralSeries_eq_bot) (b.baseChange ℝ)
      ∃ N Q : ℕ, 0 < N ∧ 0 < Q ∧
        (Fintype.card (ι → Fin (N + 1)) : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        (Fintype.card (σ → Fin (Q + 1)) : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∃ center : (ι → Fin (N + 1)) → F.realification.Group,
          (∀ j, realificationMap (hnil := F.lowerCentralSeries_eq_bot)
            (hM := G.lowerCentralSeries_eq_bot) φ (center j) = 1) ∧
          (∀ j i, |(b.baseChange ℝ).repr (center j).coord i| ≤ Real.exp ((p + C) ^ C)) ∧
          ∀ (E : (F.realification.adaptedPolynomialFiltration w).Group)
            (EF : (G.realification.adaptedPolynomialFiltration w).Group),
            F.PolynomialSlowBound b w T (Real.exp ((p + 2) ^ a)) E →
            G.PolynomialSlowBound c w T (Real.exp ((p + 2) ^ a)) EF →
            F.realPolynomialGroupMap G φ hφ w E = EF →
            ∃ label : (σ → Fin (Q + 1)) → (ι → Fin (N + 1)),
              ∀ j (v : σ → ℝ), (∀ i, |v i| ≤ T i) →
                (∀ i, |v i - normalizedRealBoxGrid T Q j i| ≤ T i * (2 / Q)) →
                dist (F.adaptedPolynomialRealValueHom w v
                  (E * (F.filteredRealPolynomialSection G w S hS EF)⁻¹))
                  (center (label j)) ≤ Real.exp (-((p + 2) ^ u)) := by
  obtain ⟨A, hA, hslow⟩ := exists_marked_polynomial_kernel_slow_bound s a
  obtain ⟨B, hB, hnet⟩ := exists_uniform_slow_kernel_cells s (A + u)
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((Polynomial.X + Polynomial.C A + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro σ ι κ L M _ _ _ _ _ _ _ _ _ _ _ _ _ t F G b c ω hF w hw φ hφ S hS
    hsection H p hH hp hι hκ hσ hHp hc hSbound T hT
  let := rightMetricSpace (hnil := F.realification.lowerCentralSeries_eq_bot) (b.baseChange ℝ)
  let π := realificationMap (hnil := F.lowerCentralSeries_eq_bot)
    (hM := G.lowerCentralSeries_eq_bot) φ
  have hpA : p ≤ p + A := le_add_of_nonneg_right (Nat.cast_nonneg _)
  have hpA0 : 0 ≤ p + A := hp.trans hpA
  obtain ⟨N, Q, hN, hQ, hNcard, hQcard, center, hmark, hcap, hfreeze⟩ :=
    hnet F b w hw π H (p + A) hpA0 (hι.trans hpA) (hσ.trans hpA)
      (hHp.trans (Real.exp_le_exp.mpr hpA)) hc T hT
  have hcost : (p + A + B) ^ B ≤ (p + C) ^ C := by
    simpa [Polynomial.eval₂_pow] using hbudget p hp
  refine ⟨N, Q, hN, hQ, hNcard.trans (Real.exp_le_exp.mpr hcost),
    hQcard.trans (Real.exp_le_exp.mpr hcost), center, hmark,
    fun j i => (hcap j i).trans (Real.exp_le_exp.mpr hcost), ?_⟩
  intro E EF hE hEF hproj
  have hKE := (hslow F G b c ω hF w hw H p hH hp hι hκ hσ hHp hc S hS
    (by simpa only [scalarExtension_basis_coordinates] using hSbound) T hT E EF hE hEF).1
  have hbound : (p + A) ^ A ≤ (p + A + 2) ^ (A + u) :=
    (pow_le_pow_left₀ hpA0 (by linarith : p + A ≤ p + A + 2) A).trans
      (pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ p + A + 2) (by omega))
  have hKEslow := F.polynomialSlowBound_mono b w T hT
    (Real.exp_le_exp.mpr hbound) _ hKE
  have hmap : F.realPolynomialGroupMap G φ hφ w
      (E * (F.filteredRealPolynomialSection G w S hS EF)⁻¹) = 1 := by
    rw [map_mul, map_inv, hproj,
      F.realPolynomialGroupMap_filteredSection G w φ hφ S hS hsection EF, mul_inv_cancel]
  have hker (v : σ → ℝ) : π (F.adaptedPolynomialRealValueHom w v
      (E * (F.filteredRealPolynomialSection G w S hS EF)⁻¹)) = 1 := by
    rw [← F.realPolynomialGroupMap_value G φ hφ w, hmap, map_one]
  obtain ⟨label, hlabel⟩ := hfreeze _ hKEslow hker
  refine ⟨label, ?_⟩
  intro j v hv hvj
  apply (hlabel j v hv hvj).trans
  apply Real.exp_le_exp.mpr
  apply neg_le_neg
  exact (pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ p + 2)
    (by linarith : p + 2 ≤ p + A + 2) u).trans
      (pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ p + A + 2) (by omega))

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.RationalHomogeneousSymbolPullbackGrid
namespace OAI

section

namespace Erdos3
open Module _root_.MvPolynomial
open scoped TensorProduct

namespace NilpotentLieFiltration
open VectorPolynomial

variable {σ τ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (w : σ → ℕ) (v : τ → ℕ)

theorem realGradedSymbolPolynomial_degreeLE_one
    (hw : ∀ i, 0 < w i) (R : F.RealPolynomialSymbolGroup w) :
    DegreeLE (fun _ => 1) s (F.realGradedSymbolPolynomial b ω hF w R.coord) := by
  intro α hα
  apply ((F.associatedGradedBasis b ω hF).baseChange ℝ).repr.injective
  ext i
  rw [map_zero, Finsupp.zero_apply]
  apply F.realGradedSymbolPolynomial_coordinate_of_ne b ω hF w R.coord α i
  have hi := F.adaptedBasis_weight_le_step b ω hF i
  have hweight := exponentSum_le_positive_weight w hw α
  have hone : Finsupp.weight (fun _ : σ => 1) α = α.sum (fun _ n => n) := by
    simp [Finsupp.weight_apply]
  rw [hone] at hα
  omega

end NilpotentLieFiltration
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.AllocatedKeptCommonCurrentGradeLocalNiltest
namespace OAI

section

namespace Erdos3

open Module _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped BigOperators TensorProduct

theorem homogeneousComponent_scaled_coeff_bound {σ : Type*}
    (P : MvPolynomial σ ℝ) (k : ℕ) (N : σ → ℝ)
    (hN : ∀ i, 0 < N i) (M : ℝ) (hM : 0 ≤ M)
    (hP : ∀ α, |P.coeff α| ≤ M / monomialScale N α) :
    ∀ α, |(homogeneousComponent k P).coeff α| ≤ M / monomialScale N α := by
  intro α
  rw [coeff_homogeneousComponent]
  split_ifs with h
  · exact hP α
  · simpa only [abs_zero] using div_nonneg hM (monomialScale_pos N hN α).le

end Erdos3

end

end OAI
end


