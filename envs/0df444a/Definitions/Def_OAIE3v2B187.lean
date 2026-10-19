-- Prove2me | Definitions.Def_OAIE3v2B187
-- name    : OAIE3v2B187
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T11:41:19.280429+00:00
-- url     : https://prove2.me/theorems/522854c9-6ab4-482c-b7bb-35dd8ed636d9
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 190 of 311
-- statement:
--   Definitions bundle 190 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B161`, `OAIE3v2B162`, `OAIE3v2B164`, `OAIE3v2B170`, `OAIE3v2B171` of this split.
--
--   Modules: `Dynamics/IntervalSplitBudget.lean`, `Estimates/BoundedNativeDependentApproximations.lean`, `Estimates/NativeBoundedVariablePatchExpansion.lean`, `Estimates/NativeCoveredCommonFactorization.lean`, `Estimates/NativeGlobalErrorSplitting.lean`, `Estimates/NativeSubspaceFreeModel.lean`, `Estimates/NativeTwoVariableSplitFreezing.lean`, `Estimates/NativeWeightPairRemoval.lean`, `Estimates/PrescribedInvariantUnit.lean`, `Lattices/CommonAffineOrbitEvaluation.lean`, `Linear/CommonRealDependentProjection.lean`, `Linear/NativeCoefficientKernel.lean`, `Linear/NativeRankRelationExistence.lean`, `Linear/NativeVerticalTranslateFrame.lean`, `Linear/RankHorizontalRepresentatives.lean`, `Linear/RankIntervalFactorization.lean`, `Linear/RankNativeCoordinates.lean`, `Linear/RankProductOrbitCoefficients.lean`, `Nilpotent/PositivePolynomialFactorNiltests.lean`, `Polynomial/ControlledPositivePolynomialDownsets.lean`, `Polynomial/MarkedPolynomialGenerators.lean`, `Polynomial/PositivePolynomialVectorOrbit.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B161
import Definitions.Def_OAIE3v2B162
import Definitions.Def_OAIE3v2B164
import Definitions.Def_OAIE3v2B170
import Definitions.Def_OAIE3v2B171

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeTwoVariableSplitFreezing
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open Module
open scoped TensorProduct NNReal

theorem exists_controlled_multidegree_basepoint_normalization (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)] {d : ℕ}
      {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
      (M : D.MultidegreeStructure bound) {p : ℝ}, 0 ≤ p → D.GeometryComplexityLE p →
      ∀ g : M.filtration.realification.PolynomialOrbit,
      ∃ (ε : D.RealGroup) (A : ℝ≥0), (A : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        (letI := D.metricSpace; LipschitzWith A (fun x : D.Space => ε • x)) ∧
        ∃ g' : M.filtration.realification.PolynomialOrbit,
          M.filtration.realification.polynomialOrbitEval 0 g' = 1 ∧
          ∀ x, ε • (QuotientGroup.mk (M.filtration.realification.polynomialOrbitEval x g') : D.Space) =
            QuotientGroup.mk (M.filtration.realification.polynomialOrbitEval x g) := by
  obtain ⟨a, _, hrep⟩ := Erdos3.exists_realification_representatives_exp_bound s
  obtain ⟨b, _, hleft⟩ := exists_bounded_normalization_left_lipschitz s a
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((X + Polynomial.C a + 2 + Polynomial.C b) ^ b)
  refine ⟨C, hC, ?_⟩
  intro σ L _ _ _ _ _ _ _ d D bound M p hp hD g
  have hcost : normalizedSquareLeftBudget a b p ≤ (p + C) ^ C := by
    simpa [X, normalizedSquareLeftBudget, Polynomial.eval₂_pow] using hbudget p hp
  obtain ⟨A, _, hA, hLip⟩ := hleft D p hp hD
  obtain ⟨ε, hε, γ, hγ, hfactor⟩ :=
    hrep D.basis D.filtration.lowerCentralSeries_eq_bot D.lattice D.grid
      ⌈Real.exp p⌉₊ (p + 1) D.grid_pos D.inner_grid
      (fun i j k => rationalHeightLE_ceil_exp (hD.2.2.1 i j k))
      (by linarith) (by simpa only [Fintype.card_fin] using hD.1.trans (show p ≤ p + 1 by linarith))
      (ceil_exp_le_exp_add_one hp) (hD.2.1.trans (Real.exp_le_exp.mpr (by linarith)))
      (M.filtration.realification.polynomialOrbitEval 0 g)
  refine ⟨ε, A, hA.trans (Real.exp_le_exp.mpr hcost), hLip ε hε,
    M.filtration.realification.normalizeMultidegreeOrbit g ε γ,
    M.filtration.realification.normalizeMultidegreeOrbit_zero g ε γ hfactor, ?_⟩
  intro x
  rw [M.filtration.realification.normalizeMultidegreeOrbit_eval]
  simp only [MulAction.Quotient.smul_mk, smul_eq_mul, ← mul_assoc, mul_inv_cancel, one_mul]
  exact QuotientGroup.mk_mul_of_mem _ (D.realLattice.inv_mem hγ)

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.NativeVerticalTranslateFrame
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup CircleFourier
open scoped TensorProduct NNReal

theorem exists_native_vertical_translate_frame (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ L : Type*} [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)] {d : ℕ}
      (D : RationalFilteredNilmanifold L s d) {w : σ → ℕ} (T : D.Niltest w)
      {p : ℝ}, 0 ≤ p → T.ComplexityLE p → T.normBound ≤ 1 →
      ∀ eta : L →ₗ[ℚ] ℚ,
      (∀ z, z ∈ D.filtration.realification.subgroup s → ∀ x,
        T.observable (z • x) =
          character ((realifyFunctional eta z.coord : ℝ) : CircleFourier.Circle) * T.observable x) →
      ∀ y : D.Space, Real.exp (-p) ≤ ‖T.observable y‖ →
      ∃ n : ℕ, 0 < n ∧ (n : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
      ∃ K : ℝ≥0, (K : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
      ∃ u : Fin n → D.Space → ℂ,
        (∀ i x, ‖u i x‖ ≤ 1) ∧
        (letI := D.metricSpace; ∀ i, LipschitzWith K (u i)) ∧
        (∀ x, ∃ i, Real.exp (-(p + 1)) ≤ ‖u i x‖) ∧
        ∀ i z, z ∈ D.filtration.realification.subgroup s → ∀ x,
          u i (z • x) =
            character ((realifyFunctional eta z.coord : ℝ) : CircleFourier.Circle) * u i x := by
  obtain ⟨a, _, hrep⟩ := exists_realification_representatives_exp_bound s
  obtain ⟨b, _, hleft⟩ := exists_bounded_normalization_left_lipschitz s a
  obtain ⟨c, _, hcover⟩ := exists_native_quotient_parameter_cover s
  let X : Polynomial ℕ := Polynomial.X
  let Q := 2 * X + 2 * (X + Polynomial.C a + 2 + Polynomial.C b) ^ b + 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (X + Q + (Q + Polynomial.C c) ^ c + 1)
  refine ⟨C, hC, ?_⟩
  intro σ L _ _ _ _ _ _ d D w T p hp hT hnorm eta hvertical y hy
  let := D.metricSpace
  let l := normalizedSquareLeftBudget a b p
  let q := 2 * p + 2 * l + 2
  have hl : 0 ≤ l := normalizedSquareLeftBudget_nonneg a b hp
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hpq : p ≤ q := by dsimp [q]; linarith
  have htotal : p + q + (q + c) ^ c + 1 ≤ (p + C) ^ C := by
    simpa [X, Q, q, l, normalizedSquareLeftBudget, Polynomial.eval₂_pow] using hbudget p hp
  have hcp : 0 ≤ (q + c) ^ c := by positivity
  have hqp : q ≤ (p + C) ^ C := by linarith
  have hcount : (q + c) ^ c ≤ (p + C) ^ C := by linarith
  obtain ⟨A, _, hA, hLip⟩ := hleft D p hp hT.1
  have hrepresentatives : ∀ x : D.Space, ∃ r : D.RealGroup,
      (∀ i, |(D.basis.baseChange ℝ).repr r.coord i| ≤ Real.exp ((p + 1 + a) ^ a)) ∧
      QuotientGroup.mk r = x := by
    intro x
    induction x using Quotient.inductionOn with
    | h g =>
      obtain ⟨r, hr, γ, hγ, hg⟩ :=
        hrep D.basis D.filtration.lowerCentralSeries_eq_bot D.lattice D.grid
          ⌈Real.exp p⌉₊ (p + 1) D.grid_pos D.inner_grid
          (fun i j k => rationalHeightLE_ceil_exp (hT.1.2.2.1 i j k))
          (by linarith)
          (by simpa only [Fintype.card_fin] using hT.1.1.trans (show p ≤ p + 1 by linarith))
          (ceil_exp_le_exp_add_one hp) (hT.1.2.1.trans (Real.exp_le_exp.mpr (by linarith))) g
      refine ⟨r, hr, ?_⟩
      change (QuotientGroup.mk r : D.Space) = QuotientGroup.mk g
      rw [hg]
      exact (QuotientGroup.mk_mul_of_mem r (show γ ∈ D.realLattice from hγ)).symm
  choose r hr hrc using hrepresentatives
  have hInv (x : D.Space) : ∀ i,
      |(D.basis.baseChange ℝ).repr (r x)⁻¹.coord i| ≤ Real.exp ((p + 1 + a) ^ a) := by
    intro i
    simpa only [coord_inv, map_neg, Finsupp.neg_apply, abs_neg] using hr x i
  let ε := Real.exp (-q)
  have hε : 0 < ε := Real.exp_pos _
  have hεinv : 1 / ε ≤ Real.exp q := by
    simp only [ε, Real.exp_neg, one_div, inv_inv, le_refl]
  obtain ⟨n, hn, hnc, centers, hcenters⟩ :=
    hcover D hq (hT.1.mono D hpq) hε hεinv
  let K := T.lipBound * (A * A)
  let u (i : Fin n) (x : D.Space) := T.observable (r y • ((r (centers i))⁻¹ • x))
  have hK : (K : ℝ) ≤ Real.exp (p + 2 * l) := by
    have hTlip : (T.lipBound : ℝ) ≤ Real.exp p := by
      linarith [Niltest.observable_budget hT, T.normBound.coe_nonneg]
    calc
      _ ≤ Real.exp p * (Real.exp l * Real.exp l) := by
        dsimp [K]
        exact mul_le_mul hTlip (mul_le_mul hA hA A.coe_nonneg (Real.exp_nonneg _))
          (mul_nonneg A.coe_nonneg A.coe_nonneg) (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have huLip (i : Fin n) : LipschitzWith K (u i) :=
    T.lipschitz.comp ((hLip (r y) (hr y)).comp (hLip ((r (centers i))⁻¹) (hInv _)))
  have hcenter (i : Fin n) : u i (centers i) = T.observable y := by
    change T.observable (r y • ((r (centers i))⁻¹ • centers i)) = T.observable y
    have heq : (r (centers i))⁻¹ • centers i = (QuotientGroup.mk (1 : D.RealGroup) : D.Space) := by
      calc
        _ = (r (centers i))⁻¹ • QuotientGroup.mk (r (centers i)) :=
          congrArg (fun x : D.Space => (r (centers i))⁻¹ • x) (hrc _).symm
        _ = _ := by simp only [MulAction.Quotient.smul_mk, smul_eq_mul, inv_mul_cancel]
    rw [heq]
    simp only [MulAction.Quotient.smul_mk, smul_eq_mul, mul_one, hrc]
  have herror : (K : ℝ) * ε ≤ Real.exp (-p) / 2 := by
    calc
      _ ≤ Real.exp (p + 2 * l) * Real.exp (-q) := mul_le_mul_of_nonneg_right hK hε.le
      _ = Real.exp (-p - 2) := by rw [← Real.exp_add]; congr 1; dsimp [q]; ring
      _ ≤ Real.exp (-p - 1) := Real.exp_le_exp.mpr (by linarith)
      _ ≤ _ := exp_sub_one_le_half_exp (-p)
  refine ⟨n, hn, hnc.trans (Real.exp_le_exp.mpr hcount), K,
    hK.trans (Real.exp_le_exp.mpr (by dsimp [q] at hqp; linarith)), u, ?_, huLip, ?_, ?_⟩
  · intro i x
    have hnorm' : (T.normBound : ℝ) ≤ (1 : ℝ) := by exact_mod_cast hnorm
    exact (T.norm_le _).trans hnorm'
  · intro x
    obtain ⟨i, hi⟩ := hcenters x
    have hdist := (huLip i).dist_le_mul x (centers i)
    have herr : ‖u i (centers i) - u i x‖ ≤ Real.exp (-p) / 2 := by
      have h := hdist.trans ((mul_le_mul_of_nonneg_left hi K.coe_nonneg).trans herror)
      simpa only [dist_eq_norm, norm_sub_rev] using h
    have ht := norm_sub_norm_le (u i (centers i)) (u i x)
    rw [hcenter] at ht herr
    refine ⟨i, ?_⟩
    have hh : Real.exp (-(p + 1)) ≤ Real.exp (-p) / 2 := by
      simpa only [neg_add, sub_eq_add_neg] using exp_sub_one_le_half_exp (-p)
    linarith
  · intro i z hz x
    exact D.vertical_left_translate (fun x => T.observable (r y • x)) eta
      (fun z hz x => D.vertical_left_translate T.observable eta hvertical (r y) z hz x)
      ((r (centers i))⁻¹) z hz x

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PrescribedInvariantUnit
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open CircleFourier
open scoped TensorProduct NNReal BigOperators

theorem exists_native_unit_vertical_family (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ L : Type*} [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)] {d : ℕ}
      (D : RationalFilteredNilmanifold L s d) {w : σ → ℕ} (T : D.Niltest w)
      {p : ℝ}, 0 ≤ p → T.ComplexityLE p → T.normBound ≤ 1 →
      ∀ eta : L →ₗ[ℚ] ℚ,
      (∀ z, z ∈ D.filtration.realification.subgroup s → ∀ x,
        T.observable (z • x) =
          character ((realifyFunctional eta z.coord : ℝ) : CircleFourier.Circle) * T.observable x) →
      ∀ y : D.Space, Real.exp (-p) ≤ ‖T.observable y‖ →
      ∃ n : ℕ, 0 < n ∧ (n : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
      ∃ K : ℝ≥0, (K : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
      ∃ v : Fin n → D.Space → ℂ,
        (∀ x, ∑ i, ‖v i x‖ ^ 2 = 1) ∧
        (∀ i x, ‖v i x‖ ≤ 1) ∧
        (letI := D.metricSpace; ∀ i, LipschitzWith K (v i)) ∧
        ∀ i z, z ∈ D.filtration.realification.subgroup s → ∀ x,
          v i (z • x) =
            character ((realifyFunctional eta z.coord : ℝ) : CircleFourier.Circle) * v i x := by
  obtain ⟨a, _, hframe⟩ := exists_native_vertical_translate_frame s
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (X + 2 * (X + Polynomial.C a) ^ a + 3)
  refine ⟨C, hC, ?_⟩
  intro σ L _ _ _ _ _ _ d D w T p hp hT hnorm eta hvertical y hy
  let := D.metricSpace
  let P := (p + a) ^ a
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have htotal : p + 2 * P + 3 ≤ (p + C) ^ C := by
    simpa [P, X, Polynomial.eval₂_pow] using hbudget p hp
  obtain ⟨n, hn, hnc, K, hK, u, _, hLip, hlower, hphase⟩ :=
    hframe D T hp hT hnorm eta hvertical y hy
  let rho : ℝ≥0 := ⟨Real.exp (-(p + 1)), (Real.exp_pos _).le⟩
  have hrho : 0 < rho := Real.exp_pos _
  obtain ⟨v, hvunit, hvnorm, hvLip, hvphase⟩ :=
    exists_normalized_complex_family u hrho hLip hlower
  let B : ℝ≥0 := 2 / rho * ((n + 1 : ℝ≥0) * K)
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hnplus : (n : ℝ) + 1 ≤ Real.exp (P + 1) := by
    calc
      _ ≤ 2 * Real.exp P := by linarith [Real.one_le_exp hP]
      _ ≤ Real.exp 1 * Real.exp P := mul_le_mul_of_nonneg_right htwo (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add, add_comm]
  have hscale : 2 / (rho : ℝ) ≤ Real.exp (p + 2) := by
    calc
      _ = 2 * Real.exp (p + 1) := by
        change 2 / Real.exp (-(p + 1)) = _
        rw [Real.exp_neg, div_inv_eq_mul]
      _ ≤ Real.exp 1 * Real.exp (p + 1) := mul_le_mul_of_nonneg_right htwo (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hB : (B : ℝ) ≤ Real.exp (p + 2 * P + 3) := by
    calc
      _ ≤ Real.exp (p + 2) * (Real.exp (P + 1) * Real.exp P) := by
        dsimp [B]
        push_cast
        exact mul_le_mul hscale (mul_le_mul hnplus hK K.coe_nonneg (Real.exp_nonneg _))
          (by positivity) (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  refine ⟨n, hn, hnc.trans (Real.exp_le_exp.mpr (by dsimp [P] at *; linarith)),
    B, hB.trans (Real.exp_le_exp.mpr htotal), v, hvunit, hvnorm, ?_, ?_⟩
  · intro i
    simpa only [Fintype.card_fin] using hvLip i
  · intro i z hz x
    exact hvphase (z • x) x _ (norm_character _) (fun j => hphase j z hz x) i

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct NNReal

theorem exists_native_prescribed_unit (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L : Type*} [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)] {d : ℕ}
      (D : RationalFilteredNilmanifold L s d) {p : ℝ},
      0 ≤ p → D.GeometryComplexityLE p → ∀ η : L →ₗ[ℚ] ℚ,
      (∀ i, rationalLogHeight (η (D.basis i)) ≤ p) →
      (∀ z : D.RealGroup, z ∈ D.realLattice → ∃ n : ℤ, realifyFunctional η z.coord = n) →
      ∃ n : ℕ, 0 < n ∧ (n : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
      ∃ V : D.UnitVerticalObservable (D.filtration.realification.subgroup s) (Fin n)
        ((p + C) ^ C), V.frequency = η := by
  obtain ⟨a, _, hscalar⟩ := exists_native_prescribed_scalar s
  obtain ⟨b, _, hfamily⟩ := exists_native_unit_vertical_family s
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (X + (X + (X + Polynomial.C a) ^ a + 4 + Polynomial.C b) ^ b)
  refine ⟨C, hC, ?_⟩
  intro L _ _ _ _ _ _ d D p hp hD η hη hint
  let := D.metricSpace
  obtain ⟨K, hK, f, hf, hb, hvertical, hone⟩ := hscalar D hp hD η hη hint
  let P := (p + a) ^ a
  let q := p + P + 4
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hpq : p ≤ q := by dsimp [q]; linarith
  have htwoNorm : ‖(2 : ℂ)‖ = (2 : ℝ) := by norm_num
  let T : D.Niltest (fun _ : Unit => 1) := {
    orbit := 1
    observable := fun x => f x / 2
    normBound := 1
    lipBound := K
    norm_le := fun x => by
      rw [norm_div, htwoNorm]
      simpa only [NNReal.coe_one, div_self (by norm_num : (2 : ℝ) ≠ 0)] using
        div_le_div_of_nonneg_right (hb x) (by norm_num : (0 : ℝ) ≤ 2)
    lipschitz := by
      apply LipschitzWith.of_dist_le_mul
      intro x y
      rw [dist_eq_norm, ← sub_div, norm_div, htwoNorm]
      have h := hf.dist_le_mul x y
      rw [dist_eq_norm] at h
      linarith [norm_nonneg (f x - f y)] }
  have hT : T.ComplexityLE q := by
    refine ⟨hD.mono D hpq, ?_⟩
    have h := niltest_log_bound_of_exp (1 : ℝ≥0) K (a := 0) (b := P)
      (by norm_num) hP (by simp) hK
    simp only [NNReal.coe_one, zero_add] at h
    change Real.log (2 + ((1 : ℝ≥0) : ℝ) + K) ≤ q
    dsimp [q]
    linarith
  have hphase : ∀ z : D.RealGroup, z ∈ D.filtration.realification.subgroup s → ∀ x,
      T.observable (z • x) = CircleFourier.character
        ((realifyFunctional η z.coord : ℝ) : CircleFourier.Circle) * T.observable x := by
    intro z hz x
    change f (z • x) / 2 = _ * (f x / 2)
    rw [hvertical z hz]
    exact mul_div_assoc _ _ _
  have hy : Real.exp (-q) ≤ ‖T.observable (QuotientGroup.mk (1 : D.RealGroup))‖ := by
    change Real.exp (-q) ≤ ‖f (QuotientGroup.mk (1 : D.RealGroup)) / 2‖
    rw [hone, norm_div, norm_one, htwoNorm]
    have htwo : (2 : ℝ) ≤ Real.exp q := by
      have he := Real.add_one_le_exp q
      dsimp [q] at *
      linarith
    rw [Real.exp_neg, ← one_div]
    exact one_div_le_one_div_of_le (by norm_num) htwo
  obtain ⟨n, hn, hnc, K', hK', v, hvunit, hvnorm, hvLip, hvphase⟩ :=
    hfamily D T hq hT (by exact le_rfl) η hphase
      (QuotientGroup.mk (1 : D.RealGroup)) hy
  have htotal : p + (q + b) ^ b ≤ (p + C) ^ C := by
    simpa [X, q, P, Polynomial.eval₂_pow] using hbudget p hp
  have hqb : (q + b) ^ b ≤ (p + C) ^ C := by linarith
  have hpc : p ≤ (p + C) ^ C := by
    have : 0 ≤ (q + b) ^ b := by positivity
    linarith
  refine ⟨n, hn, hnc.trans (Real.exp_le_exp.mpr hqb), ?_⟩
  exact ⟨{
    observable := v
    unit := hvunit
    norm := hvnorm
    lipBound := K'
    lip_bound := hK'.trans (Real.exp_le_exp.mpr hqb)
    lipschitz := hvLip
    frequency := η
    height := fun i => (hη i).trans hpc
    vertical := hvphase
    integral := fun z _ hz => hint z hz }, rfl⟩

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct NNReal

theorem exists_prescribed_invariant_unit (s M : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {Γ L : Type*} [Group Γ] [Fintype Γ]
      [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)] {d : ℕ}
      (D : RationalFilteredNilmanifold L s d) [MulAction Γ D.Space],
      Fintype.card Γ ≤ M → ∀ {p : ℝ}, 0 ≤ p → D.GeometryComplexityLE p →
      (letI := D.metricSpace; ∀ a : Γ,
        LipschitzWith ⟨Real.exp ((p + 3) ^ 2), (Real.exp_pos _).le⟩ (fun x : D.Space => a • x)) →
      (∀ (a : Γ) (z : D.RealGroup), z ∈ D.filtration.realification.subgroup s → ∀ x : D.Space,
        a • (z • x) = z • (a • x)) →
      ∀ η : L →ₗ[ℚ] ℚ, (∀ i, rationalLogHeight (η (D.basis i)) ≤ p) →
      (∀ z : D.RealGroup, z ∈ D.realLattice → ∃ n : ℤ, realifyFunctional η z.coord = n) →
      ∃ n : ℕ, 0 < n ∧
        (Fintype.card (SymmetricEvaluationIndex (Fintype.card Γ) (Fin n)) : ℝ) ≤
          Real.exp ((p + C) ^ C) ∧
      ∃ W : D.UnitVerticalObservable (D.filtration.realification.subgroup s)
          (SymmetricEvaluationIndex (Fintype.card Γ) (Fin n)) ((p + C) ^ C),
        W.frequency = Fintype.card Γ • η ∧
        ∀ (a : Γ) k x, W.observable k (a • x) = W.observable k x := by
  obtain ⟨a, _, hunit⟩ := exists_native_prescribed_unit s
  obtain ⟨b, _, hcost⟩ := exists_uniform_invariantVertical_cost M
  let X : Polynomial ℕ := Polynomial.X
  let R := X + (X + Polynomial.C a) ^ a + (X + 3) ^ 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((R + Polynomial.C b) ^ b)
  refine ⟨C, hC, ?_⟩
  intro Γ L _ _ _ _ _ _ _ _ d D _ hM p hp hD hact hcomm η hη hint
  let := D.metricSpace
  obtain ⟨n, hn, hnc, V, hV⟩ := hunit D hp hD η hη hint
  let P := (p + a) ^ a
  let r := p + P + (p + 3) ^ 2
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hPr : P ≤ r := by dsimp [r]; nlinarith [sq_nonneg (p + 3)]
  have hAr : (p + 3) ^ 2 ≤ r := by dsimp [r]; linarith
  let V' := V.mono hPr
  have hn' : (Fintype.card (Fin n) : ℝ) ≤ Real.exp r := by
    simpa only [Fintype.card_fin] using hnc.trans (Real.exp_le_exp.mpr hPr)
  obtain ⟨W, hW, hWinv, hWcard⟩ := V'.exists_invariant hr hn'
    ⟨Real.exp ((p + 3) ^ 2), (Real.exp_pos _).le⟩ (Real.exp_le_exp.mpr hAr) hact hcomm
  have htotal : invariantVerticalBudget (Fintype.card Γ) r ≤ (p + C) ^ C := by
    apply (hcost (Fintype.card Γ) hM r hr).trans
    simpa [R, X, r, P, Polynomial.eval₂_pow] using hbudget p hp
  refine ⟨n, hn, hWcard.trans (Real.exp_le_exp.mpr htotal), W.mono htotal, ?_, hWinv⟩
  change W.frequency = _
  rw [hW]
  change Fintype.card Γ • V.frequency = _
  rw [hV]

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeBoundedVariablePatchExpansion
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct NNReal BigOperators

theorem exists_controlled_native_product_approximation (s a b : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {α : Type*} [Fintype α] [DecidableEq α]
      {L : α → Type*} [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)]
      [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
      [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
      [TopologicalSpace (ℝ ⊗[ℚ] (∀ i, L i))] [IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ i, L i))]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] (∀ i, L i))] [T2Space (ℝ ⊗[ℚ] (∀ i, L i))]
      {d : α → ℕ} (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i)) {p epsilon : ℝ},
      0 ≤ p → (Fintype.card α : ℝ) ≤ p → (∀ i, (D i).GeometryComplexityLE p) →
      0 < epsilon → 1 / epsilon ≤ Real.exp ((p + 2) ^ a) →
      letI : ∀ i, MetricSpace (D i).Space := fun i => (D i).metricSpace
      letI := (pi D).metricSpace
      ∃ n : α → ℕ, (∀ i, 0 < n i) ∧ (∀ i, (n i : ℝ) ≤ Real.exp ((p + C) ^ C)) ∧
        (Fintype.card (∀ i, Fin (n i)) : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∃ K : α → ℝ≥0, (∀ i, (K i : ℝ) ≤ Real.exp ((p + C) ^ C)) ∧
          ∃ ψ : ∀ i, Fin (n i) → (D i).Space → ℝ,
            (∀ i j x, 0 ≤ ψ i j x ∧ ψ i j x ≤ 1) ∧
            (∀ i x, ∑ j, ψ i j x = 1) ∧ (∀ i j, LipschitzWith (K i) (ψ i j)) ∧
            ∀ (v : (pi D).Space → ℂ) (ell : ℝ≥0),
              (ell : ℝ) ≤ Real.exp ((p + 2) ^ b) → LipschitzWith ell v → (∀ x, ‖v x‖ ≤ 2) →
              ∃ c : (∀ i, Fin (n i)) → ℂ, (∀ j, ‖c j‖ ≤ 2) ∧
                ∀ x, ‖v x - ∑ j, (∏ i, (ψ i (j i) (productProjection D i x) : ℂ)) * c j‖ ≤ epsilon := by
  obtain ⟨c, _, hpart⟩ := exists_native_product_partition_approximation s 1
  let X : Polynomial ℕ := Polynomial.X
  let Q := X + (X + 2) ^ a + (X + 2) ^ b + (X + 4) ^ 4
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((Q + Polynomial.C c) ^ c)
  refine ⟨C, hC, ?_⟩
  intro α _ _ L _ _ _ _ _ _ _ _ _ _ d D p epsilon hp hα hD hepsilon hscale
  let q := p + (p + 2) ^ a + (p + 2) ^ b + (p + 4) ^ 4
  have hpq : p ≤ q := by
    dsimp [q]
    linarith [pow_nonneg (by linarith : 0 ≤ p + 2) a,
      pow_nonneg (by linarith : 0 ≤ p + 2) b, sq_nonneg ((p + 4) ^ 2)]
  have hq : 0 ≤ q := hp.trans hpq
  let A := (p + 2) ^ b + (p + 4) ^ 4
  let rho := epsilon / Real.exp A
  have hrho : 0 < rho := div_pos hepsilon (Real.exp_pos _)
  have hrhoscale : 1 / rho ≤ Real.exp ((q + 2) ^ 1) := by
    calc
      1 / rho = Real.exp A * (1 / epsilon) := by dsimp [rho]; field_simp
      _ ≤ Real.exp A * Real.exp ((p + 2) ^ a) :=
        mul_le_mul_of_nonneg_left hscale (Real.exp_nonneg _)
      _ = Real.exp (A + (p + 2) ^ a) := (Real.exp_add _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by dsimp [A, q]; simp only [pow_one]; linarith)
  let : ∀ i, MetricSpace (D i).Space := fun i => (D i).metricSpace
  let := (pi D).metricSpace
  obtain ⟨n, hn, hnb, hcount, K, hKb, ψ, hunit, hsum, hLip, happ⟩ :=
    hpart D hq (hα.trans hpq) (fun i => (hD i).mono (D i) hpq) hrho hrhoscale
  have hcost : (q + c) ^ c ≤ (p + C) ^ C := by
    simpa [Q, X, q, Polynomial.eval₂_pow] using hbudget p hp
  have hexp := Real.exp_le_exp.mpr hcost
  refine ⟨n, hn, fun i => (hnb i).trans hexp, hcount.trans hexp,
    K, fun i => (hKb i).trans hexp, ψ, hunit, hsum, hLip, ?_⟩
  intro v ell hell hv hb
  obtain ⟨coeff, hcoeff, herr⟩ := happ v ell hv hb
  refine ⟨coeff, hcoeff, fun x => (herr x).trans ?_⟩
  calc
    (ell : ℝ) * (productMetricBound d : ℝ) * rho ≤
        Real.exp ((p + 2) ^ b) * Real.exp ((p + 4) ^ 4) * rho :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul hell (productMetricBound_le_exp d hp hα (fun i => (hD i).1))
          (productMetricBound d).coe_nonneg (Real.exp_nonneg _)) hrho.le
    _ = epsilon := by rw [← Real.exp_add]; dsimp [rho, A]; field_simp

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.ControlledPositivePolynomialDownsets
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open Module MultidegreeLieFiltration VectorPolynomial

variable {σ L : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
  {s d : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  (M : D.MultidegreeStructure bound) (J : Set (σ →₀ ℕ)) [DecidablePred (· ∈ J)]
  (hJ : IsLowerSet J)

theorem positivePolynomialDownsetFinBasis_multidegree_height (p : ℝ) (a : σ → ℕ) (j k) :
    RationalHeightLE ((M.positivePolynomialDownsetFinBasis J hJ p).repr
      (M.filtration.positivePolynomialDownsetMultidegreeBasis (M.positiveCoefficientBasis p) J hJ a j).val k) 1 := by
  rw [positivePolynomialDownsetFinBasis, Basis.repr_reindex_apply]
  exact M.filtration.positivePolynomialDownsetMultidegreeBasis_height
    (M.positiveCoefficientBasis p) J hJ a j _

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PositivePolynomialVectorOrbit
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open Module MultidegreeLieFiltration VectorPolynomial

variable {σ L : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
  {s d : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  (M : D.MultidegreeStructure bound) (J : Set (σ →₀ ℕ)) [DecidablePred (· ∈ J)]
  (hJ : IsLowerSet J)

theorem positivePolynomialDownset_projection_height (p : ℝ) (i j) :
    RationalHeightLE ((M.positivePolynomialDownsetFinBasis J hJ p).repr
      (lieQuotientMap (restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra J hJ)
        (M.positivePolynomialFinBasis p j)) i) 1 := by
  rw [positivePolynomialDownsetFinBasis, Basis.repr_reindex_apply,
    positivePolynomialFinBasis, Basis.reindex_apply]
  change RationalHeightLE ((M.filtration.positivePolynomialDownsetBasis
    (M.positiveCoefficientBasis p) J hJ).repr
      (lieQuotientMap _ (M.filtration.positivePolynomialBasis (M.positiveCoefficientBasis p) _)) _) 1
  rw [M.filtration.positivePolynomialDownsetBasis_repr]
  exact basis_repr_height_one _ _ _

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open VectorPolynomial

variable {α σ L : Type*} [Fintype α] [DecidableEq α] [Fintype σ] [DecidableEq σ]
  [LieRing L] [LieAlgebra ℚ L] {s d : ℕ} {D : RationalFilteredNilmanifold L s d}
  {bound : σ → ℕ} (M : D.MultidegreeStructure bound)
  (J : α → Set (σ →₀ ℕ)) [∀ a, DecidablePred (· ∈ J a)] (hJ : ∀ a, IsLowerSet (J a))

theorem positivePolynomialProductProjection_mk (p : ℝ) (B : ℕ) (hB : 0 < B)
    (hstable : M.PositivePolynomialGridStable p B)
    (g : M.filtration.positivePolynomialMultidegree.realification.Group) (a : α) :
    productProjection (fun a => M.positivePolynomialDownsetModel (J a) (hJ a) p B hB hstable) a
      (QuotientGroup.mk (M.filtration.positivePolynomialQuotientProductRealMap J hJ g)) =
        QuotientGroup.mk (M.filtration.positivePolynomialMultidegree.realQuotientMultidegreeMap
          (restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra (J a) (hJ a)) g) := by
  change QuotientGroup.mk (realBCHPiEquiv
    (fun a => (M.filtration.positivePolynomialDownsetQuotient (J a) (hJ a)).ordinary)
      (M.filtration.positivePolynomialQuotientProductRealMap J hJ g) a) = _
  rw [M.filtration.positivePolynomialQuotientProductRealMap_component]
  rfl

theorem positivePolynomialProductProjection_orbit (p : ℝ) (B : ℕ) (hB : 0 < B)
    (hstable : M.PositivePolynomialGridStable p B)
    (g : M.filtration.positivePolynomialMultidegree.realification.PolynomialOrbit)
    (x : σ → ℤ) (a : α) :
    productProjection (fun a => M.positivePolynomialDownsetModel (J a) (hJ a) p B hB hstable) a
      (QuotientGroup.mk (M.filtration.positivePolynomialQuotientProductRealMap J hJ
        (M.filtration.positivePolynomialMultidegree.realification.polynomialOrbitEval x g))) =
      QuotientGroup.mk ((M.filtration.positivePolynomialDownsetQuotient (J a) (hJ a)).realification.polynomialOrbitEval x
        (M.filtration.positivePolynomialDownsetOrbit (J a) (hJ a) g)) := by
  rw [M.positivePolynomialProductProjection_mk,
    M.filtration.positivePolynomialDownsetOrbit_eval]

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open NilpotentLieBCHGroup
open scoped BigOperators

variable {I α σ L : Type*} [Fintype I] [Fintype α] [DecidableEq α] [Fintype σ] [DecidableEq σ]
  [LieRing L] [LieAlgebra ℚ L] {s d : ℕ} {D : RationalFilteredNilmanifold L s d}
  {bound : σ → ℕ} (M : D.MultidegreeStructure bound)
  (J : α → Set (σ →₀ ℕ)) [∀ i, DecidablePred (· ∈ J i)] (hJ : ∀ i, IsLowerSet (J i))

theorem positivePolynomial_vector_error_of_lift (p : ℝ) (B : ℕ) (hB : 0 < B)
    (hstable : M.PositivePolynomialGridStable p B)
    (g : M.filtration.realification.PolynomialOrbit)
    (h : M.filtration.positivePolynomialMultidegree.realification.PolynomialOrbit)
    (hproj : ∀ x, realificationMap
      (hnil := M.filtration.positivePolynomialMultidegree.ordinary.lowerCentralSeries_eq_bot)
      (hM := D.filtration.lowerCentralSeries_eq_bot) M.filtration.positivePolynomialEvaluation
      (M.filtration.positivePolynomialMultidegree.realification.polynomialOrbitEval x h) =
        M.filtration.realification.polynomialOrbitEval x g)
    (n : α → ℕ)
    (ψ : ∀ i, Fin (n i) → (M.positivePolynomialDownsetModel (J i) (hJ i) p B hB hstable).Space → ℝ)
    (c : (∀ i, Fin (n i)) → EuclideanSpace ℂ I) (u : I → D.Space → ℂ) (epsilon : ℝ)
    (happrox : ∀ y, ‖(WithLp.toLp 2 (fun k => u k (QuotientGroup.mk (realificationMap
        (hnil := M.filtration.positivePolynomialMultidegree.ordinary.lowerCentralSeries_eq_bot)
        (hM := D.filtration.lowerCentralSeries_eq_bot) M.filtration.positivePolynomialEvaluation y))) : EuclideanSpace ℂ I) -
      ∑ j, (∏ i, (ψ i (j i) (productProjection
        (fun i => M.positivePolynomialDownsetModel (J i) (hJ i) p B hB hstable) i
        (QuotientGroup.mk (M.filtration.positivePolynomialQuotientProductRealMap J hJ y))) : ℂ)) • c j‖ ≤ epsilon) :
    ∀ x, ‖(WithLp.toLp 2 (fun k => u k (QuotientGroup.mk (M.filtration.realification.polynomialOrbitEval x g))) : EuclideanSpace ℂ I) -
      ∑ j, (∏ i, (ψ i (j i) (QuotientGroup.mk
        ((M.filtration.positivePolynomialDownsetQuotient (J i) (hJ i)).realification.polynomialOrbitEval x
          (M.filtration.positivePolynomialDownsetOrbit (J i) (hJ i) h))) : ℂ)) • c j‖ ≤ epsilon := by
  intro x
  have hx := happrox (M.filtration.positivePolynomialMultidegree.realification.polynomialOrbitEval x h)
  rw [hproj x] at hx
  simpa only [M.positivePolynomialProductProjection_orbit] using hx

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.PositivePolynomialFactorNiltests
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open scoped TensorProduct NNReal

variable {σ L : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
  {s d : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  (M : D.MultidegreeStructure bound) (J : Set (σ →₀ ℕ)) [DecidablePred (· ∈ J)]
  (hJ : IsLowerSet J)
  [TopologicalSpace (ℝ ⊗[ℚ] (M.filtration.positivePolynomialAlgebra ⧸
    VectorPolynomial.restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra J hJ))]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] (M.filtration.positivePolynomialAlgebra ⧸
    VectorPolynomial.restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra J hJ))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] (M.filtration.positivePolynomialAlgebra ⧸
    VectorPolynomial.restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra J hJ))]
  [T2Space (ℝ ⊗[ℚ] (M.filtration.positivePolynomialAlgebra ⧸
    VectorPolynomial.restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra J hJ))]
  (p : ℝ) (B : ℕ) (hB : 0 < B) (hstable : M.PositivePolynomialGridStable p B)
  (g : M.filtration.positivePolynomialMultidegree.realification.PolynomialOrbit)
  (ψ : (M.positivePolynomialDownsetModel J hJ p B hB hstable).Space → ℝ)
  (hψ : ∀ x, 0 ≤ ψ x ∧ ψ x ≤ 1) (K : ℝ≥0)
  (hLip : letI := (M.positivePolynomialDownsetModel J hJ p B hB hstable).metricSpace;
    LipschitzWith K ψ)

noncomputable def positivePolynomialFactorNiltest :
    (M.positivePolynomialDownsetModel J hJ p B hB hstable).Niltest (fun _ : σ => 1) :=
  (M.positivePolynomialDownsetModel J hJ p B hB hstable).sectionNiltest
    ((M.positivePolynomialDownsetModelMultidegree J hJ p B hB hstable).orbitToOrdinary
      (M.filtration.positivePolynomialDownsetOrbit J hJ g))
    (fun z (_ : Unit) => ψ z) (fun z _ => hψ z) K (fun _ => hLip) (some ())

theorem positivePolynomialFactorNiltest_unit_interval :
    (M.positivePolynomialFactorNiltest J hJ p B hB hstable g ψ hψ K hLip).UnitIntervalValued :=
  (M.positivePolynomialDownsetModel J hJ p B hB hstable).sectionNiltest_unit_interval _ _ _ _ _ _

theorem positivePolynomialFactorNiltest_eval (x : σ → ℤ) :
    (M.positivePolynomialFactorNiltest J hJ p B hB hstable g ψ hψ K hLip).eval x =
      (ψ (QuotientGroup.mk ((M.filtration.positivePolynomialDownsetQuotient J hJ).realification.polynomialOrbitEval x
        (M.filtration.positivePolynomialDownsetOrbit J hJ g))) : ℂ) := by
  exact congrArg (fun z : (M.positivePolynomialDownsetModel J hJ p B hB hstable).RealGroup =>
    (ψ (QuotientGroup.mk z) : ℂ))
    ((M.positivePolynomialDownsetModelMultidegree J hJ p B hB hstable).orbitToOrdinary_eval
      (M.filtration.positivePolynomialDownsetOrbit J hJ g) x)

theorem positivePolynomialFactorNiltest_complexity {q : ℝ}
    (hE : (M.positivePolynomialDownsetModel J hJ p B hB hstable).GeometryComplexityLE q)
    (hK : (K : ℝ) ≤ Real.exp q) :
    (M.positivePolynomialFactorNiltest J hJ p B hB hstable g ψ hψ K hLip).ComplexityLE (q + 2) := by
  have hq : 0 ≤ q := (Nat.cast_nonneg _).trans hE.1
  have h2 : (4 : ℝ) ≤ Real.exp 2 := by
    rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
    nlinarith [Real.add_one_le_exp (1 : ℝ)]
  have hlog : Real.log (3 + (K : ℝ)) ≤ q + 2 := by
    apply (Real.log_le_iff_le_exp (by positivity)).mpr
    rw [Real.exp_add]
    nlinarith [Real.one_le_exp hq,
      mul_le_mul_of_nonneg_left h2 (Real.exp_nonneg q)]
  exact (M.positivePolynomialDownsetModel J hJ p B hB hstable).sectionNiltest_complexityLE
    _ _ _ _ _ _ (hE.mono _ (by linarith)) hlog

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeGlobalErrorSplitting
namespace OAI

section

namespace Erdos3.NativeVectorEquivalence

open scoped TensorProduct BigOperators

attribute [local instance] NativeNilsequenceExpansion.lie NativeNilsequenceExpansion.algebra
  NativeNilsequenceExpansion.topology NativeNilsequenceExpansion.topologicalAdd
  NativeNilsequenceExpansion.continuousSMul NativeNilsequenceExpansion.hausdorff
  NativeVectorCorrelation.lie NativeVectorCorrelation.algebra
  NativeVectorCorrelation.topology NativeVectorCorrelation.topologicalAdd
  NativeVectorCorrelation.continuousSMul NativeVectorCorrelation.hausdorff

theorem transfer_correlation {I J K : Type*} [Fintype J] [Fintype K]
    {s N : ℕ} [NeZero N] {p : ℝ} {chi : J → ZMod N → ℂ} {chi' : K → ZMod N → ℂ}
    (E : NativeVectorEquivalence s N p chi chi')
    (hunit : ∀ x, ∑ k, ‖chi' k x‖ ^ 2 = 1) (f : I → ZMod N → ℂ)
    (W : NativeVectorCorrelation s N p
      (fun ij : I × J => fun x => f ij.1 x * star (chi ij.2 x))) :
    Nonempty (NativeVectorCorrelation s N (productNiltestBudget (3 * p + 4))
      (fun ik : I × K => fun x => f ik.1 x * star (chi' ik.2 x))) := by
  classical
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  let R (k : K) := Classical.choice (E.expansion W.coordinate.2 k)
  let psi (k : K) (a : Fin (R k).count) (x : ZMod N) : ℂ :=
    star (((R k).test a).evalCyclic N (fun _ => x))
  have hExpansion (k : K) (x : ZMod N) (_hx : x ∈ (Finset.univ : Finset (ZMod N))) :
      star (chi W.coordinate.2 x) * star (star (chi' k x)) =
        ∑ a, star ((R k).coefficient a) * psi k a x := by
    have h := congrArg star ((R k).eval x)
    simpa only [psi, star_sum, star_mul, star_star, mul_comm] using h
  have hCorr : Real.exp (-p) ≤
      ‖𝔼 x ∈ (Finset.univ : Finset (ZMod N)),
        (f W.coordinate.1 x * star (W.test.evalCyclic N (fun _ => x))) *
          star (chi W.coordinate.2 x)‖ := by
    simpa only [mul_assoc, mul_left_comm, mul_comm] using W.correlation
  obtain ⟨k, a, hka⟩ := exists_unit_expansion_correlation Finset.univ
    (fun x => f W.coordinate.1 x * star (W.test.evalCyclic N (fun _ => x)))
    (fun x => star (chi W.coordinate.2 x)) (fun k x => star (chi' k x))
    (fun k a => star ((R k).coefficient a)) psi
    (fun x _ => by simpa only [norm_star] using hunit x) hExpansion
    (Real.exp_pos (-p)) (Real.exp_pos p) (Real.exp_pos p) E.right_dimension
    (fun k => by simpa only [norm_star] using (R k).cost) hCorr
  have hfrac : Real.exp (-p) / (Real.exp p * Real.exp p) = Real.exp (-(3 * p)) := by
    rw [← Real.exp_add, ← Real.exp_sub]
    congr 1
    ring
  rw [hfrac] at hka
  have hpq : p ≤ 3 * p + 4 := by linarith
  let g (ik : I × K) (x : ZMod N) := f ik.1 x * star (chi' ik.2 x)
  let T := (R k).test a
  have hW : NativeVectorCorrelation s N (3 * p + 4)
      (fun iu : (I × K) × Unit => fun x => g iu.1 x * star (T.evalCyclic N (fun _ => x))) := {
    L := W.L
    dim := W.dim
    model := W.model
    test := W.test
    complexity := W.complexity.mono hpq
    coordinate := ((W.coordinate.1, k), ())
    correlation := by
      have h := (Real.exp_le_exp.mpr (show -(3 * p + 4) ≤ -(3 * p) by linarith)).trans hka
      simpa only [g, T, psi, mul_assoc, mul_left_comm, mul_comm] using h
  }
  exact NativeVectorCorrelation.exists_absorb ((R k).model a) (fun _ : Unit => T) g
    (by linarith : 2 ≤ 3 * p + 4) (fun _ => ((R k).complexity a).mono hpq) hW

end Erdos3.NativeVectorEquivalence

end

section

namespace Erdos3.NativeNilsequenceExpansion

open scoped TensorProduct BigOperators

attribute [local instance] NativeVectorCorrelation.lie NativeVectorCorrelation.algebra
  NativeVectorCorrelation.topology NativeVectorCorrelation.topologicalAdd
  NativeVectorCorrelation.continuousSMul NativeVectorCorrelation.hausdorff

theorem absorb_correlation {I : Type*} {s N : ℕ} [NeZero N] {p : ℝ}
    {eta : ZMod N → ℂ} (E : NativeNilsequenceExpansion s N p eta)
    (f : I → ZMod N → ℂ)
    (W : NativeVectorCorrelation s N p (fun i x => f i x * star (eta x))) :
    Nonempty (NativeVectorCorrelation s N (productNiltestBudget (3 * p + 4)) f) := by
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  have hdim : (Fintype.card Unit : ℝ) ≤ Real.exp p := by
    simpa only [Fintype.card_unit, Nat.cast_one] using Real.one_le_exp hp
  let V : NativeVectorEquivalence s N p (fun _ : Unit => eta) (fun _ : Unit => fun _ => 1) := {
    left_dimension := hdim
    right_dimension := hdim
    expansion := fun _ _ => by
      simpa only [star_one, mul_one] using (show Nonempty (NativeNilsequenceExpansion s N p eta) from ⟨E⟩) }
  let W' : NativeVectorCorrelation s N p
      (fun iu : I × Unit => fun x => f iu.1 x * star (eta x)) :=
    { W with coordinate := (W.coordinate, ()) }
  obtain ⟨R⟩ := V.transfer_correlation (fun _ => by simp) f W'
  exact ⟨{ R with
    coordinate := R.coordinate.1
    correlation := by simpa only [star_one, mul_one] using R.correlation }⟩

end Erdos3.NativeNilsequenceExpansion

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeWeightPairRemoval
namespace OAI

section

namespace Erdos3.NativeIntegerExpansion

noncomputable def fourPoint {s : ℕ} {p : ℝ} (f : Fin 4 → ℤ → ℂ)
    (E : ∀ i, NativeIntegerExpansion (fun _ : Unit => 1) s p (fun x => f i (x ())))
    (hp : 2 ≤ p) (δ : ℤ) :
    NativeIntegerExpansion (fun _ : Unit => 1) s (mixedErrorBudget p)
      (fun x => fourPointProduct (f 0) (f 1) (f 2) (f 3) δ (x ())) := by
  have hp0 : 0 ≤ p := le_trans (by norm_num) hp
  have hpair : 2 ≤ mixedErrorPairBudget p := hp.trans (le_mixedErrorPairBudget hp0)
  let E₁₂ := (E 0).conjugate.mul ((E 1).translate δ) hp
  let E₃₄ := (E 2).mul ((E 3).translate δ).conjugate hp
  simpa only [mixedErrorBudget, mixedErrorPairBudget, fourPointProduct, mul_assoc] using E₁₂.mul E₃₄ hpair

end Erdos3.NativeIntegerExpansion

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.IntervalSplitBudget
namespace OAI

section

namespace Erdos3

theorem mixedErrorBudget_mono {p q : ℝ} (hp : 0 ≤ p) (hpq : p ≤ q) :
    mixedErrorBudget p ≤ mixedErrorBudget q := by
  exact mixedErrorPairBudget_mono (hp.trans (le_mixedErrorPairBudget hp))
    (mixedErrorPairBudget_mono hp hpq)

theorem intervalErrorBaseBudget_bounds {p : ℝ} (hp : 0 ≤ p) :
    2 ≤ intervalErrorBaseBudget p ∧ p ≤ intervalErrorBaseBudget p ∧
      mixedErrorBudget (p + 2) ≤ intervalErrorBaseBudget p := by
  have hp2 : 0 ≤ p + 2 := by linarith
  have hpair := hp2.trans (le_mixedErrorPairBudget hp2)
  have hglobal : 0 ≤ mixedErrorBudget (p + 2) := hpair.trans (le_mixedErrorPairBudget hpair)
  unfold intervalErrorBaseBudget
  constructor
  · linarith only [hp, hglobal]
  constructor <;> linarith only [hp, hglobal]

end Erdos3

end

section

namespace Erdos3

theorem intervalErrorBudget_nonneg {K : ℝ} (hK : 0 ≤ K) : 0 ≤ intervalErrorBudget K := by
  have hb : 0 ≤ intervalErrorBaseBudget K := le_trans (by norm_num) (intervalErrorBaseBudget_bounds hK).1
  exact hb.trans (le_mixedErrorPairBudget hb)

theorem intervalSplitInput_bounds {K : ℝ} (hK : 0 ≤ K) :
    2 ≤ intervalSplitInput K ∧ K ≤ intervalSplitInput K ∧
      2 * K ≤ intervalSplitInput K ∧ 2 * intervalErrorBudget K ≤ intervalSplitInput K := by
  have hL := intervalErrorBudget_nonneg hK
  unfold intervalSplitInput
  constructor
  · linarith only [hK, hL]
  constructor
  · linarith only [hK, hL]
  constructor <;> linarith only [hK, hL]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.NativeRankRelationExistence
namespace OAI

section

namespace Erdos3.NativeRankInterval

variable {s r N : ℕ} [NeZero N] {b p q : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {t : ZMod N × ZMod N × ZMod N} {branch : Bool}
  (I : NativeRankInterval W out H t branch p q)

theorem monomialScale_modulus_bound (hp : 0 ≤ p) (α : Unit →₀ ℕ)
    (hα : Finsupp.weight (fun _ : Unit => 1) α ≤ s) :
    monomialScale (fun _ : Unit => (N : ℝ)) α ≤
      Real.exp ((s : ℝ) * p) * monomialScale (fun _ : Unit => (I.length : ℝ)) α := by
  have hN : (0 : ℝ) < N := by exact_mod_cast NeZero.pos N
  have hlength : (0 : ℝ) < I.length := by exact_mod_cast I.length_pos
  have hlower : Real.exp (-p) * (N : ℝ) ≤ I.length :=
    (le_div_iff₀ hN).mp I.length_ratio
  have hratio : (N : ℝ) ≤ Real.exp p * I.length := by
    calc
      (N : ℝ) = Real.exp p * (Real.exp (-p) * N) := by
        rw [← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul]
      _ ≤ Real.exp p * I.length := mul_le_mul_of_nonneg_left hlower (Real.exp_pos _).le
  exact monomialScale_le_exp_mul _ _ (fun _ => hlength) (fun _ => hN) hp
    (fun _ => hratio) α hα

theorem norm_bound_on_modulus {ι : Type*} [Fintype ι]
    (hp : 0 ≤ p) (α : Unit →₀ ℕ) (hα : Finsupp.weight (fun _ : Unit => 1) α ≤ s)
    {M : ℝ} (hM : 0 ≤ M) (x : ι → ℝ)
    (hx : ‖x‖ ≤ M / monomialScale (fun _ : Unit => (I.length : ℝ)) α) :
    ‖x‖ ≤ (M * Real.exp ((s : ℝ) * p)) / monomialScale (fun _ : Unit => (N : ℝ)) α := by
  have hN : (0 : ℝ) < N := by exact_mod_cast NeZero.pos N
  have hlength : (0 : ℝ) < I.length := by exact_mod_cast I.length_pos
  apply hx.trans
  apply (div_le_div_iff₀ (monomialScale_pos _ (fun _ => hlength) α)
    (monomialScale_pos _ (fun _ => hN) α)).mpr
  exact (mul_le_mul_of_nonneg_left (I.monomialScale_modulus_bound hp α hα) hM).trans_eq
    (mul_assoc _ _ _).symm

end Erdos3.NativeRankInterval

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RankIntervalFactorization
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) {G : NilpotentLieFiltration L s}

theorem orbitEquivOfEq_log (h : F = G) (w : σ → ℕ) (g : F.PolynomialOrbit w) :
    (F.orbitEquivOfEq h w g).log = g.log := by
  subst G
  rfl

theorem orbitEquivOfEq_translate (h : F = G) (w : σ → ℕ) (hw : ∀ i, 0 < w i)
    (g : F.PolynomialOrbit w) (a : σ → ℤ) :
    F.orbitEquivOfEq h w (g.translate hw a) = (F.orbitEquivOfEq h w g).translate hw a := by
  subst G
  rfl

end Erdos3.NilpotentLieFiltration

namespace Erdos3.RationalFilteredNilmanifold.DegreeRankStructure

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d r : ℕ}
  {D : RationalFilteredNilmanifold L s d} (R : D.DegreeRankStructure r)

theorem orbitEquiv_log (w : σ → ℕ) (g : D.filtration.realification.PolynomialOrbit w) :
    (R.orbitEquiv w g).log = g.log :=
  D.filtration.realification.orbitEquivOfEq_log R.real_associated.symm w g

theorem orbitEquiv_translate (w : σ → ℕ) (hw : ∀ i, 0 < w i)
    (g : D.filtration.realification.PolynomialOrbit w) (a : σ → ℤ) :
    R.orbitEquiv w (g.translate hw a) = (R.orbitEquiv w g).translate hw a :=
  D.filtration.realification.orbitEquivOfEq_translate R.real_associated.symm w hw g a

end Erdos3.RationalFilteredNilmanifold.DegreeRankStructure

end

section

namespace Erdos3.NativeDegreeRankFamily

open Module
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff

variable {κ A : Type*} {s r : ℕ} {p : ℝ} (W : NativeDegreeRankFamily s r A p)
  (hs : 1 ≤ s) (c : Basis κ ℚ W.L) (τ : κ → ℕ)
  (hG : ∀ j, W.rank.filtration.associatedDegree.layer j = Submodule.span ℚ (c '' {i | j ≤ τ i}))

noncomputable def horizontalCoefficient (α : Unit →₀ ℕ) (a : A) :
    ℝ ⊗[ℚ] W.rank.filtration.HigherHorizontal (Finsupp.weight (fun _ : Unit => 1) α) :=
  Multiplicative.toAdd (W.rank.filtration.nativeHorizontalCoefficientHom hs c τ hG (fun _ => 1) α
    (W.rank.orbitEquiv (fun _ => 1) (W.orbit a)))

theorem fourPointFactors_orbit (out : Fin W.outputDim) (a : Fin 4 → A) (δ : ℤ) (k : Fin 4) :
    (W.fourPointFactors out a δ k).orbit =
      ![W.orbit (a 0), (W.orbit (a 1)).translate (fun _ => Nat.zero_lt_one) (fun _ => δ),
        W.orbit (a 2), (W.orbit (a 3)).translate (fun _ => Nat.zero_lt_one) (fun _ => δ)] k := by
  fin_cases k <;> rfl

theorem fourPoint_horizontalCoefficient (out : Fin W.outputDim) (a : Fin 4 → A)
    (δ : ℤ) (α : Unit →₀ ℕ) (k : Fin 4) :
    Multiplicative.toAdd (W.rank.filtration.nativeHorizontalCoefficientHom hs c τ hG (fun _ => 1) α
      (W.rank.orbitEquiv (fun _ => 1) (W.fourPointFactors out a δ k).orbit)) =
        W.horizontalCoefficient hs c τ hG α (a k) := by
  rw [W.fourPointFactors_orbit]
  fin_cases k
  · rfl
  · have h := congrArg
      (fun g : W.rank.filtration.realification.associatedDegree.PolynomialOrbit (fun _ : Unit => 1) =>
        W.rank.filtration.nativeHorizontalCoefficientHom hs c τ hG (fun _ => 1) α g)
      (W.rank.orbitEquiv_translate (fun _ : Unit => 1) (fun _ => Nat.zero_lt_one)
        (W.orbit (a 1)) (fun _ => δ))
    exact congrArg Multiplicative.toAdd (h.trans
      (W.rank.filtration.nativeHorizontalCoefficientHom_translate hs c τ hG
        (fun _ : Unit => 1) (fun _ => Nat.zero_lt_one) α
        (W.rank.orbitEquiv (fun _ => 1) (W.orbit (a 1))) (fun _ => δ)))
  · rfl
  · have h := congrArg
      (fun g : W.rank.filtration.realification.associatedDegree.PolynomialOrbit (fun _ : Unit => 1) =>
        W.rank.filtration.nativeHorizontalCoefficientHom hs c τ hG (fun _ => 1) α g)
      (W.rank.orbitEquiv_translate (fun _ : Unit => 1) (fun _ => Nat.zero_lt_one)
        (W.orbit (a 3)) (fun _ => δ))
    exact congrArg Multiplicative.toAdd (h.trans
      (W.rank.filtration.nativeHorizontalCoefficientHom_translate hs c τ hG
        (fun _ : Unit => 1) (fun _ => Nat.zero_lt_one) α
        (W.rank.orbitEquiv (fun _ => 1) (W.orbit (a 3))) (fun _ => δ)))

end Erdos3.NativeDegreeRankFamily

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RankProductOrbitCoefficients
namespace OAI

section

namespace Erdos3.NativeRankInterval

open RationalFilteredNilmanifold VectorPolynomial
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

theorem rankProjection_coefficient (α : Unit →₀ ℕ) (k : Fin 4) :
    (LinearMap.proj k).baseChange ℝ
        ((I.rankProjection i).toLinearMap.baseChange ℝ (coefficients (I.productOrbit i).log α)) =
      coefficients ((W.fourPointFactors out (rankQuadrupleParameters t)
        (cyclicBranchOffset t.1 branch) ((![1, 2, 0, 3] : Fin 4 → Fin 4) k)).orbit).log α := by
  change realificationLieHom (liePiEval k)
    (realificationLieHom (I.rankProjection i) (coefficients (I.productOrbit i).log α)) = _
  have h := realification_liePiEval_liePiMap (M := fun _ : Fin 4 => W.L)
    (fun j : Fin 4 => (liePiEval (some ((![1, 2, 0, 3] : Fin 4 → Fin 4) j)) :
      (∀ a : Option (Fin 4), optionLieSpace (I.expansion.L i) (fun _ : Fin 4 => W.L) a) →ₗ⁅ℚ⁆ W.L))
    (coefficients (I.productOrbit i).log α) k
  apply h.trans
  exact NilpotentLieFiltration.piRealOrbit_coefficient
    (fun j => (I.productModels i j).filtration) (fun j => (I.productTests i j).orbit)
    α (some ((![1, 2, 0, 3] : Fin 4 → Fin 4) k))

theorem rankProjection_component_log (k : Fin 4) :
    VectorPolynomial.map
        ((realificationLieHom ((liePiEval k).comp (I.rankProjection i))).toLinearMap.restrictScalars ℚ)
        (I.productOrbit i).log =
      (W.fourPointFactors out (rankQuadrupleParameters t) (cyclicBranchOffset t.1 branch)
        ((![1, 2, 0, 3] : Fin 4 → Fin 4) k)).orbit.log := by
  apply coefficients.injective
  ext α
  rw [coefficients_map]
  change ((LinearMap.proj k).comp (I.rankProjection i).toLinearMap).baseChange ℝ
    (coefficients (I.productOrbit i).log α) = _
  rw [LinearMap.baseChange_comp, LinearMap.comp_apply]
  exact I.rankProjection_coefficient i α k

end Erdos3.NativeRankInterval

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.NativeCoefficientKernel
namespace OAI

section

namespace Erdos3.NativeRankInterval

open RationalFilteredNilmanifold
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
  (I : NativeRankInterval W out H t branch p q)

noncomputable def projectedCoefficient (i : Fin I.expansion.count) (α : Unit →₀ ℕ) :
    (pi (I.productModels i)).filtration.PolynomialSymbol (fun _ : Unit => 1) →ₗ[ℚ]
      (Fin 4 → W.rank.filtration.HigherHorizontal (Finsupp.weight (fun _ : Unit => 1) α)) :=
  W.rank.filtration.projectedHorizontalSymbolCoefficient (pi (I.productModels i)).filtration
    (I.rankProjection i) (I.rankProjection_mem_layer i) (fun _ => 1) α

namespace SunflowerWitness

variable {I} {P : ℝ} (D : I.SunflowerWitness P)

theorem exists_projected_corrections (hs : 1 ≤ s) :
    ∃ E R : (pi (I.productModels D.index)).filtration.RealPolynomialSymbolGroup (fun _ : Unit => 1),
      (pi (I.productModels D.index)).filtration.SymbolSlowBound
        D.adapted.basis D.adapted.weight D.adapted.layers (fun _ => 1)
        (fun _ => (I.length : ℝ)) (Real.exp P) E ∧
      (pi (I.productModels D.index)).filtration.SymbolRationalGrid
        D.adapted.basis D.adapted.weight D.adapted.layers (fun _ => 1) D.denominator R ∧
      ∀ α : Unit →₀ ℕ,
        (I.projectedCoefficient D.index α).baseChange ℝ
            (I.productSymbol D.index D.adapted.basis D.adapted.weight D.adapted.layers).coord -
          (I.projectedCoefficient D.index α).baseChange ℝ E.coord -
          (I.projectedCoefficient D.index α).baseChange ℝ R.coord ∈
        (I.refilteredHorizontalImage D.index D.subalgebra (Finsupp.weight (fun _ : Unit => 1) α)).baseChange ℝ := by
  exact W.rank.filtration.projectedHorizontal_factorization (pi (I.productModels D.index)).filtration
    (I.rankProjection D.index) (I.rankProjection_mem_layer D.index) hs
    D.adapted.basis D.adapted.weight D.adapted.layers (fun _ => (I.length : ℝ))
    (I.productSymbol D.index D.adapted.basis D.adapted.weight D.adapted.layers)
    P D.denominator D.subalgebra D.factorization

end SunflowerWitness

end Erdos3.NativeRankInterval

end

section

namespace Erdos3.NativeRankInterval.SunflowerWitness

open Module RationalFilteredNilmanifold VectorPolynomial
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {t : ZMod N × ZMod N × ZMod N} {branch : Bool}
  {I : NativeRankInterval W out H t branch p q} (D : I.SunflowerWitness P)

noncomputable def projectedRepresentative
    (X : (pi (I.productModels D.index)).filtration.RealPolynomialSymbolGroup (fun _ : Unit => 1))
    (α : Unit →₀ ℕ) : ℝ ⊗[ℚ] (Fin 4 → W.L) :=
  (I.rankProjection D.index).toLinearMap.baseChange ℝ
    (coefficients ((pi (I.productModels D.index)).filtration.realSymbolRepresentative
      D.adapted.basis D.adapted.weight D.adapted.layers (fun _ => 1) X.coord) α)

end Erdos3.NativeRankInterval.SunflowerWitness

end

section

namespace Erdos3.NativeRankInterval.SunflowerWitness

open Module RationalFilteredNilmanifold VectorPolynomial
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {t : ZMod N × ZMod N × ZMod N} {branch : Bool}
  {I : NativeRankInterval W out H t branch p q} (D : I.SunflowerWitness P)

theorem projectedRepresentative_mem
    (X : (pi (I.productModels D.index)).filtration.RealPolynomialSymbolGroup (fun _ : Unit => 1))
    (α : Unit →₀ ℕ) : D.projectedRepresentative X α ∈
      (W.rank.filtration.fourHorizontalLayer (Finsupp.weight (fun _ : Unit => 1) α)).baseChange ℝ := by
  have h := W.rank.filtration.real_projectedCoefficient_mem (pi (I.productModels D.index)).filtration
    (I.rankProjection D.index) (I.rankProjection_mem_layer D.index)
    D.adapted.basis D.adapted.weight D.adapted.layers (fun _ => 1) α
    ((pi (I.productModels D.index)).filtration.realAdaptedSymbolRepresentative
      D.adapted.basis D.adapted.weight D.adapted.layers (fun _ => 1) X.coord)
  convert h using 2
  dsimp only [projectedRepresentative, NilpotentLieFiltration.realAdaptedSymbolRepresentative]

noncomputable def projectedRepresentativeLayer
    (X : (pi (I.productModels D.index)).filtration.RealPolynomialSymbolGroup (fun _ : Unit => 1))
    (α : Unit →₀ ℕ) :
    (W.rank.filtration.fourHorizontalLayer (Finsupp.weight (fun _ : Unit => 1) α)).baseChange ℝ :=
  ⟨D.projectedRepresentative X α, D.projectedRepresentative_mem X α⟩

theorem projectedRepresentative_horizontal
    (X : (pi (I.productModels D.index)).filtration.RealPolynomialSymbolGroup (fun _ : Unit => 1))
    (α : Unit →₀ ℕ) :
    W.rank.filtration.realFourHorizontalMap (Finsupp.weight (fun _ : Unit => 1) α)
        (D.projectedRepresentativeLayer X α) =
      (I.projectedCoefficient D.index α).baseChange ℝ X.coord := by
  have h := W.rank.filtration.real_projectedCoefficient_horizontal
    (pi (I.productModels D.index)).filtration (I.rankProjection D.index)
    (I.rankProjection_mem_layer D.index) D.adapted.basis D.adapted.weight D.adapted.layers
    (fun _ => 1) α ((pi (I.productModels D.index)).filtration.realAdaptedSymbolRepresentative
      D.adapted.basis D.adapted.weight D.adapted.layers (fun _ => 1) X.coord)
    (D.projectedRepresentativeLayer X α) (by
      dsimp only [projectedRepresentativeLayer, projectedRepresentative,
        NilpotentLieFiltration.realAdaptedSymbolRepresentative])
  rwa [NilpotentLieFiltration.realPolynomialSymbolMap_representative] at h

theorem projectedOrbitCoefficient_horizontal (α : Unit →₀ ℕ) :
    W.rank.filtration.realFourHorizontalMap (Finsupp.weight (fun _ : Unit => 1) α)
        (D.projectedOrbitCoefficient α) =
      (I.projectedCoefficient D.index α).baseChange ℝ
        (I.productSymbol D.index D.adapted.basis D.adapted.weight D.adapted.layers).coord := by
  exact W.rank.filtration.real_projectedCoefficient_horizontal
    (pi (I.productModels D.index)).filtration (I.rankProjection D.index)
    (I.rankProjection_mem_layer D.index) D.adapted.basis D.adapted.weight D.adapted.layers
    (fun _ => 1) α ⟨(I.productOrbit D.index).log, (I.productOrbit D.index).property⟩
    (D.projectedOrbitCoefficient α) rfl

end Erdos3.NativeRankInterval.SunflowerWitness

end

section

namespace Erdos3.NativeRankInterval.SunflowerWitness

open Module RationalFilteredNilmanifold
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {κ : Type*} {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {t : ZMod N × ZMod N × ZMod N} {branch : Bool}
  {I : NativeRankInterval W out H t branch p q} (D : I.SunflowerWitness P)
  (hs : 1 ≤ s) (c : Basis κ ℚ W.L) (τ : κ → ℕ)
  (hG : ∀ j, W.rank.filtration.associatedDegree.layer j = Submodule.span ℚ (c '' {i | j ≤ τ i}))

theorem projectedSymbol_native_component (α : Unit →₀ ℕ) (k : Fin 4) :
    (LinearMap.proj k).baseChange ℝ
        ((I.projectedCoefficient D.index α).baseChange ℝ
          (I.productSymbol D.index D.adapted.basis D.adapted.weight D.adapted.layers).coord) =
      W.horizontalCoefficient hs c τ hG α
        (rankQuadrupleParameters t ((![1, 2, 0, 3] : Fin 4 → Fin 4) k)) := by
  have h := W.rank.filtration.projectedHorizontalSymbolCoefficient_native
    (pi (I.productModels D.index)).filtration (I.rankProjection D.index)
    (I.rankProjection_mem_layer D.index) hs D.adapted.basis D.adapted.weight D.adapted.layers
    c τ hG (fun _ : Unit => 1) α
    ⟨(I.productOrbit D.index).log, (I.productOrbit D.index).property⟩
    (W.rank.orbitEquiv (fun _ => 1)
      (W.fourPointFactors out (rankQuadrupleParameters t) (cyclicBranchOffset t.1 branch)
        ((![1, 2, 0, 3] : Fin 4 → Fin 4) k)).orbit) k (by
      exact (I.rankProjection_component_log D.index k).trans
        (W.rank.orbitEquiv_log (fun _ : Unit => 1)
          (W.fourPointFactors out (rankQuadrupleParameters t) (cyclicBranchOffset t.1 branch)
            ((![1, 2, 0, 3] : Fin 4 → Fin 4) k)).orbit).symm)
  exact h.trans (W.fourPoint_horizontalCoefficient hs c τ hG out
    (rankQuadrupleParameters t) (cyclicBranchOffset t.1 branch) α
    ((![1, 2, 0, 3] : Fin 4 → Fin 4) k))

theorem projectedOrbitCoefficient_native_component (α : Unit →₀ ℕ) (k : Fin 4) :
    (LinearMap.proj k).baseChange ℝ
        (W.rank.filtration.realFourHorizontalMap (Finsupp.weight (fun _ : Unit => 1) α)
          (D.projectedOrbitCoefficient α)) =
      W.horizontalCoefficient hs c τ hG α
        (rankQuadrupleParameters t ((![1, 2, 0, 3] : Fin 4 → Fin 4) k)) := by
  exact (congrArg ((LinearMap.proj k).baseChange ℝ) (D.projectedOrbitCoefficient_horizontal α)).trans
    (D.projectedSymbol_native_component hs c τ hG α k)

end Erdos3.NativeRankInterval.SunflowerWitness

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RankHorizontalRepresentatives
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.DegreeRankStructure

open Module

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s n r : ℕ}
  {D : RationalFilteredNilmanifold L s n} (R : D.DegreeRankStructure r)

theorem exists_rank_two_basis (d : Fin (s + 1)) (hd : 1 ≤ d.val) {p : ℝ}
    (hR : R.ComplexityLE p) :
    ∃ b : Basis (Fin (finrank ℚ (R.filtration.layer d.val 2))) ℚ (R.filtration.layer d.val 2),
      ∀ j k, rationalLogHeight (D.basis.repr (b j : L) k) ≤ p := by
  by_cases hs : 2 < s + 1
  · exact ⟨R.basis d ⟨2, hs⟩, hR.2 d ⟨2, hs⟩⟩
  · have hbot : R.filtration.layer d.val 2 = ⊥ := by
      apply bot_unique
      calc
        R.filtration.layer d.val 2 ≤ R.filtration.layer s (r + 1) :=
          R.filtration.lex_antitone (Or.inr ⟨by omega, by have hr := R.filtration.rank_le_degree; omega⟩)
        _ = ⊥ := R.filtration.terminal
    let : FiniteDimensional ℚ L := D.basis.finiteDimensional_of_finite
    let b := Module.finBasis ℚ (R.filtration.layer d.val 2)
    refine ⟨b, fun j k => ?_⟩
    have hb : (b j : L) = 0 := by
      have h := (b j).property
      simpa only [hbot, Submodule.mem_bot] using h
    rw [hb]
    simpa [rationalLogHeight] using (Nat.cast_nonneg n).trans hR.1.1

theorem exists_horizontal_ambient_basis (d : Fin (s + 1)) (hd : 1 ≤ d.val)
    {p : ℝ} (hp : 0 ≤ p) (hR : R.ComplexityLE p) :
    ∃ H : ℕ, 1 ≤ H ∧ (H : ℝ) ≤ Real.exp ((p + 3) ^ 7) ∧
      ∃ m : ℕ, m ≤ n ∧ ∃ f : Basis (Fin m) ℚ (L ⧸ R.filtration.layer d.val 2),
        ∀ i j, RationalHeightLE (f.repr ((R.filtration.layer d.val 2).mkQ (D.basis j)) i) H := by
  let : FiniteDimensional ℚ L := D.basis.finiteDimensional_of_finite
  obtain ⟨b, hb⟩ := R.exists_rank_two_basis d hd hR
  have hdim : (finrank ℚ (R.filtration.layer d.val 2) : ℝ) ≤ p + 1 := by
    calc
      _ ≤ (finrank ℚ L : ℝ) := by exact_mod_cast Submodule.finrank_le (R.filtration.layer d.val 2)
      _ = n := by rw [finrank_eq_card_basis D.basis, Fintype.card_fin]
      _ ≤ p + 1 := hR.1.1.trans (by linarith)
  obtain ⟨H, hH, hHp, m, hm, f, hf⟩ := exists_submodule_quotient_basis_exp D.basis
    (R.filtration.layer d.val 2) (fun j => (b j : L))
    (span_submodule_basis (R.filtration.layer d.val 2) b) (one_le_ceil_exp p)
    (fun j k => rationalHeightLE_ceil_exp (hb j k)) (by linarith : 0 ≤ p + 1)
    (by simpa only [Fintype.card_fin] using hdim) (ceil_exp_le_exp_add_one hp)
  refine ⟨H, hH, ?_, m, ?_, f, hf⟩
  · convert hHp using 2
    ring
  · simpa only [Fintype.card_fin] using hm

end Erdos3.RationalFilteredNilmanifold.DegreeRankStructure

end

section

namespace Erdos3.RationalFilteredNilmanifold.DegreeRankStructure

open Module
open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s n r : ℕ}
  {D : RationalFilteredNilmanifold L s n} (R : D.DegreeRankStructure r)

theorem exists_controlled_horizontal_representatives
    {σ : Type*} (d : Fin (s + 1)) (hd : 1 ≤ d.val)
    {p : ℝ} (hp : 0 ≤ p) (hR : R.ComplexityLE p)
    {t : ℕ} (ht : t ≤ n) (f : Basis (Fin t) ℚ (L ⧸ R.filtration.layer d.val 2))
    (hf : ∀ i j, rationalLogHeight (f.repr ((R.filtration.layer d.val 2).mkQ (D.basis j)) i) ≤ p)
    {l : ℕ} (hl : 0 < l) (hlp : (l : ℝ) ≤ Real.exp p)
    (T : σ → ℝ) (hT : ∀ i, Real.exp (separationBudget ((p + 3) ^ 4)) ≤ T i) :
    let P : ℝ := (p + 3) ^ 4
    ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp (P + ((P + 2) ^ 3 + (P + 2) ^ 36)) ∧ l ∣ m ∧
      ∀ (α : σ →₀ ℕ), α ≠ 0 →
        ∀ (x y z : ℝ ⊗[ℚ] R.filtration.HigherHorizontal d.val) (a q : Fin t → ℝ),
        R.filtration.realHigherHorizontalCoordinates d.val f (x - y - z) = a + q →
        ‖a‖ ≤ Real.exp P / monomialScale T α → q ∈ realDenominatorGrid l →
        ∃ E Q : (R.filtration.layer d.val 1).baseChange ℝ,
          R.filtration.realHigherHorizontalCoordinates d.val f
            (R.filtration.realHorizontalMap d.val E) = a ∧
          R.filtration.realHigherHorizontalCoordinates d.val f
            (R.filtration.realHorizontalMap d.val Q) = q ∧
          x - y - R.filtration.realHorizontalMap d.val E -
            R.filtration.realHorizontalMap d.val Q = z ∧
          ‖(D.basis.baseChange ℝ).equivFun E.val‖ ≤
            Real.exp ((P + 2) ^ 3 + (P + 2) ^ 18 + P) / monomialScale T α ∧
          (D.basis.baseChange ℝ).equivFun Q.val ∈ realDenominatorGrid m := by
  let : FiniteDimensional ℚ L := D.basis.finiteDimensional_of_finite
  let b := R.basis d ⟨1, by omega⟩
  let v : Fin (finrank ℚ (R.filtration.layer d.val 1)) → L := fun j => b j
  let K := ⌈Real.exp p⌉₊
  let H := max K ((n + 1) * (K * K) ^ n)
  let P : ℝ := (p + 3) ^ 4
  have hP : p + 1 ≤ P := by
    simpa only [P, show p + 1 + 2 = p + 3 by ring] using
      le_power_budget (p := p + 1) (by linarith) (by decide : 1 ≤ 4)
  have hpP : p ≤ P := (by linarith : p ≤ p + 1).trans hP
  have hn : (n : ℝ) ≤ p := hR.1.1
  have hvdim : finrank ℚ (R.filtration.layer d.val 1) ≤ n := by
    simpa only [finrank_eq_card_basis D.basis, Fintype.card_fin] using
      Submodule.finrank_le (R.filtration.layer d.val 1)
  have hH : 1 ≤ H := (one_le_ceil_exp p).trans (Nat.le_max_left _ _)
  have hHP : (H : ℝ) ≤ Real.exp P := by
    change ((max K (replicatedFrequencyHeight n K) : ℕ) : ℝ) ≤ Real.exp P
    rw [Nat.cast_max]
    exact max_le ((ceil_exp_le_exp_add_one hp).trans (Real.exp_le_exp.mpr hP))
      (replicatedFrequencyHeight_ceil_exp n hp hn)
  have hvH : ∀ j i, RationalHeightLE (D.basis.repr (v j) i) H := by
    intro j i
    exact (rationalHeightLE_ceil_exp (hR.2 d ⟨1, by omega⟩ j i)).mono (Nat.le_max_left _ _)
  have hfH : ∀ j i,
      RationalHeightLE (R.filtration.ambientHorizontalCoordinates d.val f (v j) i) H := by
    intro j i
    have h := linearMap_coordinate_height D.basis f (R.filtration.layer d.val 2).mkQ
      (fun j i => rationalHeightLE_ceil_exp (hf i j)) (v j)
      (fun i => rationalHeightLE_ceil_exp (hR.2 d ⟨1, by omega⟩ j i)) i
    exact (show RationalHeightLE
      (R.filtration.ambientHorizontalCoordinates d.val f (v j) i)
      ((n + 1) * (K * K) ^ n) from by
        simpa only [Fintype.card_fin, DegreeRankLieFiltration.ambientHorizontalCoordinates,
          LinearMap.comp_apply, LinearEquiv.coe_coe, Basis.equivFun_apply] using h).mono
        (Nat.le_max_right _ _)
  exact R.filtration.exists_controlled_horizontal_lifts d.val f D.basis v
    (span_submodule_basis _ b) hH hl hvH hfH (hp.trans hpP)
    (by simpa only [Fintype.card_fin] using hn.trans hpP)
    (by simpa only [Fintype.card_fin] using (Nat.cast_le.mpr ht).trans (hn.trans hpP))
    (by simpa only [Fintype.card_fin] using (Nat.cast_le.mpr hvdim).trans (hn.trans hpP))
    hHP (hlp.trans (Real.exp_le_exp.mpr hpP)) T hT

end Erdos3.RationalFilteredNilmanifold.DegreeRankStructure

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RankNativeCoordinates
namespace OAI

section

namespace Erdos3.NativeRankInterval.SunflowerWitness

open Module RationalFilteredNilmanifold

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {ι κ : Type*} [Fintype ι] {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {t : ZMod N × ZMod N × ZMod N} {branch : Bool}
  {I : NativeRankInterval W out H t branch p q}

theorem projectedOrbitCoefficient_native_coordinates (D : I.SunflowerWitness P)
    (hs : 1 ≤ s) (c : Basis κ ℚ W.L) (τ : κ → ℕ)
    (hG : ∀ j, W.rank.filtration.associatedDegree.layer j = Submodule.span ℚ (c '' {i | j ≤ τ i}))
    (α : Unit →₀ ℕ)
    (f : Basis ι ℚ (W.L ⧸ W.rank.filtration.layer (Finsupp.weight (fun _ : Unit => 1) α) 2))
    (k : Fin 4) (i : ι) :
    W.rank.filtration.realFourAmbientCoordinates (Finsupp.weight (fun _ : Unit => 1) α) f
        (D.projectedOrbitCoefficient α).val ⟨k, i⟩ =
      (f.baseChange ℝ).repr
        ((W.rank.filtration.higherHorizontalAmbient (Finsupp.weight (fun _ : Unit => 1) α)).baseChange ℝ
          (W.horizontalCoefficient hs c τ hG α
            (rankQuadrupleParameters t ((![1, 2, 0, 3] : Fin 4 → Fin 4) k)))) i := by
  have hmap := congrFun (W.rank.filtration.realFourHorizontalCoordinates_map
    (Finsupp.weight (fun _ : Unit => 1) α) f (D.projectedOrbitCoefficient α)).symm ⟨k, i⟩
  have hcomponent := W.rank.filtration.realFourHorizontalCoordinates_component
    (Finsupp.weight (fun _ : Unit => 1) α) f
    (W.rank.filtration.realFourHorizontalMap (Finsupp.weight (fun _ : Unit => 1) α)
      (D.projectedOrbitCoefficient α)) k i
  exact hmap.trans (hcomponent.trans (congrArg
    (fun x => (f.baseChange ℝ).repr
      ((W.rank.filtration.higherHorizontalAmbient (Finsupp.weight (fun _ : Unit => 1) α)).baseChange ℝ x) i)
    (D.projectedOrbitCoefficient_native_component hs c τ hG α k)))

end Erdos3.NativeRankInterval.SunflowerWitness

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.BoundedNativeDependentApproximations
namespace OAI

section

namespace Erdos3

open Module RationalFilteredNilmanifold

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

namespace NativeDegreeRankFamily

noncomputable def nativeCoefficientCoordinates
    {ι κ : Type*} [Fintype ι] {s r N : ℕ} [NeZero N] {b : ℝ}
    (W : NativeDegreeRankFamily s r (ZMod N) b) (hs : 1 ≤ s)
    (c : Basis κ ℚ W.L) (τ : κ → ℕ)
    (hG : ∀ j, W.rank.filtration.associatedDegree.layer j = Submodule.span ℚ (c '' {i | j ≤ τ i}))
    (α : Unit →₀ ℕ)
    (f : Basis ι ℚ (W.L ⧸ W.rank.filtration.layer (Finsupp.weight (fun _ : Unit => 1) α) 2)) :
    ZMod N → ι → ℝ :=
  fun h i => (f.baseChange ℝ).repr
    ((W.rank.filtration.higherHorizontalAmbient (Finsupp.weight (fun _ : Unit => 1) α)).baseChange ℝ
      (W.horizontalCoefficient hs c τ hG α h)) i

end NativeDegreeRankFamily

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.CommonRealDependentProjection
namespace OAI

section

namespace Erdos3

open Module RationalFilteredNilmanifold
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

namespace NativeDegreeRankFamily

theorem nativeCoefficientCoordinates_eq_real
    {ι κ : Type*} [Fintype ι] {s r N : ℕ} [NeZero N] {b : ℝ}
    (W : NativeDegreeRankFamily s r (ZMod N) b) (hs : 1 ≤ s)
    (c : Basis κ ℚ W.L) (τ : κ → ℕ)
    (hG : ∀ j, W.rank.filtration.associatedDegree.layer j = Submodule.span ℚ (c '' {i | j ≤ τ i}))
    (α : Unit →₀ ℕ)
    (f : Basis ι ℚ (W.L ⧸ W.rank.filtration.layer (Finsupp.weight (fun _ : Unit => 1) α) 2))
    (h : ZMod N) :
    W.nativeCoefficientCoordinates hs c τ hG α f h =
      W.rank.filtration.realHigherHorizontalCoordinates (Finsupp.weight (fun _ : Unit => 1) α) f
        (W.horizontalCoefficient hs c τ hG α h) := by
  funext i
  exact (W.rank.filtration.realHigherHorizontalCoordinates_component
    (Finsupp.weight (fun _ : Unit => 1) α) f (W.horizontalCoefficient hs c τ hG α h) i).symm

end NativeDegreeRankFamily

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeCoveredCommonFactorization
namespace OAI

section

namespace Erdos3

open Module RationalFilteredNilmanifold VectorPolynomial
open scoped TensorProduct

namespace NilpotentLieFiltration

theorem polynomialOrbitEval_zero_iff_coefficient_zero
    {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (w : σ → ℕ) (g : F.PolynomialOrbit w) :
    F.polynomialOrbitEval w 0 g = 1 ↔ coefficients g.log 0 = 0 := by
  constructor
  · intro h
    have hc := congrArg NilpotentLieBCHGroup.coord h
    simpa only [F.polynomialOrbitEval_coord, Pi.zero_apply, Int.cast_zero,
      eval_zero_eq_coefficient, NilpotentLieBCHGroup.coord_one] using hc
  · intro h
    apply NilpotentLieBCHGroup.ext
    simpa only [F.polynomialOrbitEval_coord, Pi.zero_apply, Int.cast_zero,
      eval_zero_eq_coefficient, NilpotentLieBCHGroup.coord_one] using h

end NilpotentLieFiltration

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

end Erdos3

end

section

namespace Erdos3

open Module VectorPolynomial

namespace VectorPolynomial

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]

theorem CoefficientBound.add (b : Basis ι ℝ L) (T : σ → ℝ) {M N : ℝ}
    {P Q : VectorPolynomial σ ℚ L} (hP : CoefficientBound b T M P) (hQ : CoefficientBound b T N Q) :
    CoefficientBound b T (M + N) (P + Q) := by
  intro α i
  simp only [map_add, Finsupp.add_apply]
  exact (abs_add_le _ _).trans ((add_le_add (hP α i) (hQ α i)).trans_eq (add_div _ _ _).symm)

theorem CoefficientGrid.add (b : Basis ι ℝ L) (l : ℕ)
    {P Q : VectorPolynomial σ ℚ L} (hP : CoefficientGrid b l P) (hQ : CoefficientGrid b l Q) :
    CoefficientGrid b l (P + Q) := by
  intro α
  obtain ⟨a, ha⟩ := hP α
  obtain ⟨c, hc⟩ := hQ α
  refine ⟨a + c, ?_⟩
  funext i
  simp only [Pi.add_apply, Int.cast_add, map_add, Finsupp.add_apply]
  change (a i : ℝ) + (c i : ℝ) =
    (l : ℝ) * (b.repr (coefficients P α) i + b.repr (coefficients Q α) i)
  exact (congrArg₂ (· + ·) (congrFun ha i) (congrFun hc i)).trans (mul_add _ _ _).symm

end VectorPolynomial

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeSubspaceFreeModel
namespace OAI

section

namespace Erdos3.VectorPolynomial

variable {V W : Type*} [AddCommGroup V] [Module ℚ V]
  [AddCommGroup W] [Module ℚ W] {s : ℕ}

theorem map_positiveUnivariate (f : V →ₗ[ℚ] W) (v : Fin s → V) :
    map f (positiveUnivariate v) = positiveUnivariate (fun d => f (v d)) := by
  simp only [positiveUnivariate, map_sum, map_monomial]

theorem positiveUnivariate_reconstruct (p : VectorPolynomial Unit ℚ V)
    (hp : DegreeLE (fun _ : Unit => 1) s p) (hzero : coefficients p 0 = 0) :
    positiveUnivariate (fun d : Fin s => coefficients p (Finsupp.single () (d.val + 1))) = p := by
  apply coefficients.injective
  ext α
  have hα : Finsupp.single () (α ()) = α := by
    apply Finsupp.ext
    intro u
    cases u
    simp
  have hweight : Finsupp.weight (fun _ : Unit => 1) α = α () := by
    rw [← hα]
    simp [Finsupp.weight_single]
  by_cases h0 : α () = 0
  · have hz : α = 0 := by simpa only [h0, Finsupp.single_zero] using hα.symm
    rw [hz, positiveUnivariate_zero, hzero]
  · by_cases hle : α () ≤ s
    · let d : Fin s := ⟨α () - 1, by omega⟩
      have hd : d.val + 1 = α () := by dsimp only [d]; omega
      have he : Finsupp.single () (d.val + 1) = α := by rw [hd]; exact hα
      rw [← he, positiveUnivariate_coefficient]
    · have hhigh : s < Finsupp.weight (fun _ : Unit => 1) α := by rw [hweight]; omega
      rw [hp α hhigh]
      apply positiveUnivariate_coefficient_eq_zero
      intro d he
      have hv := congrArg (fun β : Unit →₀ ℕ => β ()) he
      simp only [Finsupp.single_eq_same] at hv
      omega

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.MarkedPolynomialGenerators
namespace OAI

section

namespace Erdos3

open VectorPolynomial

variable {I σ L : Type*} [LieRing L] [LieAlgebra ℚ L]

noncomputable def markedPolynomialAlgebra (v : I → L) (w : I → ℕ) (marked : I → Bool) :
    LieSubalgebra ℚ (VectorPolynomial σ ℚ L) :=
  { markedPolynomialLayer (σ := σ) v w marked 0 0 0 with
    lie_mem' := by
      intro p q hp hq
      change ⁅p, q⁆ ∈ markedPolynomialLayer v w marked 0 0 0
      exact markedPolynomialLayer_lie_mem v w marked
        (d := 0) (e := 0) (k := 0) (m := 0) (l := 0) (n := 0) hp hq }

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.CommonAffineOrbitEvaluation
namespace OAI

section

namespace Erdos3

open VectorPolynomial
open scoped BigOperators TensorProduct

namespace VectorPolynomial

variable {σ L : Type*} [AddCommGroup L] [Module ℚ L]

noncomputable def monomialLinearMap (α : σ →₀ ℕ) : L →ₗ[ℚ] VectorPolynomial σ ℚ L where
  toFun := monomial α
  map_add' x y := by simp only [monomial, TensorProduct.tmul_add]
  map_smul' a x := by
    change monomial α (a • x) = a • monomial α x
    simp only [monomial, TensorProduct.tmul_smul]

noncomputable def realAffinePolynomial [Fintype σ] (x : ℝ ⊗[ℚ] L) (y : σ → ℝ ⊗[ℚ] L) :
    ℝ ⊗[ℚ] VectorPolynomial σ ℚ L :=
  (monomialLinearMap (0 : σ →₀ ℕ)).baseChange ℝ x +
    ∑ i, (monomialLinearMap (Finsupp.single i 1)).baseChange ℝ (y i)

end VectorPolynomial

variable {I σ L : Type*} [LieRing L] [LieAlgebra ℚ L]

theorem realMonomial_mem_markedPolynomialLayer
    (v : I → L) (w : I → ℕ) (marked : I → Bool) (d k l : ℕ) (α : σ →₀ ℕ)
    {x : ℝ ⊗[ℚ] L}
    (hx : x ∈ (markedLieSpan v w marked d (k + Finsupp.weight (fun _ : σ => 1) α) l).baseChange ℝ) :
    (monomialLinearMap α).baseChange ℝ x ∈
      (markedPolynomialLayer v w marked d k l).baseChange ℝ := by
  have hmap : (markedLieSpan v w marked d (k + Finsupp.weight (fun _ : σ => 1) α) l).map
      (monomialLinearMap α) ≤ markedPolynomialLayer v w marked d k l := by
    rintro z ⟨y, hy, rfl⟩
    exact monomial_mem_markedPolynomialLayer v w marked d k l α hy
  have h := Submodule.baseChange_mono ℝ hmap
  rw [realification_map] at h
  exact h ⟨x, hx, rfl⟩

end Erdos3

end

end OAI
end


