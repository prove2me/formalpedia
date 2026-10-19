-- Prove2me | Definitions.Def_OAIE3v2B181
-- name    : OAIE3v2B181
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T11:40:43.082792+00:00
-- url     : https://prove2.me/theorems/868c0da1-8112-4ef2-b937-bbf220f867dc
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 184 of 311
-- statement:
--   Definitions bundle 184 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B161`, `OAIE3v2B162`, `OAIE3v2B163`, `OAIE3v2B164`, `OAIE3v2B165`, `OAIE3v2B166`, `OAIE3v2B170` of this split.
--
--   Modules: `Estimates/BiasedNativeTerminal.lean`, `Estimates/BiasedSynchronizedSquareFamily.lean`, `Estimates/GradedUnitEvaluation.lean`, `Estimates/NativeOptionFixedSourceQuotientMarkStrong.lean`, `Estimates/NativeOrbitFreezing.lean`, `Estimates/NativeSharedFrozenCorrelations.lean`, `Estimates/NativeSubspaceFreeModel.lean`, `Estimates/NativeWeightPairRemoval.lean`, `Estimates/SourceUnitCover.lean`, `Estimates/UnitVerticalCyclicDifference.lean`, `Geometry/NativeCoordinateEstimates.lean`, `Geometry/NativeCoordinateSplitFreezing.lean`, `Geometry/SquareQuotientHeightTransport.lean`, `Linear/FixedAdaptedSymbolFactorizationBasis.lean`, `Linear/FullFastHorizontalSpanning.lean`, `Linear/NativeCoefficientKernel.lean`, `Linear/NativeRankQuotientOrbit.lean`, `Linear/NativeRankRelationExistence.lean`, `Linear/RankIntervalFactorization.lean`, `Linear/RankUnadaptedFactorization.lean`, `Linear/RefiltrationLayerBasis.lean`, `Nilpotent/FreeDegreeRankNilmanifold.lean`, `Nilpotent/NativeRankZeroNiltest.lean`, `Nilpotent/RankAdaptedNiltest.lean`, `Nilpotent/RankInvariantNiltestBudget.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B161
import Definitions.Def_OAIE3v2B162
import Definitions.Def_OAIE3v2B163
import Definitions.Def_OAIE3v2B164
import Definitions.Def_OAIE3v2B165
import Definitions.Def_OAIE3v2B166
import Definitions.Def_OAIE3v2B170

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SourceUnitCover
namespace OAI

section

namespace Erdos3

open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff

namespace NativeMultidegreeNilcharacter

variable {σ : Type*} [Fintype σ] {bound : σ → ℕ} {p q : ℝ}
  (W : NativeMultidegreeNilcharacter bound p)

theorem norm_eval (i : Fin W.outputDim) (x : σ → ℤ) : ‖W.eval i x‖ ≤ 1 := W.vertical.norm i _

end NativeMultidegreeNilcharacter

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeOptionFixedSourceQuotientMarkStrong
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module
open scoped TensorProduct NNReal

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}

namespace AdaptedModelData

variable {D : RationalFilteredNilmanifold L s d}

variable [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]

theorem original_dist_le (F : D.AdaptedModelData) (H : ℕ)
    (hH : ∀ i j, RationalHeightLE (D.basis.repr (F.basis i) j) H) (x y : D.Space) :
    @dist D.Space D.metricSpace.toDist x y ≤
      coordinateLipschitzBound d (finrank ℚ L) H * @dist F.model.Space F.model.metricSpace.toDist x y := by
  have hreal (j i) : |(D.basis.baseChange ℝ).repr ((F.basis.baseChange ℝ) i) j| ≤ (H : ℝ≥0) := by
    rw [Basis.baseChange_apply, Basis.baseChange_repr_tmul]
    simpa only [Rat.smul_def, mul_one, NNReal.coe_natCast] using (hH i j).abs_real_le
  have h := NilpotentLieBCHGroup.basisQuotientDist_change_le
    (F.basis.baseChange ℝ) (D.basis.baseChange ℝ) D.realLattice
    D.realLattice_closed_discrete.1 H hreal x y
  simp only [Fintype.card_fin] at h
  convert h using 1 <;> rfl

end AdaptedModelData

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeOrbitFreezing
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct

theorem polynomialRationalGrid_uniform_cosets {σ L : Type*} [Fintype σ]
    [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
    (D : RationalFilteredNilmanifold L s d) (w : σ → ℕ) (hw : ∀ i, 0 < w i)
    (q : ℕ) (hq : 0 < q)
    (g : (D.filtration.realification.adaptedPolynomialFiltration w).Group)
    (hg : D.filtration.PolynomialRationalGrid D.basis w q g) (x y : σ → ℤ)
    (hxy : ∀ j, (uniformPolynomialBCHPeriod (σ := σ) D.basis s s D.grid q : ℤ) ∣ x j - y j) :
    let f := fun z : σ → ℤ => D.filtration.adaptedPolynomialRealValueHom w (fun j => (z j : ℝ)) g
    ((QuotientGroup.mk (f x) : D.Space) = QuotientGroup.mk (f y)) ∧
    ((QuotientGroup.mk (f x)⁻¹ : D.Space) = QuotientGroup.mk (f y)⁻¹) := by
  obtain ⟨P, hdegree, hden, hval⟩ :=
    D.filtration.polynomialRationalGrid_exists_coordinates D.basis w hw q hq g hg
  dsimp only
  rw [← hval (fun j => (x j : ℝ)), ← hval (fun j => (y j : ℝ))]
  exact realPolynomialBCHMap_uniform_cosets D.basis D.filtration.lowerCentralSeries_eq_bot
    D.lattice s D.grid q P hdegree hden D.inner_grid x y hxy

theorem exists_native_rational_period (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
      {d : ℕ} (D : RationalFilteredNilmanifold L s d) (w : σ → ℕ),
      (∀ i, 0 < w i) → ∀ (p : ℝ), 0 ≤ p → D.GeometryComplexityLE p →
      (Fintype.card σ : ℝ) ≤ p → ∀ (q : ℕ), 0 < q → (q : ℝ) ≤ Real.exp p →
      ∃ M : ℕ, 0 < M ∧ (M : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∀ g : (D.filtration.realification.adaptedPolynomialFiltration w).Group,
          D.filtration.PolynomialRationalGrid D.basis w q g →
          let f := fun z : σ → ℤ => D.filtration.adaptedPolynomialRealValueHom w (fun j => (z j : ℝ)) g
          ∀ x y : σ → ℤ, (∀ j, (M : ℤ) ∣ x j - y j) →
            ((QuotientGroup.mk (f x) : D.Space) = QuotientGroup.mk (f y)) ∧
            ((QuotientGroup.mk (f x)⁻¹ : D.Space) = QuotientGroup.mk (f y)⁻¹) := by
  obtain ⟨a, _, hperiod⟩ := exists_uniformPolynomialBCHPeriod_exp_bound s s
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((Polynomial.X + 1 + Polynomial.C a) ^ a)
  refine ⟨C, hC, ?_⟩
  intro σ L _ _ _ d D w hw p hp hD hσ q hq hqp
  let M := uniformPolynomialBCHPeriod (σ := σ) D.basis s s D.grid q
  have hpp : p ≤ p + 1 := le_add_of_nonneg_right zero_le_one
  have hb := hperiod (σ := σ) D.basis D.grid ⌈Real.exp p⌉₊ q (p + 1)
    (by linarith) (by simpa only [Fintype.card_fin] using hD.1.trans hpp) (hσ.trans hpp)
    (ceil_exp_le_exp_add_one hp) (hD.2.1.trans (Real.exp_le_exp.mpr hpp))
    (hqp.trans (Real.exp_le_exp.mpr hpp))
    (fun i j k => rationalHeightLE_ceil_exp (hD.2.2.1 i j k))
  have hMb : (M : ℝ) ≤ Real.exp ((p + C) ^ C) := by
    apply hb.trans (Real.exp_le_exp.mpr _)
    simpa [Polynomial.eval₂_pow] using hbudget p hp
  exact ⟨M, uniformPolynomialBCHPeriod_pos D.basis s s D.grid q D.grid_pos hq, hMb,
    fun g hg x y hxy => D.polynomialRationalGrid_uniform_cosets w hw q hq g hg x y hxy⟩

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3

open VectorPolynomial
open scoped TensorProduct

namespace RationalFilteredNilmanifold

theorem exists_native_orbit_rational_period (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
      {d : ℕ} (D : RationalFilteredNilmanifold L s d) (w : σ → ℕ),
      (∀ i, 0 < w i) → ∀ (p : ℝ), 0 ≤ p → D.GeometryComplexityLE p →
      (Fintype.card σ : ℝ) ≤ p → ∀ (q : ℕ), 0 < q → (q : ℝ) ≤ Real.exp p →
      ∃ M : ℕ, 0 < M ∧ (M : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∀ g : D.filtration.realification.PolynomialOrbit w,
          CoefficientGrid (D.basis.baseChange ℝ) q g.log →
          ∀ x y : σ → ℤ, (∀ j, (M : ℤ) ∣ x j - y j) →
            ((QuotientGroup.mk (D.filtration.realification.polynomialOrbitEval w x g) : D.Space) =
              QuotientGroup.mk (D.filtration.realification.polynomialOrbitEval w y g)) ∧
            ((QuotientGroup.mk (D.filtration.realification.polynomialOrbitEval w x g)⁻¹ : D.Space) =
              QuotientGroup.mk (D.filtration.realification.polynomialOrbitEval w y g)⁻¹) := by
  obtain ⟨C, hC, hperiod⟩ := exists_native_rational_period s
  refine ⟨C, hC, ?_⟩
  intro σ L _ _ _ d D w hw p hp hD hσ q hq hqp
  obtain ⟨M, hM, hMp, hsolve⟩ := hperiod D w hw p hp hD hσ q hq hqp
  refine ⟨M, hM, hMp, ?_⟩
  intro g hg x y hxy
  have hgrid := (D.filtration.polynomialRationalGrid_iff_formal D.basis w q
    (D.filtration.realification.polynomialOrbitCoordinates w g)).mpr hg
  have h := hsolve (D.filtration.realification.polynomialOrbitCoordinates w g) hgrid x y hxy
  simpa only [D.filtration.polynomialOrbitCoordinates_realValue] using h

end RationalFilteredNilmanifold
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeSharedFrozenCorrelations
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup

theorem exists_uniform_conjugated_source_cover (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L M : Type*} [LieRing L] [LieAlgebra ℚ L]
      [LieRing M] [LieAlgebra ℚ M] {d e : ℕ}
      (D : RationalFilteredNilmanifold L s d) (E : RationalFilteredNilmanifold M s e)
      (φ : L →ₗ⁅ℚ⁆ M) (p : ℝ), 0 ≤ p → D.GeometryComplexityLE p → E.GeometryComplexityLE p →
      (∀ i j, rationalLogHeight (E.basis.repr (φ (D.basis j)) i) ≤ p) →
      ∀ q : ℕ, 0 < q → (q : ℝ) ≤ Real.exp p →
      ∃ Λ : Subgroup D.filtration.Group,
        Λ ≤ D.conjugationPullback E φ q ∧ Λ ≤ D.lattice ∧
        (Λ.subgroupOf D.lattice).Characteristic ∧ (Λ.subgroupOf D.lattice).Normal ∧
        (Λ.subgroupOf D.lattice).FiniteIndex ∧ (Λ.relIndex D.lattice : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∃ (N : ℕ) (hN : 0 < N)
          (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates D.basis Λ)
          (hout : bchSubgroupCoordinates D.basis Λ ⊆ denominatorGrid N),
          (D.withLattice Λ N hN hin hout).GeometryComplexityLE ((p + C) ^ C) := by
  obtain ⟨a, _, hconj⟩ := exists_uniform_conjugated_inner_grid s
  let X : Polynomial ℕ := Polynomial.X
  let U := X + 1 + (X + 1 + Polynomial.C a) ^ a + (X + 2) ^ 3
  let P := U + 2 * U ^ 2 + (U + 2) ^ 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro L M _ _ _ _ d e D E φ p hp hD hE hφ q hq hqp
  classical
  let t := p + 1
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hpt : p ≤ t := le_add_of_nonneg_right zero_le_one
  let H := ⌈Real.exp p⌉₊
  have hH : (H : ℝ) ≤ Real.exp t := ceil_exp_le_exp_add_one hp
  obtain ⟨B, hB, hBb, hBgrid⟩ := hconj E.basis E.filtration.lowerCentralSeries_eq_bot
    E.lattice E.grid q H t E.grid_pos hq E.inner_grid ht
    (by simpa only [Fintype.card_fin] using hE.1.trans hpt) hH
    (fun i j k => rationalHeightLE_ceil_exp (hE.2.2.1 i j k))
    (hE.2.1.trans (Real.exp_le_exp.mpr hpt)) (hqp.trans (Real.exp_le_exp.mpr hpt))
  let A := LinearMap.toMatrix D.basis E.basis φ.toLinearMap
  have hAb : (matrixDenominator A : ℝ) ≤ Real.exp ((p + 2) ^ 3) := by
    apply matrixDenominator_le_exp_power A hp 1
      (by simpa only [Fintype.card_fin] using hE.1)
      (by simpa only [Fintype.card_fin] using hD.1)
    intro i j
    have h := ((rationalLogHeight_le_iff _ p).mp (hφ i j)).2
    dsimp only [A]
    rw [LinearMap.toMatrix_apply]
    exact h.trans (Real.exp_le_exp.mpr (by simp only [pow_one]; linarith))
  let N₀ := B * matrixDenominator A
  have hN₀ : 0 < N₀ := Nat.mul_pos hB (matrixDenominator_pos A)
  have hgrid : scaledIntegerGrid N₀ ⊆ bchSubgroupCoordinates D.basis (D.conjugationPullback E φ q) := by
    intro x hx
    change (⟨D.basis.equivFun.symm x⟩ : D.filtration.Group) ∈ D.conjugationPullback E φ q
    apply Subgroup.mem_iInf.mpr
    intro z
    change x ∈ bchSubgroupCoordinates D.basis
      ((E.lattice.map (MulAut.conj z.val).toMonoidHom).comap
        (NilpotentLieBCHGroup.map (hnil := D.filtration.lowerCentralSeries_eq_bot)
          (hM := E.filtration.lowerCentralSeries_eq_bot) φ))
    rw [bchSubgroupCoordinates_comap D.basis E.basis φ]
    exact hBgrid z.val z.property (matrix_mulVec_fine_grid A B hx)
  let u := t + (t + a) ^ a + (p + 2) ^ 3
  have htu : t ≤ u := by
    exact (le_add_of_nonneg_right (pow_nonneg (add_nonneg ht (Nat.cast_nonneg a)) _)).trans
      (le_add_of_nonneg_right (pow_nonneg (by linarith) _))
  have hu : 0 ≤ u := ht.trans htu
  have hpu : p ≤ u := hpt.trans htu
  have hN₀b : (N₀ : ℝ) ≤ Real.exp u := by
    calc
      _ = (B : ℝ) * matrixDenominator A := Nat.cast_mul _ _
      _ ≤ Real.exp ((t + a) ^ a) * Real.exp ((p + 2) ^ 3) :=
        mul_le_mul hBb hAb (Nat.cast_nonneg _) (Real.exp_pos _).le
      _ = Real.exp ((t + a) ^ a + (p + 2) ^ 3) := (Real.exp_add _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by dsimp only [u]; linarith)
  obtain ⟨Λ, htarget, hΛ, hchar, hnormal, hfinite, hindex, N, hN, hNb, hin, hout⟩ :=
    D.filtration.exists_normal_cover_exp_quadratic D.basis D.lattice (D.conjugationPullback E φ q)
      D.grid N₀ D.grid_pos hN₀ D.inner_grid D.outer_grid hgrid hu
      (by simpa only [Fintype.card_fin] using hD.1.trans hpu)
      (hD.2.1.trans (Real.exp_le_exp.mpr hpu)) hN₀b
  have hsum : u + 2 * u ^ 2 + (u + 2) ^ 2 ≤ (p + C) ^ C := by
    simpa [P, U, X, u, t, Polynomial.eval₂_pow] using hbudget p hp
  have huC : u ≤ (p + C) ^ C :=
    ((le_add_of_nonneg_right (by positivity : 0 ≤ 2 * u ^ 2)).trans
      (le_add_of_nonneg_right (sq_nonneg (u + 2)))).trans hsum
  have hiC : 2 * u ^ 2 ≤ (p + C) ^ C :=
    ((le_add_of_nonneg_left hu).trans (le_add_of_nonneg_right (sq_nonneg (u + 2)))).trans hsum
  have hgC : (u + 2) ^ 2 ≤ (p + C) ^ C :=
    (le_add_of_nonneg_left (add_nonneg hu (by positivity))).trans hsum
  exact ⟨Λ, htarget, hΛ, hchar, hnormal, hfinite,
    hindex.trans (Real.exp_le_exp.mpr hiC), N, hN, hin, hout,
    D.withLattice_geometry Λ N hN hin hout hD (hpu.trans huC) (hNb.trans (Real.exp_le_exp.mpr hgC))⟩

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct NNReal

theorem exists_uniform_frozen_coset_map (s k : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L M : Type*} [LieRing L] [LieAlgebra ℚ L]
      [LieRing M] [LieAlgebra ℚ M]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)]
      {d e : ℕ} (D : RationalFilteredNilmanifold L s d) (E : RationalFilteredNilmanifold M s e)
      (φ : L →ₗ⁅ℚ⁆ M) (p : ℝ), 0 ≤ p → D.GeometryComplexityLE p → E.GeometryComplexityLE p →
      (∀ i j, rationalLogHeight (E.basis.repr (φ (D.basis j)) i) ≤ p) →
      ∀ q : ℕ, 0 < q → (q : ℝ) ≤ Real.exp p →
      ∃ Λ : Subgroup D.filtration.Group, Λ ≤ D.lattice ∧
        (Λ.subgroupOf D.lattice).Characteristic ∧ (Λ.subgroupOf D.lattice).Normal ∧
        (Λ.subgroupOf D.lattice).FiniteIndex ∧ (Λ.relIndex D.lattice : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∃ (N : ℕ) (hN : 0 < N)
          (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates D.basis Λ)
          (hout : bchSubgroupCoordinates D.basis Λ ⊆ denominatorGrid N),
          let Q := D.withLattice Λ N hN hin hout
          Q.GeometryComplexityLE ((p + C) ^ C) ∧
          ∀ a r : E.RealGroup,
            (∀ i, |(E.basis.baseChange ℝ).repr a.coord i| ≤ Real.exp ((p + 2) ^ k)) →
            (E.basis.baseChange ℝ).equivFun r.coord ∈ realDenominatorGrid q →
            ∃ (f : Q.Space → E.Space) (K : ℝ≥0),
              (K : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
              (letI := Q.metricSpace; letI := E.metricSpace; LipschitzWith K f) ∧
              ∀ x : Q.RealGroup, f (QuotientGroup.mk x) = QuotientGroup.mk
                (a * realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
                  (hM := E.filtration.lowerCentralSeries_eq_bot) φ x * r) := by
  obtain ⟨c₀, _, hcover⟩ := exists_uniform_conjugated_source_cover s
  obtain ⟨c₁, _, hleft⟩ := exists_uniform_left_lipschitz_exp_bound s k
  let X : Polynomial ℕ := Polynomial.X
  let P := (X + Polynomial.C c₀) ^ c₀ + X +
    (X + 1 + Polynomial.C c₁) ^ c₁ + (X + 1 + 2) ^ 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro L M _ _ _ _ _ _ _ _ _ _ _ _ d e D E φ p hp hD hE hφ q hq hqp
  obtain ⟨Λ, htarget, hΛ, hchar, hnormal, hfinite, hindex, N, hN, hin, hout, hQ⟩ :=
    hcover D E φ p hp hD hE hφ q hq hqp
  let Q := D.withLattice Λ N hN hin hout
  let t := p + 1
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hpt : p ≤ t := le_add_of_nonneg_right zero_le_one
  have hsum : (p + c₀) ^ c₀ + p + (t + c₁) ^ c₁ + (t + 2) ^ 2 ≤ (p + C) ^ C := by
    simpa [P, X, t, Polynomial.eval₂_pow] using hbudget p hp
  have hcovC : (p + c₀) ^ c₀ ≤ (p + C) ^ C := by
    exact (((le_add_of_nonneg_right hp).trans
      (le_add_of_nonneg_right (pow_nonneg (add_nonneg ht (Nat.cast_nonneg c₁)) _))).trans
      (le_add_of_nonneg_right (sq_nonneg (t + 2)))).trans hsum
  have hcostC : p + (t + c₁) ^ c₁ + (t + 2) ^ 2 ≤ (p + C) ^ C := by
    have hc : 0 ≤ (p + c₀) ^ c₀ := pow_nonneg (add_nonneg hp (Nat.cast_nonneg c₀)) _
    linarith
  let H := ⌈Real.exp p⌉₊
  have hH : (H : ℝ) ≤ Real.exp t := ceil_exp_le_exp_add_one hp
  have hd : (Fintype.card (Fin d) : ℝ) ≤ t := by simpa only [Fintype.card_fin] using hD.1.trans hpt
  have he : (Fintype.card (Fin e) : ℝ) ≤ t := by simpa only [Fintype.card_fin] using hE.1.trans hpt
  let := rightMetricSpace (hnil := D.filtration.realification.lowerCentralSeries_eq_bot) (D.basis.baseChange ℝ)
  let := rightMetricSpace (hnil := E.filtration.realification.lowerCentralSeries_eq_bot) (E.basis.baseChange ℝ)
  obtain ⟨A, _, hA, hALip⟩ := hleft (E.basis.baseChange ℝ) (lieStructureConstants E.basis) H t
    E.filtration.realification.lowerCentralSeries_eq_bot
    (fun i j k => (realLieBasis_structure E.basis i j k).symm) ht he hH
    (fun i j k => rationalHeightLE_ceil_exp (hE.2.2.1 i j k))
  obtain ⟨B, _, hB, hBLip⟩ := exists_realificationMap_lipschitz_exp_bound
    (hnil := D.filtration.lowerCentralSeries_eq_bot) (hM := E.filtration.lowerCentralSeries_eq_bot)
    D.basis E.basis φ H ht hd he hH (fun i j => rationalHeightLE_ceil_exp (hφ i j))
  refine ⟨Λ, hΛ, hchar, hnormal, hfinite, hindex.trans (Real.exp_le_exp.mpr hcovC),
    N, hN, hin, hout, hQ.mono Q hcovC, ?_⟩
  intro a r ha hr
  have hconj := D.real_conjugationPullback_property E φ q hq Λ htarget r hr
  have ha' : LipschitzWith A (fun x => a * x) := hALip a (fun i =>
    (ha i).trans (Real.exp_le_exp.mpr (pow_le_pow_left₀ (by linarith) (by dsimp [t]; linarith) _)))
  let f := frozenCosetMap Q.realLattice E.realLattice
    (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
      (hM := E.filtration.lowerCentralSeries_eq_bot) φ) a r hconj
  have hf : letI := Q.metricSpace; letI := E.metricSpace; LipschitzWith (A * B) f :=
    Q.lipschitz_native_frozenCosetMap E φ a r hconj hBLip ha'
  refine ⟨f, A * B, ?_, hf, fun _ => rfl⟩
  calc
    _ = (A : ℝ) * B := by simp only [NNReal.coe_mul]
    _ ≤ Real.exp ((t + c₁) ^ c₁) * Real.exp ((t + 2) ^ 2) :=
      mul_le_mul hA hB B.coe_nonneg (Real.exp_pos _).le
    _ = Real.exp ((t + c₁) ^ c₁ + (t + 2) ^ 2) := (Real.exp_add _ _).symm
    _ ≤ _ := Real.exp_le_exp.mpr (by linarith)

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal

theorem exists_uniform_unit_frozen_cover (s k : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L I : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype I]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {d r : ℕ} (D : RationalFilteredNilmanifold L s d) (R : D.DegreeRankStructure r)
      (p : ℝ), 0 ≤ p → R.ComplexityLE p →
      ∀ q : ℕ, 0 < q → (q : ℝ) ≤ Real.exp p →
      ∃ Λ : Subgroup D.filtration.Group, Λ ≤ D.lattice ∧
        (Λ.subgroupOf D.lattice).Characteristic ∧ (Λ.subgroupOf D.lattice).Normal ∧
        (Λ.subgroupOf D.lattice).FiniteIndex ∧ (Λ.relIndex D.lattice : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∃ (N : ℕ) (hN : 0 < N)
          (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates D.basis Λ)
          (hout : bchSubgroupCoordinates D.basis Λ ⊆ denominatorGrid N),
          (R.withLattice Λ N hN hin hout).ComplexityLE ((p + C) ^ C) ∧
          ∀ (V : D.UnitVerticalObservable (R.realSubgroup s r) I p) (a u : D.RealGroup),
            (∀ i, |(D.basis.baseChange ℝ).repr a.coord i| ≤ Real.exp ((p + 2) ^ k)) →
            (D.basis.baseChange ℝ).equivFun u.coord ∈ realDenominatorGrid q →
            ∃ U : (D.withLattice Λ N hN hin hout).UnitVerticalObservable
                ((R.withLattice Λ N hN hin hout).realSubgroup s r) I ((p + C) ^ C),
              U.frequency = V.frequency ∧ ∀ i x,
                U.observable i (QuotientGroup.mk x) = V.observable i (QuotientGroup.mk (a * x * u)) := by
  obtain ⟨b, _, hcover⟩ := exists_uniform_frozen_coset_map s k
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (Polynomial.X + (Polynomial.X + Polynomial.C b) ^ b)
  refine ⟨C, hC, ?_⟩
  intro L I _ _ _ _ _ _ _ d r D R p hp hR q hq hqp
  classical
  have hcost : p + (p + b) ^ b ≤ (p + C) ^ C := by
    simpa [Polynomial.eval₂_pow] using hbudget p hp
  have hbp : 0 ≤ (p + b) ^ b := by positivity
  have hpC : p ≤ (p + C) ^ C := by linarith
  have hbC : (p + b) ^ b ≤ (p + C) ^ C := by linarith
  have hidheight (i j : Fin d) : rationalLogHeight (D.basis.repr ((LieHom.id : L →ₗ⁅ℚ⁆ L) (D.basis j)) i) ≤ p := by
    change rationalLogHeight (D.basis.repr (D.basis j) i) ≤ p
    by_cases hji : j = i
    · subst i
      simpa [rationalLogHeight] using hp
    · simpa [Basis.repr_self, Finsupp.single_apply, hji, rationalLogHeight] using hp
  obtain ⟨Λ, hΛ, hchar, hnormal, hfinite, hindex, N, hN, hin, hout, hQ, hmaps⟩ :=
    hcover D D (LieHom.id : L →ₗ⁅ℚ⁆ L) p hp hR.1 hR.1 hidheight q hq hqp
  refine ⟨Λ, hΛ, hchar, hnormal, hfinite, hindex.trans (Real.exp_le_exp.mpr hbC),
    N, hN, hin, hout, R.withLattice_complexity Λ N hN hin hout hR hpC
      (hQ.mono _ hbC), ?_⟩
  intro V a u ha hu
  obtain ⟨f, K, hK, hLip, hf⟩ := hmaps a u ha hu
  have hfid (x : D.RealGroup) : f (QuotientGroup.mk x) = QuotientGroup.mk (a * x * u) := by
    simpa only [D.realificationMap_id_apply] using hf x
  have hVK : ((V.lipBound * K : ℝ≥0) : ℝ) ≤ Real.exp ((p + C) ^ C) := by
    calc
      _ = (V.lipBound : ℝ) * K := NNReal.coe_mul _ _
      _ ≤ Real.exp p * Real.exp ((p + b) ^ b) :=
        mul_le_mul V.lip_bound hK K.coe_nonneg (Real.exp_pos p).le
      _ = Real.exp (p + (p + b) ^ b) := (Real.exp_add _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr hcost
  let U := V.frozenCover R Λ hΛ N hN hin hout a u f hfid K hLip hpC hVK
  refine ⟨U, rfl, ?_⟩
  intro i x
  exact congrArg (V.observable i) (hfid x)

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct NNReal

theorem exists_shared_frozen_unit_observable (s k : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {G L I : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype I]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)] {d r : ℕ}
      (D : RationalFilteredNilmanifold L s d) (R : D.DegreeRankStructure r) {p ε : ℝ},
      0 ≤ p → R.ComplexityLE p → 0 < ε → 1 / ε ≤ Real.exp p →
      ∀ q : ℕ, 0 < q → (q : ℝ) ≤ Real.exp p →
      ∀ (V : D.UnitVerticalObservable (R.realSubgroup s r) I p)
        (H : Finset G) (a u : G → D.RealGroup), H.Nonempty →
      (∀ h ∈ H, ∀ i, |(D.basis.baseChange ℝ).repr (a h).coord i| ≤ Real.exp ((p + 2) ^ k)) →
      (∀ h ∈ H, ∀ i, |(D.basis.baseChange ℝ).repr (u h).coord i| ≤ Real.exp ((p + 2) ^ k)) →
      (∀ h ∈ H, (D.basis.baseChange ℝ).equivFun (u h).coord ∈ realDenominatorGrid q) →
      ∃ Λ : Subgroup D.filtration.Group, Λ ≤ D.lattice ∧
        (Λ.subgroupOf D.lattice).Characteristic ∧ (Λ.subgroupOf D.lattice).Normal ∧
        (Λ.subgroupOf D.lattice).FiniteIndex ∧ (Λ.relIndex D.lattice : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∃ (m : ℕ) (hm : 0 < m)
          (hin : scaledIntegerGrid m ⊆ bchSubgroupCoordinates D.basis Λ)
          (hout : bchSubgroupCoordinates D.basis Λ ⊆ denominatorGrid m),
          (R.withLattice Λ m hm hin hout).ComplexityLE ((p + C) ^ C) ∧
          ∃ H' : Finset G, H' ⊆ H ∧ H'.Nonempty ∧
            Real.exp (-((p + C) ^ C)) * H.card ≤ (H'.card : ℝ) ∧
            ∃ U : (D.withLattice Λ m hm hin hout).UnitVerticalObservable
                ((R.withLattice Λ m hm hin hout).realSubgroup s r) I ((p + C) ^ C),
              U.frequency = V.frequency ∧
              ∀ h ∈ H', ∀ i x, ‖V.observable i (QuotientGroup.mk (a h * x * u h)) -
                U.observable i (QuotientGroup.mk x)‖ ≤ (V.lipBound : ℝ) * ε := by
  obtain ⟨b, _, hselect⟩ := exists_native_frozen_parameter_fiber s k
  obtain ⟨c, _, hcover⟩ := exists_uniform_unit_frozen_cover s k
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((Polynomial.X + Polynomial.C b) ^ b + (Polynomial.X + Polynomial.C c) ^ c)
  refine ⟨C, hC, ?_⟩
  intro G L I _ _ _ _ _ _ _ d r D R p ε hp hR hε hεp q hq hqp V H a u hH ha hu hugrid
  have hsum : (p + b) ^ b + (p + c) ^ c ≤ (p + C) ^ C := by
    simpa [Polynomial.eval₂_pow] using hbudget p hp
  have hb : (p + b) ^ b ≤ (p + C) ^ C := by
    have : 0 ≤ (p + c) ^ c := by positivity
    linarith
  have hc : (p + c) ^ c ≤ (p + C) ^ C := by
    have : 0 ≤ (p + b) ^ b := by positivity
    linarith
  obtain ⟨H', hsub, hnonempty, hdense, a₀, u₀, ha₀, _, hu₀, hclose⟩ :=
    hselect D hp hR.1 hε hεp q hq hqp H a u hH ha hu hugrid
  obtain ⟨Λ, hΛ, hchar, hnormal, hfinite, hindex, m, hm, hin, hout, hRank, hU⟩ :=
    hcover (I := I) D R p hp hR q hq hqp
  obtain ⟨U, hfreq, hval⟩ := hU V a₀ u₀ ha₀ hu₀
  refine ⟨Λ, hΛ, hchar, hnormal, hfinite, hindex.trans (Real.exp_le_exp.mpr hc),
    m, hm, hin, hout, hRank.mono _ hc, H', hsub, hnonempty, ?_, U.mono hc, hfreq, ?_⟩
  · exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hb))
      (Nat.cast_nonneg _)).trans hdense
  · intro h hh i x
    let := rightMetricSpace (hnil := D.filtration.realification.lowerCentralSeries_eq_bot)
      (D.basis.baseChange ℝ)
    obtain ⟨hdist, hu⟩ := hclose h hh
    change ‖V.observable i (QuotientGroup.mk (a h * x * u h)) -
      U.observable i (QuotientGroup.mk x)‖ ≤ _
    rw [hval, hu]
    exact (D.frozen_observable_change_left (V.observable i) (V.lipschitz i) (a h) a₀ x u₀).trans
      (mul_le_mul_of_nonneg_left hdist V.lipBound.coe_nonneg)

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.NativeRankQuotientOrbit
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.DegreeRankStructure

open Module

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d r : ℕ}
  {D : RationalFilteredNilmanifold L s d} (R : D.DegreeRankStructure r)

theorem exists_controlled_rank_adapted_basis {p : ℝ} (hp : 0 ≤ p) (hR : R.ComplexityLE p) :
    ∃ (b : Basis (Fin (finrank ℚ L)) ℚ L) (N : ℕ),
      IsCentralLieBasis b ∧
      (∀ i j, ∃ c ≤ finrank ℚ L, R.filtration.layer i j = basisTail b c) ∧
      (∀ j i, rationalLogHeight (D.basis.repr (b j) i) ≤ p + 1) ∧
      (∀ i j, rationalLogHeight (b.repr (D.basis i) j) ≤ (p + 3) ^ 5) ∧
      (∀ i j k, rationalLogHeight (lieStructureConstants b i j k) ≤ (p + 3) ^ 11) ∧
      0 < N ∧ (N : ℝ) ≤ Real.exp ((p + 3) ^ 9) ∧
      scaledIntegerGrid N ⊆ bchSubgroupCoordinates b D.lattice ∧
      bchSubgroupCoordinates b D.lattice ⊆ denominatorGrid N := by
  let := D.basis.finiteDimensional_of_finite
  let H := ⌈Real.exp p⌉₊
  have hH : 1 ≤ H := one_le_ceil_exp p
  have hHp : (H : ℝ) ≤ Real.exp (p + 1) := ceil_exp_le_exp_add_one hp
  have hp1 : 0 ≤ p + 1 := by linarith
  have hd : (d : ℝ) ≤ p + 1 := hR.1.1.trans (by linarith)
  have hr : (finrank ℚ L : ℝ) ≤ p + 1 := by
    simpa only [finrank_eq_card_basis D.basis, Fintype.card_fin] using hd
  have hgrid : (D.grid : ℝ) ≤ Real.exp (p + 1) :=
    hR.1.2.1.trans (Real.exp_le_exp.mpr (by linarith))
  obtain ⟨b, hcentral, hb, htail⟩ := R.exists_bounded_rank_adapted_basis
    (fun i j a k => rationalHeightLE_ceil_exp (hR.2 i j a k))
  obtain ⟨N, hN, hNb, hin, hout⟩ := exists_basis_change_grid_exp_bound D.basis b D.lattice
    hH D.grid_pos hb D.inner_grid D.outer_grid hp1
    (by simpa only [Fintype.card_fin] using hd)
    (by simpa only [Fintype.card_fin] using hr) hHp hgrid
  have hInv := inverse_basis_entries_height D.basis b hH hb
  have hStructure := basis_change_structure_height D.basis b hH hb
    (fun i j k => rationalHeightLE_ceil_exp (hR.1.2.2.1 i j k))
  have hSolveBudget := rationalSolveHeight_le_budget (finrank ℚ L) H hp1 hr hHp
  have hStructureBudget := rationalLieStructureHeight_inverse_budget d (finrank ℚ L) H hp1 hd hr hHp
  have hshift : p + 1 + 2 = p + 3 := by ring
  refine ⟨b, N, hcentral, htail, ?_, ?_, ?_, hN, ?_, hin, hout⟩
  · exact fun j i => rationalLogHeight_le_of_height (hb j i) hHp
  · intro i j
    apply rationalLogHeight_le_of_height (hInv i j)
    simpa only [Fintype.card_fin, hshift] using hSolveBudget
  · intro i j k
    apply rationalLogHeight_le_of_height (hStructure i j k)
    simpa only [Fintype.card_fin, hshift] using hStructureBudget
  · simpa only [hshift] using hNb

end Erdos3.RationalFilteredNilmanifold.DegreeRankStructure

end

section

namespace Erdos3.RationalFilteredNilmanifold.DegreeRankStructure

open Module

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d r : ℕ}
  {D : RationalFilteredNilmanifold L s d}

namespace AdaptedData

variable {R : D.DegreeRankStructure r} (F : R.AdaptedData)

theorem model_geometry_of_bounds {p : ℝ} (hp : 0 ≤ p) (hd : (finrank ℚ L : ℝ) ≤ p)
    (hgrid : (F.grid : ℝ) ≤ Real.exp p)
    (hc : ∀ i j k, rationalLogHeight (lieStructureConstants F.basis i j k) ≤ p) :
    F.model.GeometryComplexityLE p :=
  D.filtration.ofAdaptedBasis_geometry F.basis F.weight F.layers D.lattice F.grid F.grid_pos
    F.inner F.outer hp hd hgrid hc

theorem rank_complexity {p : ℝ} (hp : 0 ≤ p) (hF : F.model.GeometryComplexityLE p) :
    F.rank.ComplexityLE p := by
  refine ⟨hF, ?_⟩
  intro i j a k
  apply rationalLogHeight_le_of_height
    (basisOfTail_height F.basis _ (Classical.choose (F.rank_layers i.val j.val))
      (Classical.choose_spec (F.rank_layers i.val j.val)).2 a k)
  simpa only [Nat.cast_one] using Real.one_le_exp hp

end AdaptedData

theorem exists_rank_adapted_data (R : D.DegreeRankStructure r) {p : ℝ}
    (hp : 0 ≤ p) (hR : R.ComplexityLE p) :
    ∃ F : R.AdaptedData, F.rank.ComplexityLE ((p + 3) ^ 11) ∧
      (∀ i j, rationalLogHeight (D.basis.repr (F.basis i) j) ≤ p + 1) ∧
      ∀ j i, rationalLogHeight (F.basis.repr (D.basis j) i) ≤ (p + 3) ^ 5 := by
  obtain ⟨b, N, hcentral, htail, hb, hinv, hc, hN, hNb, hin, hout⟩ :=
    R.exists_controlled_rank_adapted_basis hp hR
  have hOrd : ∀ i, ∃ c, D.filtration.layer i = basisTail b c := by
    intro i
    obtain ⟨c, _, h⟩ := htail i 0
    refine ⟨c, ?_⟩
    rw [← R.associated]
    exact h
  obtain ⟨w, hw⟩ := D.filtration.exists_weights_of_tails b hOrd
  let F : R.AdaptedData := {
    basis := b
    weight := w
    layers := hw
    grid := N
    grid_pos := hN
    inner := hin
    outer := hout
    central := hcentral
    rank_layers := htail
  }
  have hp1 : 1 ≤ p + 3 := by linarith
  have hpow : p ≤ (p + 3) ^ 11 := by
    calc
      p ≤ p + 3 := by linarith
      _ = (p + 3) ^ 1 := (pow_one _).symm
      _ ≤ (p + 3) ^ 11 := pow_le_pow_right₀ hp1 (by decide)
  have hdim : (finrank ℚ L : ℝ) ≤ (p + 3) ^ 11 := by
    simpa only [finrank_eq_card_basis D.basis, Fintype.card_fin] using hR.1.1.trans hpow
  have hgeom : F.model.GeometryComplexityLE ((p + 3) ^ 11) :=
    F.model_geometry_of_bounds (by positivity) hdim
      (hNb.trans (Real.exp_le_exp.mpr (pow_le_pow_right₀ hp1 (by decide : 9 ≤ 11)))) hc
  exact ⟨F, F.rank_complexity (by positivity) hgeom, hb, hinv⟩

end Erdos3.RationalFilteredNilmanifold.DegreeRankStructure

end

section

namespace Erdos3

namespace RationalFilteredNilmanifold.DegreeRankStructure.AdaptedData

open Module NilpotentLieFiltration

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r d : ℕ}
  {D : RationalFilteredNilmanifold L s d} {R : D.DegreeRankStructure (r + 1)}
  (F : R.AdaptedData)

theorem exists_lower_rank_quotient {p : ℝ} (hp : 0 ≤ p) (hF : F.model.GeometryComplexityLE p) :
    let I := R.filtration.layerIdeal s (r + 1)
    let hI : D.filtration.layer (s + 1) ≤ I.toSubmodule := by rw [D.filtration.terminal]; exact bot_le
    ∃ n : ℕ, n ≤ finrank ℚ L ∧
      ∃ Q : RationalFilteredNilmanifold (L ⧸ I) s n,
        ∃ U : Q.DegreeRankStructure r,
          U.filtration = R.filtration.quotientRank r (Nat.le_of_succ_le R.filtration.rank_le_degree) ∧
          Q.filtration = D.filtration.quotientLie I hI ∧
          Q.lattice = D.lattice.map (D.filtration.quotientStepHom I hI) ∧
          U.ComplexityLE p ∧
          (∀ i j, rationalLogHeight (Q.basis.repr (lieQuotientMap I (F.basis i)) j) ≤ 0) ∧
          ∀ j, ∃ k, ∀ x : L, Q.basis.repr (lieQuotientMap I x) j = F.basis.repr x k := by
  intro I hI
  classical
  let S : Set (Fin (finrank ℚ L)) := {i | F.basis i ∈ I}
  have hspan : I.toSubmodule = Submodule.span ℚ (F.basis '' S) := by
    obtain ⟨c, _, hc⟩ := F.rank_layers s (r + 1)
    exact tail_span_basis_members F.basis _ c hc
  let Q := D.filtration.coordinateQuotientModel F.basis F.weight F.layers I hI S hspan
    D.lattice F.grid F.grid_pos F.inner F.outer
  let G := R.filtration.quotientRank r (Nat.le_of_succ_le R.filtration.rank_le_degree)
  have hG : G.associatedDegree = Q.filtration := by
    apply NilpotentLieFiltration.eq_of_layer_eq
    funext j
    change (R.filtration.layer j 0).map (lieQuotientMap I).toLinearMap =
      (D.filtration.layer j).map (lieQuotientMap I).toLinearMap
    exact congrArg (fun P : Submodule ℚ L => P.map (lieQuotientMap I).toLinearMap)
      (congrArg (fun H : NilpotentLieFiltration L s => H.layer j) R.associated)
  have hbase (i j : Fin (s + 1)) :
      ∃ b : Basis (Fin (finrank ℚ (G.layer i.val j.val))) ℚ (G.layer i.val j.val),
        ∀ a k, rationalLogHeight (Q.basis.repr (b a : L ⧸ I) k) ≤ 0 := by
    obtain ⟨c, _, hc⟩ := F.rank_layers i.val j.val
    exact exists_coordinate_quotient_layer_basis F.basis I S hspan (R.filtration.layer i.val j.val)
      {k | c ≤ k.val} (hc.trans (basisTail_eq_span F.basis c))
  choose b hb using hbase
  let U : Q.DegreeRankStructure r := ⟨G, hG, b⟩
  have hQ : Q.GeometryComplexityLE p :=
    D.filtration.coordinateQuotientModel_geometry F.basis F.weight F.layers I hI S hspan
      D.lattice F.grid F.grid_pos F.inner F.outer hp
      (by simpa only [Fintype.card_fin] using hF.1) hF.2.1 hF.2.2.1
  refine ⟨_, ?_, Q, U, rfl, rfl, rfl, ⟨hQ, ?_⟩, ?_, ?_⟩
  · simpa only [Fintype.card_fin] using Fintype.card_subtype_le (fun i : Fin (finrank ℚ L) => i ∉ S)
  · intro i j a k
    exact (hb i j a k).trans hp
  · intro i j
    exact rationalLogHeight_le_of_height
      (quotientFinBasis_projection_height F.basis I S hspan i j) (by norm_num)

  · intro j
    exact ⟨((Fintype.equivFin {i // i ∉ S}).symm j).val,
      fun x => quotientFinBasis_repr_mk F.basis I S hspan x j⟩

end RationalFilteredNilmanifold.DegreeRankStructure.AdaptedData
end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold.DegreeRankStructure

open Module NilpotentLieFiltration

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r d : ℕ}
  {D : RationalFilteredNilmanifold L s d} (R : D.DegreeRankStructure (r + 1))

theorem exists_controlled_lower_rank_quotient {p : ℝ} (hp : 0 ≤ p) (hR : R.ComplexityLE p) :
    let I := R.filtration.layerIdeal s (r + 1)
    ∃ n : ℕ, n ≤ d ∧
      ∃ Q : RationalFilteredNilmanifold (L ⧸ I) s n,
        ∃ U : Q.DegreeRankStructure r,
          U.filtration = R.filtration.quotientRank r (Nat.le_of_succ_le R.filtration.rank_le_degree) ∧
          Q.filtration = D.filtration.quotientLie I R.terminal_le_topRankIdeal ∧
          Q.lattice = D.lattice.map (D.filtration.quotientStepHom I R.terminal_le_topRankIdeal) ∧
          U.ComplexityLE ((p + 3) ^ 11) ∧
          ∀ i j, rationalLogHeight (Q.basis.repr (lieQuotientMap I (D.basis i)) j) ≤ (p + 3) ^ 5 := by
  intro I
  obtain ⟨F, hF, _, hinv⟩ := R.exists_rank_adapted_data hp hR
  obtain ⟨n, hn, Q, U, hU, hQF, hQL, hUc, _, hcoord⟩ :=
    F.exists_lower_rank_quotient (by positivity : 0 ≤ (p + 3) ^ 11) hF.1
  have hdim : finrank ℚ L = d := by
    simpa only [Fintype.card_fin] using finrank_eq_card_basis D.basis
  refine ⟨n, hdim ▸ hn, Q, U, hU, hQF, hQL, hUc, ?_⟩
  intro i j
  obtain ⟨k, hk⟩ := hcoord j
  rw [hk]
  exact hinv i k

end Erdos3.RationalFilteredNilmanifold.DegreeRankStructure

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.GradedUnitEvaluation
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))

local notation "ωW" => (fun a : ReducedSquareBasisIndex s ω => squareBasisWeight ω (Subtype.val a))

theorem reducedSquareGradedDifference_projection (j : ℕ)
    (x : F.squareLieSubalgebra ⧸ F.squareFiltration.layerIdeal (s + 1)) :
    F.reducedSquareGradedDifference e ω hF
        (F.squareFiltration.quotientTop.gradedPieceProjection
          (F.reducedSquareBasis e ω hF) ωW (F.reducedSquareBasis_layers e ω hF) j x) =
      F.gradedPieceProjection e ω hF (j + 1) (F.reducedSquareDifference x) := by
  have he : (F.reducedSquareGradedDifference e ω hF).comp
      (F.squareFiltration.quotientTop.gradedPieceProjection
        (F.reducedSquareBasis e ω hF) ωW (F.reducedSquareBasis_layers e ω hF) j) =
      (F.gradedPieceProjection e ω hF (j + 1)).comp F.reducedSquareDifference := by
    apply (F.reducedSquareBasis e ω hF).ext
    intro a
    simp only [LinearMap.comp_apply, F.squareFiltration.quotientTop.gradedPieceProjection_basis,
      F.reducedSquareDifference_basis]
    simp only [apply_ite, map_zero, F.reducedSquareGradedDifference_basis]
    rcases a with ⟨a, ha⟩
    cases a with
    | inl i => simp only [Sum.elim_inl, map_zero, ite_self]
    | inr i =>
      simp only [Sum.elim_inr, squareBasisWeight, F.gradedPieceProjection_basis]
      have hi : (ω i.val - 1 = j) ↔ ω i.val = j + 1 := by have h := i.property; omega
      simp only [hi]
  exact LinearMap.congr_fun he x

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.FullFastHorizontalSpanning
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module
open scoped TensorProduct

variable {ι κ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))

theorem gradedHorizontalKernel_real_mem (K : Submodule ℚ (L ⧸ F.layer 2))
    (x : ℝ ⊗[ℚ] (L ⧸ F.layer 2)) (hx : x ∈ K.baseChange ℝ) :
    (F.layerOneGradedMap e ω hF).baseChange ℝ x ∈ (F.gradedHorizontalKernel e ω hF K).baseChange ℝ := by
  rw [gradedHorizontalKernel, realification_map]
  exact ⟨x, hx, rfl⟩

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.FixedAdaptedSymbolFactorizationBasis
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module
open scoped Matrix NNReal

theorem exists_controlled_symbol_basis_change (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ControlledSymbolBasisChangeSpec s C := by
  let Q : Polynomial ℕ := (Polynomial.X + Polynomial.C (s + 2)) ^ (s + 2)
  let P : Polynomial ℕ := (Q + 2) ^ 3 + Polynomial.X + (Polynomial.X + 2) ^ 4
  obtain ⟨C, hC, hfinal⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro σ ι κ L _ _ _ _ _ F b ω hF c ν hc H p hH hp hι hκ hσ hHp hb T hT η X hX
  classical
  let w := fun _ : σ => 1
  let q : ℝ := (p + (s + 2 : ℕ)) ^ (s + 2)
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hpq : p ≤ q := by
    apply (show p ≤ p + (s + 2 : ℕ) from le_add_of_nonneg_right (Nat.cast_nonneg _)).trans
    simpa only [pow_one] using pow_le_pow_right₀
      (show (1 : ℝ) ≤ p + (s + 2 : ℕ) by have := Nat.cast_nonneg (α := ℝ) s; push_cast; linarith)
      (show 1 ≤ s + 2 by omega)
  have hcost : 0 ≤ (q + 2) ^ 3 + p := by positivity
  have hheight : 0 ≤ (p + 2) ^ 4 := by positivity
  have hbound : (q + 2) ^ 3 + p + (p + 2) ^ 4 ≤ (p + C) ^ C := by
    simpa [P, Q, q, Polynomial.eval₂_pow] using hfinal p hp
  have hcostC : (q + 2) ^ 3 + p ≤ (p + C) ^ C := by linarith
  have hheightC : (p + 2) ^ 4 ≤ (p + C) ^ C := by linarith
  let : Fintype (SymbolBasisIndex w ω) :=
    symbolBasisIndexFintype w ω s (fun _ => Nat.zero_lt_one) (F.adaptedBasis_weight_le_step b ω hF)
  let : Fintype (SymbolBasisIndex w ν) :=
    symbolBasisIndexFintype w ν s (fun _ => Nat.zero_lt_one) (F.adaptedBasis_weight_le_step c ν hc)
  let Bb := F.polynomialSymbolBasis b ω hF w
  let Bc := F.polynomialSymbolBasis c ν hc w
  let M : Matrix (SymbolBasisIndex w ν) (SymbolBasisIndex w ω) ℚ := fun i j => Bc.repr (Bb j) i
  have hMb : ∀ i j, RationalHeightLE (M i j) H :=
    fun i j => F.polynomialSymbolBasis_change_height b ω hF c ν hc w hH hb j i
  have hDb : (Fintype.card (SymbolBasisIndex w ω) : ℝ) ≤ q :=
    (Nat.cast_le.mpr (symbolBasisIndex_card_le w ω s (fun _ => Nat.zero_lt_one)
      (F.adaptedBasis_weight_le_step b ω hF))).trans
        (by simpa only [q, Nat.cast_add, Nat.cast_ofNat] using
          symbol_dimension_bound_le_power s (Fintype.card ι) (Fintype.card σ) hp hι hσ)
  have hDc : (Fintype.card (SymbolBasisIndex w ν) : ℝ) ≤ q :=
    (Nat.cast_le.mpr (symbolBasisIndex_card_le w ν s (fun _ => Nat.zero_lt_one)
      (F.adaptedBasis_weight_le_step c ν hc))).trans
        (by simpa only [q, Nat.cast_add, Nat.cast_ofNat] using
          symbol_dimension_bound_le_power s (Fintype.card κ) (Fintype.card σ) hp hκ hσ)
  have hHq : (H : ℝ) ≤ Real.exp q := hHp.trans (Real.exp_le_exp.mpr hpq)
  have hδ : (matrixDenominator M : ℝ) ≤ Real.exp ((q + 2) ^ 3) :=
    real_basis_transfer_denominator Bb Bc hq hDb hDc hHq hMb
  have hblock : ∀ i j, i.val.1 ≠ j.val.1 → M i j = 0 := by
    intro i j hij
    change (F.polynomialSymbolBasis c ν hc w).repr (F.polynomialSymbolBasis b ω hF w j) i = 0
    rw [F.polynomialSymbolBasis_change_coordinate, if_neg hij.symm]
  obtain ⟨m, E, R, B, Z, v, hm, hmp, hprod, hE, hB, hv, hZ, hh, hη, hR⟩ := hX
  let n := matrixDenominator M * m
  have hn : 0 < n := Nat.mul_pos (matrixDenominator_pos M) hm
  have hnC : (n : ℝ) ≤ Real.exp ((p + C) ^ C) := by
    dsimp only [n]
    rw [Nat.cast_mul]
    calc
      _ ≤ Real.exp ((q + 2) ^ 3) * Real.exp p := mul_le_mul hδ hmp (Nat.cast_nonneg _) (Real.exp_nonneg _)
      _ = Real.exp ((q + 2) ^ 3 + p) := (Real.exp_add _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr hcostC
  have hgrid : F.SymbolRationalGrid c ν hc w n B :=
    real_basis_coordinates_grid Bb Bc m B.coord hB
  have hslow : F.SymbolSlowBound c ν hc w T (Real.exp ((p + C) ^ C)) E := by
    dsimp only [SymbolSlowBound] at hE
    intro i
    have hcoord := congrFun (real_basis_coordinates_transfer Bb Bc E.coord) i
    change |(Bc.baseChange ℝ).repr E.coord i| ≤ _
    rw [hcoord]
    have hEcoord : ∀ j : SymbolBasisIndex w ω,
        |(Bb.baseChange ℝ).repr E.coord j| ≤ Real.exp p / monomialScale T j.val.1 := by
      simpa only [Bb, w] using hE
    have hweighted := weighted_matrix_mulVec_bound (fun i : SymbolBasisIndex w ν => i.val.1)
      (fun j : SymbolBasisIndex w ω => j.val.1) (fun i j => (M i j : ℝ))
      (fun i j hij => by rw [hblock i j hij, Rat.cast_zero]) (H : ℝ≥0)
      (fun i j => (hMb i j).abs_real_le) (monomialScale T) (monomialScale_pos T hT)
      (Real.exp_nonneg p) (fun j => (Bb.baseChange ℝ).repr E.coord j) hEcoord i
    have hfactor : ((Fintype.card (SymbolBasisIndex w ω) : ℝ) + 1) * ((H : ℝ) + 1) ≤
        Real.exp ((q + 2) ^ 3) := by
      have hHlarge : (H : ℝ) ≤ Real.exp ((q + 2) ^ 1) :=
        hHq.trans (Real.exp_le_exp.mpr (by simp))
      calc
        _ ≤ ((Fintype.card (SymbolBasisIndex w ω) : ℝ) + 1) *
            (Real.exp ((q + 2) ^ 1) + 1) :=
          mul_le_mul_of_nonneg_left (add_le_add hHlarge le_rfl) (by positivity)
        _ ≤ _ := matrix_weighted_factor_le_exp_power _ hq hDb 1 (by decide)
    apply hweighted.trans
    apply div_le_div_of_nonneg_right _ (monomialScale_pos T hT i.val.1).le
    calc
      _ ≤ Real.exp ((q + 2) ^ 3) * Real.exp p := mul_le_mul_of_nonneg_right hfactor (Real.exp_nonneg p)
      _ = Real.exp ((q + 2) ^ 3 + p) := (Real.exp_add _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr hcostC
  have hcard : Fintype.card κ = Fintype.card ι := by
    rw [← finrank_eq_card_basis c, finrank_eq_card_basis b]
  let e := Fintype.equivOfCardEq hcard
  let v' : κ → F.AssociatedGraded := fun i => v (e i)
  have hrange : Set.range v' = Set.range v := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨e i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨e.symm i, congrArg v (e.apply_symm_apply i)⟩
  refine ⟨n, E, R, B, Z, v', hn, hnC, hprod, hslow, hgrid, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hrange]
    exact hv
  · exact (F.associatedGraded_submodule_basis_independent b ω hF c ν hc Z.toSubmodule).mpr hZ
  · intro i j
    have hx : ∀ k, rationalLogHeight ((F.associatedGradedBasis b ω hF).repr (v (e i)) k) ≤ p := hh (e i)
    have hbc : ∀ j k, RationalHeightLE ((F.associatedGradedBasis c ν hc).repr
        (F.associatedGradedBasis b ω hF j) k) H :=
      F.associatedGradedBasis_change_height b ω hF c ν hc hH hb
    have htransfer := rational_basis_coordinates_logHeight (F.associatedGradedBasis b ω hF)
      (F.associatedGradedBasis c ν hc) hp hι hHp hbc (v (e i)) hx j
    exact htransfer.trans hheightC
  · intro x hx htop
    have htop' : basisGradeProjection (F.associatedGradedBasis b ω hF) ω s x = x := by
      rw [← F.associatedGraded_projection_basis_independent b ω hF c ν hc s]
      exact htop
    exact (F.gradedFrequency_top_basis_independent b ω hF c ν hc η x htop').trans (hη x hx htop')
  · rw [F.symbolPointwiseSubalgebra_basis_independent b ω hF c ν hc w]
    simpa only [w] using hR

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.SquareQuotientHeightTransport
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {σ ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (Γ : Subgroup F.squareFiltration.Group) (N : ℕ) (hN : 0 < N)
  (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates (F.squareFinBasis b ω (hF 2)) Γ)
  (hout : bchSubgroupCoordinates (F.squareFinBasis b ω (hF 2)) Γ ⊆ denominatorGrid N)

local notation "Q" => F.squareFiltration.topQuotientModel (F.squareFinBasis b ω (hF 2))
  (squareFinWeight ω) (F.squareFinBasis_layers b ω hF) Γ N hN hin hout
local notation "hQ" => F.squareFiltration.topQuotientModel_basis_layers
  (F.squareFinBasis b ω (hF 2)) (squareFinWeight ω) (F.squareFinBasis_layers b ω hF) Γ N hN hin hout
local notation "bq" => F.reducedSquareBasis b ω hF
local notation "ωq" => (fun i : ReducedSquareBasisIndex s ω => squareBasisWeight ω (Subtype.val i))
local notation "hq" => F.reducedSquareBasis_layers b ω hF

theorem squareTopQuotientModel_graded_iff
    (U : Submodule ℚ F.squareFiltration.quotientTop.AssociatedGraded) :
    BasisGradedSubmodule ((Q).filtration.associatedGradedBasis (Q).basis
        (quotientFinWeight (squareFinWeight ω) {i | s + 1 ≤ squareFinWeight ω i}) hQ)
        (quotientFinWeight (squareFinWeight ω) {i | s + 1 ≤ squareFinWeight ω i}) U ↔
      BasisGradedSubmodule (F.squareFiltration.quotientTop.associatedGradedBasis bq ωq hq) ωq U := by
  exact F.squareFiltration.quotientTop.graded_submodule_iff_of_basis_reindex bq ωq hq
    (reducedSquareFinIndexEquiv s ω) (Q).basis
    (quotientFinWeight (squareFinWeight ω) {i | s + 1 ≤ squareFinWeight ω i}) hQ
    (F.squareTopQuotientModel_basis_reindex b ω hF Γ N hN hin hout) rfl U

theorem squareTopQuotientModel_graded_repr (x : F.squareFiltration.quotientTop.AssociatedGraded)
    (i : ReducedSquareBasisIndex s ω) :
    ((Q).filtration.associatedGradedBasis (Q).basis
      (quotientFinWeight (squareFinWeight ω) {i | s + 1 ≤ squareFinWeight ω i}) hQ).repr x
        (reducedSquareFinIndexEquiv s ω i) =
      (F.squareFiltration.quotientTop.associatedGradedBasis bq ωq hq).repr x i := by
  exact F.squareFiltration.quotientTop.associatedGradedBasis_repr_of_basis_reindex bq ωq hq
    (reducedSquareFinIndexEquiv s ω) (Q).basis
    (quotientFinWeight (squareFinWeight ω) {i | s + 1 ≤ squareFinWeight ω i}) hQ
    (F.squareTopQuotientModel_basis_reindex b ω hF Γ N hN hin hout) rfl x i

theorem squareTopQuotientModel_top_annihilation_iff
    (ξ : (F.squareLieSubalgebra ⧸ F.squareFiltration.layerIdeal (s + 1)) →ₗ[ℚ] ℚ)
    (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded) :
    (∀ x ∈ W, basisGradeProjection ((Q).filtration.associatedGradedBasis (Q).basis
          (quotientFinWeight (squareFinWeight ω) {i | s + 1 ≤ squareFinWeight ω i}) hQ)
          (quotientFinWeight (squareFinWeight ω) {i | s + 1 ≤ squareFinWeight ω i}) s x = x →
      (Q).filtration.gradedFrequency (Q).basis
        (quotientFinWeight (squareFinWeight ω) {i | s + 1 ≤ squareFinWeight ω i}) hQ ξ x = 0) ↔
    (∀ x ∈ W, basisGradeProjection (F.squareFiltration.quotientTop.associatedGradedBasis bq ωq hq)
        ωq s x = x → F.squareFiltration.quotientTop.gradedFrequency bq ωq hq ξ x = 0) := by
  exact F.squareFiltration.quotientTop.graded_top_annihilation_iff_of_basis_reindex bq ωq hq
    (reducedSquareFinIndexEquiv s ω) (Q).basis
    (quotientFinWeight (squareFinWeight ω) {i | s + 1 ≤ squareFinWeight ω i}) hQ
    (F.squareTopQuotientModel_basis_reindex b ω hF Γ N hN hin hout) rfl ξ W

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

theorem squareTopQuotientModel_graded_logHeight
    {ι κ L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L (s + 1)) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (Γ : Subgroup F.squareFiltration.Group) (N : ℕ) (hN : 0 < N)
    (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates (F.squareFinBasis b ω (hF 2)) Γ)
    (hout : bchSubgroupCoordinates (F.squareFinBasis b ω (hF 2)) Γ ⊆ denominatorGrid N)
    (v : κ → F.squareFiltration.quotientTop.AssociatedGraded) {p : ℝ}
    (hheight : BasisFamilyLogHeight
      ((F.squareFiltration.topQuotientModel (F.squareFinBasis b ω (hF 2))
        (squareFinWeight ω) (F.squareFinBasis_layers b ω hF) Γ N hN hin hout).filtration.associatedGradedBasis
        (F.squareFiltration.topQuotientModel (F.squareFinBasis b ω (hF 2))
          (squareFinWeight ω) (F.squareFinBasis_layers b ω hF) Γ N hN hin hout).basis
        (quotientFinWeight (squareFinWeight ω) {i | s + 1 ≤ squareFinWeight ω i})
        (F.squareFiltration.topQuotientModel_basis_layers (F.squareFinBasis b ω (hF 2))
          (squareFinWeight ω) (F.squareFinBasis_layers b ω hF) Γ N hN hin hout)) v p) :
    BasisFamilyLogHeight
      (F.squareFiltration.quotientTop.associatedGradedBasis
        (F.reducedSquareBasis b ω hF) (fun i => squareBasisWeight ω i.val)
        (F.reducedSquareBasis_layers b ω hF)) v p := by
  intro i j
  have heq := F.squareTopQuotientModel_graded_repr b ω hF Γ N hN hin hout (v i) j
  exact (congrArg rationalLogHeight heq).symm.le.trans
    (hheight i (reducedSquareFinIndexEquiv s ω j))

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.BiasedSynchronizedSquareFamily
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieFiltration NilpotentLieBCHGroup VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [Fintype σ] [Fintype ι] [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  (D : RationalFilteredNilmanifold L (s + 1) d) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

omit [Fintype ι] in
theorem SynchronizedNativeSquareData.mono {T : σ → ℝ}
    {g : D.filtration.RealAdaptedPolynomialGroup (fun _ : σ => 1)}
    {S : Finset (σ → ℤ)} {h₀ : σ → ℤ}
    {W : LieSubalgebra ℚ D.filtration.squareFiltration.quotientTop.AssociatedGraded}
    {p q p' q' : ℝ} {l m : ℕ}
    (hdata : D.SynchronizedNativeSquareData b ω hF T g S h₀ W p q l m)
    (hp : p ≤ p') (hq : q ≤ q') (hT : ∀ i, 0 < T i) :
    D.SynchronizedNativeSquareData b ω hF T g S h₀ W p' q' l m := by
  obtain ⟨ε, γ, r, E, P, R, A, B, D₀, hprod, hA, hD, hB, hgood, hrelative⟩ := hdata
  refine ⟨ε, γ, r, E, P, R, A, B, D₀, hprod, ?_, hD, hB, ?_, hrelative⟩
  · exact D.filtration.quotientTop.symbolSlowBound_mono
      (D.filtration.quotientTopBasis b ω hF) (fun i => ω i.val)
      (D.filtration.quotientTopBasis_layers b ω hF) (fun _ => 1) T hT
      (Real.exp_le_exp.mpr hp) A hA
  · intro h hh
    obtain ⟨hγ, hε, hf, hs, hderivative, hfactor, hfast, hleft, hright, hmiddle, hslow, hrat⟩ := hgood h hh
    refine ⟨hγ, (fun i => (hε i).trans (Real.exp_le_exp.mpr hp)), hf, hs, hderivative,
      hfactor, hfast, hleft, hright, hmiddle, ?_, hrat⟩
    exact D.filtration.squareFiltration.quotientTop.symbolSlowBound_mono
      (D.filtration.reducedSquareBasis b ω hF) (fun i => squareBasisWeight ω i.val)
      (D.filtration.reducedSquareBasis_layers b ω hF) (fun _ => 1) T hT
      (Real.exp_le_exp.mpr hq) (E h) hslow

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.BiasedNativeTerminal
namespace OAI

section

namespace Erdos3

open Module NilpotentLieFiltration VectorPolynomial
open scoped BigOperators

def SynchronizedNativeTerminalSpec (s C : ℕ) : Prop :=
  ∀ {σ ι τ L : Type*} [Fintype σ] [DecidableEq σ] [Fintype ι] [Fintype τ]
    [LieRing L] [LieAlgebra ℚ L] {d : ℕ} (D : RationalFilteredNilmanifold L (s + 1) d)
    (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (H l m : ℕ) (p : ℝ) (_hH : 1 ≤ H) (_hl : 0 < l) (_hm : 0 < m) (_hp : 0 ≤ p) (_hs : 1 ≤ s)
    (_hι : (Fintype.card ι : ℝ) ≤ p) (_hσ : (Fintype.card σ : ℝ) ≤ p)
    (_hτ : (Fintype.card τ : ℝ) ≤ p) (_hd : (d : ℝ) ≤ p)
    (_hHp : (H : ℝ) ≤ Real.exp p) (_hlp : (l : ℝ) ≤ Real.exp p) (_hmp : (m : ℝ) ≤ Real.exp p)
    (_hgrid : (D.grid : ℝ) ≤ Real.exp p)
    (_hc : ∀ i j k, RationalHeightLE (b.repr ⁅b i, b j⁆ k) H)
    (_hb : ∀ i j, RationalHeightLE (b.repr (D.basis j) i) H)
    (W : LieSubalgebra ℚ D.filtration.squareFiltration.quotientTop.AssociatedGraded)
    (v : τ → D.filtration.squareFiltration.quotientTop.AssociatedGraded)
    (_hv : Submodule.span ℚ (Set.range v) = W.toSubmodule)
    (_hW : BasisGradedSubmodule
      (D.filtration.squareFiltration.quotientTop.associatedGradedBasis
        (D.filtration.reducedSquareBasis b ω hF) (fun i => squareBasisWeight ω i.val)
        (D.filtration.reducedSquareBasis_layers b ω hF)) (fun i => squareBasisWeight ω i.val) W.toSubmodule)
    (_hh : ∀ i j, RationalHeightLE
      ((D.filtration.squareFiltration.quotientTop.associatedGradedBasis
        (D.filtration.reducedSquareBasis b ω hF) (fun i => squareBasisWeight ω i.val)
        (D.filtration.reducedSquareBasis_layers b ω hF)).repr (v i) j) H)
    (η : D.filtration.AssociatedGraded →ₗ[ℚ] ℚ)
    (_hη : ∀ x ∈ D.filtration.fullFastGradedRelative b ω hF W,
      basisGradeProjection (D.filtration.associatedGradedBasis b ω hF) ω (s + 1) x = x → η x = 0)
    (T : σ → ℝ) (_hT : ∀ i, Real.exp ((p + C) ^ C) ≤ T i)
    (g : D.filtration.RealAdaptedPolynomialGroup (fun _ : σ => 1))
    (S : Finset (σ → ℤ)) (h₀ : σ → ℤ) (_hh₀ : h₀ ∈ S)
    (_hbox : ∀ h ∈ S, ∀ i, |(h i : ℝ)| ≤ T i)
    (_hdense : Real.exp (-p) * ∏ i, T i ≤ (S.card : ℝ))
    (_hdata : D.SynchronizedNativeSquareData b ω hF T g S h₀ W p p l m),
    ∃ A B R : D.filtration.RealAdaptedPolynomialGroup (fun _ : σ => 1),
      A * B * R = g ∧
      D.filtration.RealAdaptedCoefficientBound b ω hF (fun _ => 1) T (Real.exp p) A.coord ∧
      D.filtration.RealAdaptedCoefficientGrid b ω hF (fun _ => 1) l R.coord ∧
      D.filtration.SymbolTerminalFactorization b ω hF W η T
        (D.filtration.realPolynomialSymbolHom b ω hF (fun _ => 1)
          (D.filtration.realAdaptedPolynomialGroupHom (fun _ => 1) B)) ((p + C) ^ C)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeWeightPairRemoval
namespace OAI

section

namespace Erdos3

noncomputable def translatedMixedProduct {s : ℕ} {p : ℝ}
    (V : NativeMultidegreeNilcharacter (fun _ : ReplicatedIndex (mixedCorrelationDegree s) => 1) p)
    (k : Fin 4 → Fin V.outputDim) (h₁ h₂ h₃ h₄ δ n : ℤ) : ℂ :=
  fourPointProduct
    (fun n => V.eval (k 0) (fun j => correlationInput h₁ n j.1))
    (fun n => V.eval (k 1) (fun j => correlationInput h₂ n j.1))
    (fun n => V.eval (k 2) (fun j => correlationInput h₃ n j.1))
    (fun n => V.eval (k 3) (fun j => correlationInput h₄ n j.1)) δ n

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.NativeCoordinateSplitFreezing
namespace OAI

section

namespace Erdos3.NativeCoordinateSplit

open scoped TensorProduct

attribute [local instance] NativeCoordinateSplit.lie NativeCoordinateSplit.algebra
  NativeCoordinateSplit.topology NativeCoordinateSplit.topologicalAdd
  NativeCoordinateSplit.continuousSMul NativeCoordinateSplit.hausdorff

variable {σ : Type} [Fintype σ] [DecidableEq σ] [Nonempty σ] {i : σ} {s d : ℕ}
  {p epsilon : ℝ} {f : (σ → ℤ) → ℂ} (R : NativeCoordinateSplit i s d p epsilon f)

theorem first_eval_eq (j : Fin R.count) (x y : σ → ℤ) (hxy : x i = y i) :
    (R.test false j).eval x = (R.test false j).eval y := by
  unfold RationalFilteredNilmanifold.Niltest.eval
  rw [R.test_orbit false j, (R.multi false).orbitToOrdinary_eval,
    (R.multi false).orbitToOrdinary_eval]
  apply congrArg (R.test false j).observable
  apply congrArg QuotientGroup.mk
  apply (R.multi false).filtration.realification.polynomialOrbitEval_eq_on_active_coordinates
  intro k hk
  have hki : k = i := by
    by_contra hn
    exact hk (by simp [coordinateSplitBound, hn])
  subst k
  exact hxy

end Erdos3.NativeCoordinateSplit

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.NativeRankRelationExistence
namespace OAI

section

namespace Erdos3

open scoped BigOperators

namespace NativeRankInterval

noncomputable def mono {s r N : ℕ} [NeZero N] {b p q p' q' : ℝ}
    {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
    {H : Finset (ZMod N)} {t : ZMod N × ZMod N × ZMod N} {branch : Bool}
    (I : NativeRankInterval W out H t branch p q) (hp : p ≤ p') (hq : q ≤ q') :
    NativeRankInterval W out H t branch p' q' :=
  { I with
    length_ratio := (Real.exp_le_exp.mpr (neg_le_neg hp)).trans I.length_ratio
    expansion := I.expansion.mono hq
    correlation := (Real.exp_le_exp.mpr (neg_le_neg hp)).trans I.correlation }

end NativeRankInterval

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

namespace NativeRankInterval

variable {s r N : ℕ} [NeZero N] {b p q : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {t : ZMod N × ZMod N × ZMod N} {branch : Bool}

theorem select_lower_term (I : NativeRankInterval W out H t branch p q) :
    ∃ i : Fin I.expansion.count, Real.exp (-(p + q)) ≤
      ‖𝔼 n ∈ Finset.Ico (I.start : ℤ) (I.start + I.length),
        fourPointProduct (W.eval out t.2.1) (W.eval out (t.2.1 - t.1))
          (W.eval out t.2.2) (W.eval out (t.2.2 - t.1)) (cyclicBranchOffset t.1 branch) n *
            (I.expansion.test i).eval (fun _ => n)‖ :=
  I.expansion.select_sample_product_correlation
    (Finset.Ico (I.start : ℤ) (I.start + I.length)) (fun n _ => n)
    (fun n => fourPointProduct (W.eval out t.2.1) (W.eval out (t.2.1 - t.1))
      (W.eval out t.2.2) (W.eval out (t.2.2 - t.1)) (cyclicBranchOffset t.1 branch) n)
    I.correlation

end NativeRankInterval

theorem exists_rank_interval_raised_lower_term (s : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {r N : ℕ} [NeZero N] {b p q : ℝ}
      {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
      {H : Finset (ZMod N)} {t : ZMod N × ZMod N × ZMod N} {branch : Bool}
      (I : NativeRankInterval W out H t branch p q),
      ∃ i : Fin I.expansion.count,
        ∃ R : ((I.expansion.model i).raiseStep (Nat.sub_le s 1)).DegreeRankStructure r,
          R.ComplexityLE ((q + C) ^ C) ∧ R.realSubgroup s r = ⊥ ∧
          ((I.expansion.test i).raiseStep (Nat.sub_le s 1)).ComplexityLE (raisedNiltestBudget q) ∧
          Real.exp (-(p + q)) ≤
            ‖𝔼 n ∈ Finset.Ico (I.start : ℤ) (I.start + I.length),
              fourPointProduct (W.eval out t.2.1) (W.eval out (t.2.1 - t.1))
                (W.eval out t.2.2) (W.eval out (t.2.2 - t.1)) (cyclicBranchOffset t.1 branch) n *
                  ((I.expansion.test i).raiseStep (Nat.sub_le s 1)).eval (fun _ => n)‖ := by
  obtain ⟨C, hC, hraise⟩ := RationalFilteredNilmanifold.exists_raised_degree_rank_structure s
  refine ⟨C, hC, ?_⟩
  intro r N _ b p q W out H t branch I
  obtain ⟨i, hi⟩ := I.select_lower_term
  have hq : 0 ≤ q := (Nat.cast_nonneg _).trans (I.expansion.complexity i).1.1
  have hsmall : s - 1 < s := by omega
  obtain ⟨R, hR, hzero⟩ := hraise (I.expansion.model i) hsmall
    W.rank.filtration.rank_le_degree hq (I.expansion.complexity i).1
  refine ⟨i, R, hR, hzero,
    (I.expansion.test i).raiseStep_complexity (Nat.sub_le s 1) hq (I.expansion.complexity i), ?_⟩
  simpa only [RationalFilteredNilmanifold.Niltest.raiseStep_eval] using hi

end Erdos3

end

section

namespace Erdos3.NativeRankInterval

variable {s r N : ℕ} [NeZero N] {b p q : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {t : ZMod N × ZMod N × ZMod N} {branch : Bool}
  (I : NativeRankInterval W out H t branch p q)

theorem length_lower_bound : Real.exp (-p) * N ≤ (I.length : ℝ) := by
  have hN : (0 : ℝ) < N := by exact_mod_cast NeZero.pos N
  exact (le_div_iff₀ hN).mp I.length_ratio

theorem length_exp_lower_bound {A : ℝ} (hN : Real.exp (p + A) ≤ N) :
    Real.exp A ≤ (I.length : ℝ) := by
  calc
    Real.exp A = Real.exp (-p) * Real.exp (p + A) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp (-p) * N := mul_le_mul_of_nonneg_left hN (Real.exp_pos _).le
    _ ≤ I.length := I.length_lower_bound

end Erdos3.NativeRankInterval

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.RankAdaptedNiltest
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.AdaptedModelData

open Module CircleFourier
open scoped TensorProduct NNReal

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d} (F : D.AdaptedModelData) (H : ℕ)
  (hH : ∀ i j, RationalHeightLE (D.basis.repr (F.basis i) j) H) {w : σ → ℕ}

noncomputable def rebaseNiltest (T : D.Niltest w) : F.model.Niltest w where
  orbit := T.orbit
  observable := T.observable
  normBound := T.normBound
  lipBound := T.lipBound * coordinateLipschitzBound d (finrank ℚ L) H
  norm_le := T.norm_le
  lipschitz := by
    let := F.model.metricSpace
    apply LipschitzWith.of_dist_le_mul
    intro x y
    have hT : dist (T.observable x) (T.observable y) ≤
        (T.lipBound : ℝ) * @dist D.Space D.metricSpace.toDist x y := by
      let := D.metricSpace
      exact T.lipschitz.dist_le_mul x y
    calc
      dist (T.observable x) (T.observable y) ≤
          (T.lipBound : ℝ) * @dist D.Space D.metricSpace.toDist x y := hT
      _ ≤ (T.lipBound : ℝ) *
          (coordinateLipschitzBound d (finrank ℚ L) H * dist x y) :=
        mul_le_mul_of_nonneg_left (F.original_dist_le H hH x y) T.lipBound.coe_nonneg
      _ = ↑(T.lipBound * coordinateLipschitzBound d (finrank ℚ L) H) * dist x y := by
        rw [NNReal.coe_mul]
        ring

theorem rebaseNiltest_complexity (T : D.Niltest w) {p : ℝ} (hp : 0 ≤ p)
    (hT : T.ComplexityLE p) (hF : F.model.GeometryComplexityLE p) (hHp : (H : ℝ) ≤ Real.exp p) :
    (F.rebaseNiltest H hH T).ComplexityLE (p + (p + 2) ^ 2) := by
  have hK : (coordinateLipschitzBound d (finrank ℚ L) H : ℝ) ≤ Real.exp ((p + 2) ^ 2) :=
    coordinateLipschitzBound_le_exp d (finrank ℚ L) H hp hT.1.1 hF.1 hHp
  have h1 : 1 ≤ Real.exp ((p + 2) ^ 2) := Real.one_le_exp_iff.mpr (sq_nonneg _)
  refine ⟨hF.mono F.model (le_add_of_nonneg_right (sq_nonneg _)), ?_⟩
  change Real.log (2 + (T.normBound : ℝ) +
    (T.lipBound : ℝ) * coordinateLipschitzBound d (finrank ℚ L) H) ≤ p + (p + 2) ^ 2
  apply (Real.log_le_iff_le_exp (by positivity)).mpr
  calc
    2 + (T.normBound : ℝ) + (T.lipBound : ℝ) * coordinateLipschitzBound d (finrank ℚ L) H ≤
        (2 + (T.normBound : ℝ)) * Real.exp ((p + 2) ^ 2) +
          (T.lipBound : ℝ) * Real.exp ((p + 2) ^ 2) :=
      add_le_add (le_mul_of_one_le_right (by positivity) h1)
        (mul_le_mul_of_nonneg_left hK T.lipBound.coe_nonneg)
    _ = (2 + (T.normBound : ℝ) + (T.lipBound : ℝ)) * Real.exp ((p + 2) ^ 2) := by ring
    _ ≤ Real.exp p * Real.exp ((p + 2) ^ 2) :=
      mul_le_mul_of_nonneg_right (Niltest.observable_budget hT) (Real.exp_pos _).le
    _ = Real.exp (p + (p + 2) ^ 2) := (Real.exp_add _ _).symm

end Erdos3.RationalFilteredNilmanifold.AdaptedModelData

end

section

namespace Erdos3

namespace RationalFilteredNilmanifold.DegreeRankStructure

open Module
open scoped TensorProduct

theorem exists_adapted_niltest {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d r : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {D : RationalFilteredNilmanifold L s d} (R : D.DegreeRankStructure r)
    {w : σ → ℕ} (T : D.Niltest w) {p : ℝ} (hp : 0 ≤ p)
    (hR : R.ComplexityLE p) (hT : T.ComplexityLE p) :
    ∃ F : R.AdaptedData,
      F.rank.ComplexityLE (rankAdaptedNiltestBudget p) ∧
      (∀ i j, rationalLogHeight (D.basis.repr (F.basis i) j) ≤ p + 1) ∧
      (∀ j i, rationalLogHeight (F.basis.repr (D.basis j) i) ≤ (p + 3) ^ 5) ∧
      ∃ S : F.model.Niltest w, S.orbit = T.orbit ∧ S.observable = T.observable ∧
        S.ComplexityLE (rankAdaptedNiltestBudget p) := by
  obtain ⟨F, hF, hb, hinv⟩ := R.exists_rank_adapted_data hp hR
  let H := ⌈Real.exp (p + 1)⌉₊
  have hH (i j) : RationalHeightLE (D.basis.repr (F.basis i) j) H :=
    rationalHeightLE_ceil_exp (hb i j)
  let q := rankAdaptedNiltestBase p
  have hpow : 0 ≤ (p + 3) ^ 11 := by positivity
  have hpq : p ≤ q := by dsimp [q, rankAdaptedNiltestBase]; linarith
  have hfq : (p + 3) ^ 11 ≤ q := by dsimp [q, rankAdaptedNiltestBase]; linarith
  have hq : 0 ≤ q := hp.trans hpq
  have hHq : (H : ℝ) ≤ Real.exp q :=
    (ceil_exp_le_exp_add_one (by linarith : 0 ≤ p + 1)).trans
      (Real.exp_le_exp.mpr (by dsimp [q, rankAdaptedNiltestBase]; linarith))
  have hqb : q ≤ rankAdaptedNiltestBudget p := by
    exact le_add_of_nonneg_right (sq_nonneg _)
  refine ⟨F, hF.mono F.rank (hfq.trans hqb), hb, hinv,
    F.toAdaptedModelData.rebaseNiltest H hH T, rfl, rfl, ?_⟩
  exact F.toAdaptedModelData.rebaseNiltest_complexity H hH T hq
    (hT.mono hpq) (hF.1.mono F.model hfq) hHq

end RationalFilteredNilmanifold.DegreeRankStructure

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RefiltrationLayerBasis
namespace OAI

section

namespace Erdos3

open Module

namespace NilpotentLieFiltration

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (w : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ w i}))

theorem exists_uniform_refiltration_layer_bases
    {κ : Type*} [Fintype κ] (W : LieSubalgebra ℚ F.AssociatedGraded)
    (v : κ → F.AssociatedGraded) (hspan : Submodule.span ℚ (Set.range v) = W.toSubmodule)
    {H : ℕ} (hH : 1 ≤ H)
    (hv : ∀ i k, RationalHeightLE ((F.associatedGradedBasis b w hlayers).repr (v i) k) H)
    {p : ℝ} (hp : 0 ≤ p) (hd : (Fintype.card ι : ℝ) ≤ p)
    (hκ : (Fintype.card κ : ℝ) ≤ p) (hHp : (H : ℝ) ≤ Real.exp p) :
    ∃ B : ℕ, 1 ≤ B ∧ (B : ℝ) ≤ Real.exp ((p + (p + 2) ^ 7 + 2) ^ 9) ∧
      ∀ j, ∃ e : Basis (Fin (finrank ℚ (F.gradedRefiltrationLayer W j))) ℚ (F.gradedRefiltrationLayer W j),
        ∀ i k, RationalHeightLE (b.repr (e i : L) k) B := by
  obtain ⟨A, hA, hAp, d, hdim, f, hf⟩ := exists_submodule_quotient_basis_exp
    (F.associatedGradedBasis b w hlayers) W.toSubmodule v hspan hH hv hp hκ hHp
  let B := (Fintype.card ι + 1) * rationalKernelHeight (Fintype.card ι) A ^ Fintype.card ι
  have hB : 1 ≤ B := by
    exact Nat.mul_le_mul (Nat.le_add_left 1 _) (one_le_pow₀ (rationalKernelHeight_pos _ hA))
  let q := p + (p + 2) ^ 7
  have hpq : p ≤ q := le_add_of_nonneg_right (by positivity)
  have hq : 0 ≤ q := hp.trans hpq
  have hAq : (A : ℝ) ≤ Real.exp q := hAp.trans (Real.exp_le_exp.mpr (by dsimp [q]; linarith))
  have hBp : (B : ℝ) ≤ Real.exp ((q + 2) ^ 9) :=
    stepDrop_basis_height_budget _ _ A hq (hd.trans hpq) (hd.trans hpq) hAq
  refine ⟨B, hB, hBp, ?_⟩
  intro j
  obtain ⟨r, hr, e, he⟩ := F.exists_refiltration_layer_basis_of_quotient b w hlayers W f hA
    (fun i k => hf k i) j
  have hrd : r ≤ d := by simpa only [Fintype.card_fin] using hr
  have hrι : r ≤ Fintype.card ι := hrd.trans hdim
  refine ⟨e, fun i k => (he i k).mono ?_⟩
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (rationalKernelHeight_mono hA hrι) _)

end NilpotentLieFiltration
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RankUnadaptedFactorization
namespace OAI

section

namespace Erdos3

open scoped TensorProduct BigOperators

theorem rankVerticalSelectionBudget_bounds {p : ℝ} (hp : 0 ≤ p) :
    p + 1 ≤ rankVerticalSelectionBudget p ∧
      verticalDecompositionBudget (p + 1) ≤ rankVerticalSelectionBudget p := by
  have h := verticalDecompositionBudget_nonneg (show 0 ≤ p + 1 by linarith)
  unfold rankVerticalSelectionBudget
  constructor <;> linarith

namespace RationalFilteredNilmanifold.Niltest

open CircleFourier

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  {D : RationalFilteredNilmanifold L s d}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]

theorem exists_biased_mode_restricting_frequency (T : D.Niltest (fun _ : σ => 1))
    {p : ℝ} (hp : 0 ≤ p) (hT : T.ComplexityLE p)
    (S : Submodule ℚ L) (hS : S ≤ D.filtration.layer s) (η : L →ₗ[ℚ] ℚ)
    (hchar : ∀ y ∈ S, ∀ t : ℝ, ∀ x,
      T.observable ((⟨t ⊗ₜ[ℚ] y⟩ : D.RealGroup) • x) =
        character ((t * (η y : ℝ) : ℝ) : CircleFourier.Circle) * T.observable x)
    (Q : Finset (σ → ℤ)) (hQ : Q.Nonempty)
    (hbias : Real.exp (-p) ≤ ‖𝔼 x ∈ Q, T.eval x‖) :
    ∃ (ξ : L →ₗ[ℚ] ℚ) (U : D.Niltest (fun _ : σ => 1)),
      U.ComplexityLE (rankVerticalSelectionBudget p) ∧ U.orbit = T.orbit ∧
      (∀ i, rationalLogHeight (ξ (D.basis i)) ≤ rankVerticalSelectionBudget p) ∧
      (∀ z ∈ D.filtration.realification.subgroup s, ∀ x,
        U.observable (z • x) = character ((realifyFunctional ξ z.coord : ℝ) : CircleFourier.Circle) *
          U.observable x) ∧
      (∀ y ∈ S, ξ y = η y) ∧
      Real.exp (-rankVerticalSelectionBudget p) ≤ ‖𝔼 x ∈ Q, U.eval x‖ := by
  have hp1 : 0 ≤ p + 1 := by linarith
  have hρp : (Real.exp (-p) / 2)⁻¹ ≤ Real.exp (p + 1) := by
    have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    calc
      _ = 2 * Real.exp p := by rw [inv_div, Real.exp_neg]; field_simp
      _ ≤ Real.exp 1 * Real.exp p := mul_le_mul_of_nonneg_right htwo (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add, add_comm]
  obtain ⟨ξ, U, hU, hOrbit, hheight, hvert, _, hpres, hc⟩ :=
    T.exists_correlating_vertical_mode_preserving_characters hp1
      (hT.mono (by linarith)) (Real.exp_pos (-p)) hρp hQ (fun _ => 1)
      (fun _ _ => by simp) (by rwa [norm_finiteCorrelation_one])
  rw [norm_finiteCorrelation_one] at hc
  have hthreshold : Real.exp (-rankVerticalSelectionBudget p) ≤
      Real.exp (-p) / (2 * Real.exp (verticalDecompositionBudget (p + 1))) := by
    calc
      _ = Real.exp (-p - 1) / Real.exp (verticalDecompositionBudget (p + 1)) := by
        rw [← Real.exp_sub]
        congr 1
        unfold rankVerticalSelectionBudget
        ring
      _ ≤ (Real.exp (-p) / 2) / Real.exp (verticalDecompositionBudget (p + 1)) :=
        div_le_div_of_nonneg_right (exp_sub_one_le_half_exp (-p)) (Real.exp_nonneg _)
      _ = _ := by ring
  have hfinal := hthreshold.trans hc
  have hne : ∃ x, U.observable x ≠ 0 := by
    by_contra! hzero
    have heval : ∀ x, U.eval x = 0 := fun x => hzero _
    simp only [heval, Finset.expect_const_zero, norm_zero] at hfinal
    exact (not_le_of_gt (Real.exp_pos _)) hfinal
  refine ⟨ξ, U, hU.mono (rankVerticalSelectionBudget_bounds hp).1, hOrbit,
    fun i => (hheight i).trans (rankVerticalSelectionBudget_bounds hp).2, hvert, ?_, hfinal⟩
  intro y hy
  have heq := vertical_frequency_on_real_direction D.filtration D.realLattice ξ U.observable
    hvert hne y (hS hy) (η y : ℝ) (fun t x => hpres _ _ (hchar y hy t) x)
  exact_mod_cast heq

end RationalFilteredNilmanifold.Niltest

end Erdos3

end

section

namespace Erdos3

theorem exists_rank_biased_factorization_budget (c : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p →
      rankVerticalSelectionBudget p ≤ (p + C) ^ C ∧
      (rankVerticalSelectionBudget p + c) ^ c ≤ (p + C) ^ C := by
  obtain ⟨a, _, hvertical⟩ := exists_verticalDecompositionBudget_bound
  let X : Polynomial ℕ := Polynomial.X
  let Y := X + (X + 1 + Polynomial.C a) ^ a + 1
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (Y + (Y + Polynomial.C c) ^ c)
  refine ⟨C, hC, ?_⟩
  intro p hp
  have hq : rankVerticalSelectionBudget p ≤ p + (p + 1 + a) ^ a + 1 := by
    have h := hvertical (p + 1) (by linarith)
    unfold rankVerticalSelectionBudget
    linarith only [h]
  have hq0 : 0 ≤ rankVerticalSelectionBudget p :=
    (show 0 ≤ p + 1 by linarith).trans (rankVerticalSelectionBudget_bounds hp).1
  have hY : 0 ≤ p + (p + 1 + a) ^ a + 1 := by positivity
  have hZ : 0 ≤ (p + (p + 1 + a) ^ a + 1 + c) ^ c := by positivity
  have hpow : (rankVerticalSelectionBudget p + c) ^ c ≤
      (p + (p + 1 + a) ^ a + 1 + c) ^ c := by gcongr
  have hbound : p + (p + 1 + a) ^ a + 1 +
      (p + (p + 1 + a) ^ a + 1 + c) ^ c ≤ (p + C) ^ C := by
    simpa [X, Y, Polynomial.eval₂_pow] using hbudget p hp
  exact ⟨by linarith only [hq, hZ, hbound], by linarith only [hpow, hY, hbound]⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.NativeRankZeroNiltest
namespace OAI

section

namespace Erdos3.NativeDegreeRankFamily

open scoped NNReal

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff

variable {s r : ℕ} {A : Type*} {p : ℝ} (W : NativeDegreeRankFamily s r A p)

theorem component_eval (i : Fin W.outputDim) (a : A) (n : ℤ) :
    (W.component i a).eval (fun _ => n) = W.eval i a n := rfl

end Erdos3.NativeDegreeRankFamily

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RankIntervalFactorization
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module

variable {ι : Type*} [Fintype ι] [Nonempty ι] {L : ι → Type*}
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s r : ℕ} {d : ι → ℕ}
  (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))
  (R : ∀ i, (D i).DegreeRankStructure r)

theorem productRankLayerBasis_logHeight {p : ℝ} (hp : 0 ≤ p)
    (hR : ∀ i, (R i).ComplexityLE p) (j k : Fin (s + 1))
    (a : Σ i, Fin (finrank ℚ ((R i).filtration.layer j.val k.val)))
    (b : Σ i, Fin (d i)) :
    rationalLogHeight ((Pi.basis (fun i => (D i).basis)).repr
      ((productRankLayerBasis D R j k a).val) b) ≤ p := by
  classical
  rcases a with ⟨a, m⟩
  rcases b with ⟨b, n⟩
  simp only [productRankLayerBasis, Basis.map_apply, Pi.basis_repr]
  change rationalLogHeight ((D b).basis.repr
    (((Pi.basis (fun i => (R i).basis j k)) ⟨a, m⟩ b).val) n) ≤ p
  rw [Pi.basis_apply]
  by_cases hab : a = b
  · subst b
    rw [Pi.single_eq_same]
    exact (hR a).2 j k m n
  · rw [Pi.single_eq_of_ne (Ne.symm hab)]
    simpa [rationalLogHeight] using hp

theorem piRank_complexity {p : ℝ} (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p)
    (hR : ∀ i, (R i).ComplexityLE p) :
    (piRank D R).ComplexityLE ((p + 2) ^ 2) := by
  refine ⟨pi_geometry D hp hι (fun i => (hR i).1), ?_⟩
  intro j k a b
  change Fin (finrank ℚ
    ((DegreeRankLieFiltration.pi (fun i => (R i).filtration)).layer j.val k.val)) at a
  change rationalLogHeight ((productFinBasis D).repr
    ((productRankLayerFinBasis D R j k a).val) b) ≤ (p + 2) ^ 2
  rw [productFinBasis, Basis.repr_reindex_apply, productRankLayerFinBasis, Basis.reindex_apply]
  exact (productRankLayerBasis_logHeight D R hp hR j k _ _).trans (by nlinarith [sq_nonneg p])

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.NativeDegreeRankFamily

open RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff

variable {s r : ℕ} {A : Type*} {p : ℝ} (W : NativeDegreeRankFamily s r A p)

theorem fourPointFactors_eval (out : Fin W.outputDim) (a : Fin 4 → A) (δ n : ℤ) :
    (∏ i, (W.fourPointFactors out a δ i).eval (fun _ => n)) =
      fourPointProduct (W.eval out (a 0)) (W.eval out (a 1))
        (W.eval out (a 2)) (W.eval out (a 3)) δ n := by
  have hshift : (fun _ : Unit => n) + (fun _ => δ) = (fun _ => n + δ) := rfl
  simp [fourPointFactors, Fin.prod_univ_succ, fourPointProduct, component_eval, hshift, mul_assoc]

theorem fourPointFactors_vertical (out : Fin W.outputDim) (a : Fin 4 → A) (δ : ℤ)
    (i : Fin 4) (z : W.model.RealGroup) (hz : z ∈ W.rank.realSubgroup s r)
    (x : W.model.Space) :
    (W.fourPointFactors out a δ i).observable (z • x) =
      CircleFourier.character
        ((realifyFunctional (W.fourPointFrequencies i) z.coord : ℝ) : CircleFourier.Circle) *
          (W.fourPointFactors out a δ i).observable x := by
  have h := W.vertical.vertical out z hz x
  have hn : star (W.vertical.observable out (z • x)) =
      CircleFourier.character
        ((realifyFunctional (-W.vertical.frequency) z.coord : ℝ) : CircleFourier.Circle) *
          star (W.vertical.observable out x) := by
    rw [h, star_mul, realifyFunctional_neg, AddCircle.coe_neg, CircleFourier.character_neg]
    exact mul_comm _ _
  fin_cases i
  · exact hn
  · exact h
  · exact h
  · exact hn

end Erdos3.NativeDegreeRankFamily

end

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

namespace NativeRankInterval

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

theorem productTests_eval (i : Fin I.expansion.count) (n : ℤ) :
    (∏ k, (I.productTests i k).eval (fun _ => n)) =
      fourPointProduct (W.eval out t.2.1) (W.eval out (t.2.1 - t.1))
        (W.eval out t.2.2) (W.eval out (t.2.2 - t.1)) (cyclicBranchOffset t.1 branch) n *
          ((I.expansion.test i).raiseStep (Nat.sub_le s 1)).eval (fun _ => n) := by
  rw [Fintype.prod_option]
  change ((I.expansion.test i).raiseStep (Nat.sub_le s 1)).eval (fun _ => n) *
    (∏ k, (W.fourPointFactors out (rankQuadrupleParameters t)
      (cyclicBranchOffset t.1 branch) k).eval (fun _ => n)) = _
  rw [W.fourPointFactors_eval]
  exact mul_comm _ _

theorem productTests_vertical (hs : 1 ≤ s) (i : Fin I.expansion.count)
    (R₀ : ((I.expansion.model i).raiseStep (Nat.sub_le s 1)).DegreeRankStructure r)
    (k : Option (Fin 4)) (z : (I.productModels i k).RealGroup)
    (hz : z ∈ (I.productRanks i R₀ k).realSubgroup s r) (x : (I.productModels i k).Space) :
    (I.productTests i k).observable (z • x) =
      CircleFourier.character
        ((realifyFunctional (I.productFrequencies i k) z.coord : ℝ) : CircleFourier.Circle) *
          (I.productTests i k).observable x := by
  cases k with
  | none => exact (I.expansion.test i).raiseStep_rank_vertical (by omega) R₀ z hz x
  | some k =>
    exact W.fourPointFactors_vertical out (rankQuadrupleParameters t)
      (cyclicBranchOffset t.1 branch) k z hz x

end NativeRankInterval

end Erdos3

end

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

variable [TopologicalSpace (ℝ ⊗[ℚ]
    (∀ k : Option (Fin 4), optionLieSpace (I.expansion.L i) (fun _ : Fin 4 => W.L) k))]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ]
    (∀ k : Option (Fin 4), optionLieSpace (I.expansion.L i) (fun _ : Fin 4 => W.L) k))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ]
    (∀ k : Option (Fin 4), optionLieSpace (I.expansion.L i) (fun _ : Fin 4 => W.L) k))]
  [T2Space (ℝ ⊗[ℚ]
    (∀ k : Option (Fin 4), optionLieSpace (I.expansion.L i) (fun _ : Fin 4 => W.L) k))]

theorem productSymbol_eq {κ : Type*}
    (e : Basis κ ℚ (∀ k : Option (Fin 4),
      optionLieSpace (I.expansion.L i) (fun _ : Fin 4 => W.L) k)) (ω : κ → ℕ)
    (hF : ∀ j, (pi (I.productModels i)).filtration.layer j =
      Submodule.span ℚ (e '' {a | j ≤ ω a}))
    (T : (pi (I.productModels i)).Niltest (fun _ : Unit => 1)) (hT : T.orbit = I.productOrbit i) :
    T.symbol e ω hF = I.productSymbol i e ω hF := by
  unfold RationalFilteredNilmanifold.Niltest.symbol productSymbol
  apply congrArg ((pi (I.productModels i)).filtration.realPolynomialSymbolHom e ω hF (fun _ => 1))
  apply NilpotentLieBCHGroup.ext
  apply Subtype.ext
  exact congrArg (fun o : (pi (I.productModels i)).filtration.realification.PolynomialOrbit
    (fun _ : Unit => 1) => o.log) hT

end Erdos3.NativeRankInterval

end

section

namespace Erdos3.NativeRankInterval

open RationalFilteredNilmanifold
open scoped BigOperators

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

theorem rankProjection_frequency
    (x : ∀ k : Option (Fin 4), optionLieSpace (I.expansion.L i) (fun _ : Fin 4 => W.L) k) :
    piFrequency (I.productFrequencies i) x =
      W.vertical.frequency (I.rankProjection i x 0) + W.vertical.frequency (I.rankProjection i x 1) -
        W.vertical.frequency (I.rankProjection i x 2) - W.vertical.frequency (I.rankProjection i x 3) := by
  rw [piFrequency_apply, Fintype.sum_option]
  simp only [Fin.sum_univ_succ]
  change 0 + (-W.vertical.frequency (x (some 0)) +
    (W.vertical.frequency (x (some 1)) + (W.vertical.frequency (x (some 2)) +
      (-W.vertical.frequency (x (some 3)) + 0)))) =
    W.vertical.frequency (x (some 1)) + W.vertical.frequency (x (some 2)) -
      W.vertical.frequency (x (some 0)) - W.vertical.frequency (x (some 3))
  ring

end Erdos3.NativeRankInterval

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.NativeCoordinateEstimates
namespace OAI

section

namespace Erdos3

namespace NilpotentLieFiltration

open Module

theorem exists_refiltration_bases_in_coordinates
    {ι κ ν L : Type*} [Fintype ι] [Fintype κ] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (e : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
    (b : Basis ν ℚ L) (U : LieSubalgebra ℚ F.AssociatedGraded)
    (v : κ → F.AssociatedGraded) (hspan : Submodule.span ℚ (Set.range v) = U.toSubmodule)
    {p : ℝ} (hp : 0 ≤ p) (hd : (Fintype.card ι : ℝ) ≤ p) (hκ : (Fintype.card κ : ℝ) ≤ p)
    (hv : ∀ i j, rationalLogHeight ((F.associatedGradedBasis e ω hF).repr (v i) j) ≤ p)
    (he : ∀ i j, rationalLogHeight (b.repr (e i) j) ≤ p) :
    ∀ d, ∃ a : Basis (Fin (finrank ℚ (F.gradedRefiltrationLayer U d))) ℚ
        (F.gradedRefiltrationLayer U d),
      ∀ i j, rationalLogHeight (b.repr (a i : L) j) ≤ refiltrationCoordinateBudget p := by
  let H := ⌈Real.exp p⌉₊
  have hHp : (H : ℝ) ≤ Real.exp (p + 1) := ceil_exp_le_exp_add_one hp
  obtain ⟨B, _, hB, hbasis⟩ := F.exists_uniform_refiltration_layer_bases e ω hF U v hspan
    (one_le_ceil_exp p) (fun i j => rationalHeightLE_ceil_exp (hv i j))
    (by linarith : 0 ≤ p + 1) (hd.trans (by linarith)) (hκ.trans (by linarith)) hHp
  let r := (p + 1 + (p + 3) ^ 7 + 2) ^ 9
  have hBr : (B : ℝ) ≤ Real.exp r := by
    simpa only [r, show p + 1 + 2 = p + 3 by ring] using hB
  let t := r + p + 2
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hpt : p ≤ t := by dsimp [t]; linarith
  have hrt : r ≤ t := by dsimp [t]; linarith
  have hHt : (H : ℝ) ≤ Real.exp t :=
    hHp.trans (Real.exp_le_exp.mpr (by dsimp [t]; linarith))
  intro d
  obtain ⟨a, ha⟩ := hbasis d
  refine ⟨a, ?_⟩
  intro i j
  have hx : ∀ k, rationalLogHeight (e.repr (a i : L) k) ≤ t := fun k =>
    (rationalLogHeight_le_of_height (ha i k) hBr).trans hrt
  have h := rational_basis_coordinates_logHeight e b ht (hd.trans hpt) hHt
    (fun i j => rationalHeightLE_ceil_exp (he i j)) (a i : L) hx j
  have hshape : t + 2 = r + p + 4 := by dsimp [t]; ring
  rw [hshape] at h
  exact h

end NilpotentLieFiltration

end Erdos3

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
  (I : NativeRankInterval W out H t branch p q) (i : Fin I.expansion.count)
  (U : LieSubalgebra ℚ (pi (I.productModels i)).filtration.AssociatedGraded)

theorem refilteredHorizontalImage_frequency {J : Type*} (d : J → ℕ) (a : FreeMagma J)
    (hd : lieTreeWeight d a = s) (hr : a.length = r)
    (hker : ∀ z : J → ℝ ⊗[ℚ]
        (∀ k : Option (Fin 4), optionLieSpace (I.expansion.L i) (fun _ : Fin 4 => W.L) k),
      (∀ j, z j ∈ (pi (I.productModels i)).filtration.realGradedRefiltrationLayer U (d j)) →
      realifyFunctional (piFrequency (I.productFrequencies i)) (lieTreeEval z a) = 0)
    (v : ∀ j, Fin 4 → W.rank.filtration.HigherHorizontal (d j))
    (hv : ∀ j, v j ∈ I.refilteredHorizontalImage i U (d j)) :
    W.vertical.frequency (W.rank.filtration.horizontalTreeValue d a (fun j => v j 0)) +
      W.vertical.frequency (W.rank.filtration.horizontalTreeValue d a (fun j => v j 1)) -
      W.vertical.frequency (W.rank.filtration.horizontalTreeValue d a (fun j => v j 2)) -
      W.vertical.frequency (W.rank.filtration.horizontalTreeValue d a (fun j => v j 3)) = 0 := by
  apply W.rank.filtration.layerHorizontalImage_frequency
    ((pi (I.productModels i)).filtration.gradedRefiltrationLayer U)
    (I.rankProjection i) (I.rankProjection_mem_refiltered i U) W.vertical.frequency d a hd hr ?_ v hv
  intro u hu
  rw [← I.rankProjection_frequency i]
  exact rational_lieTree_kernel_of_real
    (fun j => (pi (I.productModels i)).filtration.gradedRefiltrationLayer U (d j))
    (piFrequency (I.productFrequencies i)) a hker u hu

theorem refiltered_sunflower_bracket {J : Type*} (d : J → ℕ) (a : FreeMagma J)
    (hd : lieTreeWeight d a = s) (hr : a.length = r)
    (hker : ∀ z : J → ℝ ⊗[ℚ]
        (∀ k : Option (Fin 4), optionLieSpace (I.expansion.L i) (fun _ : Fin 4 => W.L) k),
      (∀ j, z j ∈ (pi (I.productModels i)).filtration.realGradedRefiltrationLayer U (d j)) →
      realifyFunctional (piFrequency (I.productFrequencies i)) (lieTreeEval z a) = 0)
    (v : ∀ j, W.rank.filtration.HigherHorizontal (d j))
    (hv : ∀ j, v j ∈ fourFirstProjection (I.refilteredHorizontalImage i U (d j)))
    (j k : J) (hjk : j ≠ k) (hj : j ∈ lieTreeSupport a) (hk : k ∈ lieTreeSupport a)
    (hvj : v j ∈ fourDependentProjection (I.refilteredHorizontalImage i U (d j)))
    (hvk : v k ∈ fourDependentProjection (I.refilteredHorizontalImage i U (d k))) :
    W.vertical.frequency (W.rank.filtration.horizontalTreeValue d a v) = 0 :=
  four_dependent_inputs_vanish (lieTreeSupport a) (W.rank.filtration.horizontalTreeValue d a)
    (fun u j hj hu => W.rank.filtration.horizontalTreeValue_zero_of_leaf d a u (i := j) hj hu)
    W.vertical.frequency (map_zero _) (fun j => I.refilteredHorizontalImage i U (d j))
    (I.refilteredHorizontalImage_frequency i U d a hd hr hker) v hv j k hjk hj hk hvj hvk

theorem sunflowerKernel_of_real (hker : I.BracketKernel i U) :
    I.SunflowerKernel i U := by
  intro n d a hd hr v hv j k hjk hj hk hvj hvk
  exact I.refiltered_sunflower_bracket i U d a hd hr (hker n d a hd hr) v hv j k hjk hj hk hvj hvk

end Erdos3.NativeRankInterval

end

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

noncomputable def fourRankBasis {s r : ℕ} {A : Type*} {p : ℝ} (W : NativeDegreeRankFamily s r A p) :
    Basis (Σ _ : Fin 4, Fin W.dim) ℚ (Fin 4 → W.L) :=
  Pi.basis (fun _ : Fin 4 => W.model.basis)

end NativeDegreeRankFamily

namespace NativeRankInterval

variable {s r N : ℕ} [NeZero N] {b p q : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {t : ZMod N × ZMod N × ZMod N} {branch : Bool}
  (I : NativeRankInterval W out H t branch p q) (i : Fin I.expansion.count)

theorem rankProjection_coordinates
    (x : ∀ k : Option (Fin 4), optionLieSpace (I.expansion.L i) (fun _ : Fin 4 => W.L) k)
    (j : Σ _ : Fin 4, Fin W.dim) :
    W.fourRankBasis.repr (I.rankProjection i x) j =
      (pi (I.productModels i)).basis.repr x
        ((Fintype.equivFin (Σ k : Option (Fin 4),
          Fin (optionDimension (I.expansion.dim i) (fun _ : Fin 4 => W.dim) k)))
          ⟨some ((![1, 2, 0, 3] : Fin 4 → Fin 4) j.1), j.2⟩) := by
  change (Pi.basis (fun _ : Fin 4 => W.model.basis)).repr (I.rankProjection i x) j = _
  rw [Pi.basis_repr]
  let k : Σ a : Option (Fin 4), Fin (optionDimension (I.expansion.dim i) (fun _ : Fin 4 => W.dim) a) :=
    ⟨some ((![1, 2, 0, 3] : Fin 4 → Fin 4) j.1), j.2⟩
  have hk := (Fintype.equivFin _).symm_apply_apply k
  have h := productFinBasis_repr (I.productModels i) x ((Fintype.equivFin _) k)
  have heq := congrArg (fun z : Σ a : Option (Fin 4),
      Fin (optionDimension (I.expansion.dim i) (fun _ : Fin 4 => W.dim) a) =>
    (I.productModels i z.1).basis.repr (x z.1) z.2) hk
  exact (h.trans heq).symm

theorem rankProjection_coordinates_logHeight
    (x : ∀ k : Option (Fin 4), optionLieSpace (I.expansion.L i) (fun _ : Fin 4 => W.L) k)
    {P : ℝ} (hx : ∀ j, rationalLogHeight ((pi (I.productModels i)).basis.repr x j) ≤ P)
    (j : Σ _ : Fin 4, Fin W.dim) :
    rationalLogHeight (W.fourRankBasis.repr (I.rankProjection i x) j) ≤ P := by
  rw [I.rankProjection_coordinates i x j]
  exact hx _

end NativeRankInterval

end Erdos3

end

section

namespace Erdos3.NativeRankInterval.SunflowerWitness

open RationalFilteredNilmanifold

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P Q : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {t : ZMod N × ZMod N × ZMod N} {branch : Bool}
  {I : NativeRankInterval W out H t branch p q}

noncomputable def mono (D : I.SunflowerWitness P) (hPQ : P ≤ Q) : I.SunflowerWitness Q :=
  { D with
    lower_complexity := D.lower_complexity.mono D.lowerRank hPQ
    adapted_complexity := D.adapted_complexity.mono D.adapted.rank hPQ
    forward := fun j k => (D.forward j k).trans hPQ
    backward := fun k j => (D.backward k j).trans hPQ
    denominator_bound := D.denominator_bound.trans (Real.exp_le_exp.mpr hPQ)
    height := fun j k => (D.height j k).trans hPQ
    factorization := NilpotentLieFiltration.SymbolFactorizationIn.mono
      (pi (I.productModels D.index)).filtration D.adapted.basis D.adapted.weight D.adapted.layers
      D.factorization hPQ (fun _ => by exact_mod_cast I.length_pos) }

end Erdos3.NativeRankInterval.SunflowerWitness

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.FreeDegreeRankNilmanifold
namespace OAI

section

namespace Erdos3

open Module

theorem exists_controlled_nilmanifold_of_tails (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (L : Type*) [LieRing L] [LieAlgebra ℚ L] (r d : ℕ)
      (F : DegreeRankLieFiltration L s r) (b : Basis (Fin d) ℚ L),
      (∀ i j, ∃ c ≤ d, F.layer i j = basisTail b c) →
      ∀ (l : ℕ), 0 < l → ∀ (p : ℝ), 0 ≤ p → (d : ℝ) ≤ p → (l : ℝ) ≤ Real.exp p →
      (∀ i j k, rationalLogHeight (lieStructureConstants b i j k) ≤ p) →
      p ≤ (p + C) ^ C ∧ ∃ D : RationalFilteredNilmanifold L s d,
        ∃ R : D.DegreeRankStructure r, D.basis = b ∧ R.filtration = F ∧
          l ∣ D.grid ∧ bchSubgroupCoordinates D.basis D.lattice = scaledIntegerGrid D.grid ∧
          R.ComplexityLE ((p + C) ^ C) := by
  obtain ⟨C, hC, hgrid⟩ := exists_controlled_integral_grid s
  refine ⟨C, hC, ?_⟩
  intro L _ _ r d F b htail l hl p hp hd hlp hc
  obtain ⟨hpC, B, hB, hdiv, hBbound, hstable⟩ := hgrid L (Fin d) b
    F.associatedDegree.lowerCentralSeries_eq_bot l hl p hp
    (by simpa only [Fintype.card_fin] using hd) hlp hc
  refine ⟨hpC, F.integralGridNilmanifold b htail B hB hstable,
    F.integralGridDegreeRank b htail B hB hstable, rfl, rfl, hdiv,
    F.integralGridNilmanifold_coordinates b htail B hB hstable, ?_⟩
  exact F.integralGridDegreeRank_complexity b htail B hB hstable
    (hp.trans hpC) (hd.trans hpC) hBbound (fun i j k => (hc i j k).trans hpC)

end Erdos3

end

section

namespace Erdos3

open Module
open scoped Matrix

theorem exists_free_degree_rank_nilmanifold (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (X : Type*) [Fintype X] (r : ℕ) (hr : r ≤ s)
      (w : X → ℕ) (hw : ∀ x, 0 < w x) (l : ℕ), 0 < l →
      ∀ (p : ℝ), 0 ≤ p → (Fintype.card X : ℝ) ≤ p → (l : ℝ) ≤ Real.exp p →
      ∃ D : RationalFilteredNilmanifold (FreeDegreeRankLieAlgebra X s r w hw) s
          (finrank ℚ (FreeDegreeRankLieAlgebra X s r w hw)),
        ∃ R : D.DegreeRankStructure r,
          R.filtration = FreeDegreeRankLieAlgebra.filtration X s r w hw hr ∧
          R.ComplexityLE ((p + C) ^ C) ∧ IsCentralLieBasis D.basis ∧ l ∣ D.grid ∧
          bchSubgroupCoordinates D.basis D.lattice = scaledIntegerGrid D.grid ∧
          (∀ x ∈ FreeNilpotentLieAlgebra.treeGenerators X s, ∀ i,
            rationalLogHeight (D.basis.repr (FreeDegreeRankLieAlgebra.projection X s r w hw x) i) ≤ (p + C) ^ C) ∧
          ∃ e : Basis (Fin (finrank ℚ (FreeNilpotentLieAlgebra X s))) ℚ (FreeNilpotentLieAlgebra X s),
            (∀ i, e i ∈ FreeNilpotentLieAlgebra.treeGenerators X s) ∧
            (finrank ℚ (FreeNilpotentLieAlgebra X s) : ℝ) ≤ (p + C) ^ C ∧
            ∃ S : Matrix (Fin (finrank ℚ (FreeNilpotentLieAlgebra X s)))
                (Fin (finrank ℚ (FreeDegreeRankLieAlgebra X s r w hw))) ℚ,
              LinearMap.toMatrix e D.basis (FreeDegreeRankLieAlgebra.projection X s r w hw).toLinearMap * S = 1 ∧
              ∀ i j, rationalLogHeight (S i j) ≤ (p + C) ^ C := by
  obtain ⟨a, _, hfree⟩ := exists_adapted_free_degree_rank_model s
  obtain ⟨c, _, hnative⟩ := exists_controlled_nilmanifold_of_tails s
  let Q : Polynomial ℕ := Polynomial.X + (Polynomial.X + Polynomial.C a) ^ a
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (Q + (Q + Polynomial.C c) ^ c)
  refine ⟨C, hC, ?_⟩
  intro X _ r hr w hw l hl p hp hX hlp
  let B := (p + a) ^ a
  let T := p + B
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hBT : B ≤ T := le_add_of_nonneg_left hp
  have hpT : p ≤ T := le_add_of_nonneg_right hB
  have hT : 0 ≤ T := hp.trans hpT
  have hsum : T + (T + c) ^ c ≤ (p + C) ^ C := by
    simpa [Q, T, B, Polynomial.eval₂_pow] using hbudget p hp
  have hTC : T ≤ (p + C) ^ C :=
    (le_add_of_nonneg_right (by positivity : 0 ≤ (T + c) ^ c)).trans hsum
  have hNC : (T + c) ^ c ≤ (p + C) ^ C := (le_add_of_nonneg_left hT).trans hsum
  obtain ⟨hdim, b, hcentral, htail, hstructure, htree, e, he, hdim₀, S, hS, hSH⟩ :=
    hfree X r hr w hw p hp hX
  obtain ⟨_, D, R, hb, hR, hdiv, hcoords, hcomplexity⟩ :=
    hnative (FreeDegreeRankLieAlgebra X s r w hw) r _
      (FreeDegreeRankLieAlgebra.filtration X s r w hw hr) b htail l hl T hT
      (hdim.trans hBT) (hlp.trans (Real.exp_le_exp.mpr hpT))
      (fun i j k => (hstructure i j k).trans hBT)
  refine ⟨D, R, hR, hcomplexity.mono R hNC, ?_, hdiv, hcoords, ?_, e, he,
    hdim₀.trans (hBT.trans hTC), S, ?_, fun i j => (hSH i j).trans (hBT.trans hTC)⟩
  · rw [hb]
    exact hcentral
  · intro x hx i
    rw [hb]
    exact (htree x hx i).trans (hBT.trans hTC)
  · rw [hb]
    exact hS

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.RankInvariantNiltestBudget
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.DegreeRankStructure

open NilpotentLieBCHGroup
open scoped TensorProduct NNReal

variable {L σ : Type*} [LieRing L] [LieAlgebra ℚ L] {s r d n : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d} (R : D.DegreeRankStructure (r + 1))
  [TopologicalSpace (ℝ ⊗[ℚ] (L ⧸ R.filtration.layerIdeal s (r + 1)))]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] (L ⧸ R.filtration.layerIdeal s (r + 1)))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] (L ⧸ R.filtration.layerIdeal s (r + 1)))]
  [T2Space (ℝ ⊗[ℚ] (L ⧸ R.filtration.layerIdeal s (r + 1)))]

theorem exists_rankInvariant_niltest
    (Q : RationalFilteredNilmanifold (L ⧸ R.filtration.layerIdeal s (r + 1)) s n)
    (hQF : Q.filtration = D.filtration.quotientLie
      (R.filtration.layerIdeal s (r + 1)) R.terminal_le_topRankIdeal)
    (hQL : Q.lattice = D.lattice.map (D.filtration.quotientStepHom
      (R.filtration.layerIdeal s (r + 1)) R.terminal_le_topRankIdeal))
    {w : σ → ℕ} (T : D.Niltest w)
    (hinv : ∀ z ∈ R.realSubgroup s (r + 1), ∀ x, T.observable (z • x) = T.observable x)
    (H : ℕ) (hH : 1 ≤ H)
    (he : ∀ i j, RationalHeightLE (Q.basis.repr
      (lieQuotientMap (R.filtration.layerIdeal s (r + 1)) (D.basis j)) i) H)
    (hc : ∀ i j k, RationalHeightLE (lieStructureConstants Q.basis i j k) H) :
    ∃ S : Q.Niltest w,
      S.orbit = R.rankQuotientOrbit Q hQF T.orbit ∧
      S.normBound = T.normBound ∧
      S.lipBound = rationalReconstructionLipschitzBound s d n H T.lipBound T.normBound ∧
      (∀ x : D.RealGroup, S.observable (QuotientGroup.mk
        (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
          (hM := Q.filtration.lowerCentralSeries_eq_bot)
          (lieQuotientMap (R.filtration.layerIdeal s (r + 1))) x)) =
        T.observable (QuotientGroup.mk x)) ∧
      ∀ x, S.eval x = T.eval x := by
  have hcover : Q.lattice ≤ D.lattice.map
      (mapOfSteps (lieQuotientMap (R.filtration.layerIdeal s (r + 1)))) := by
    rw [hQL]
    exact le_rfl
  obtain ⟨f, hf, hfLip, hfBound⟩ := exists_lipschitz_realification_reconstruction
    D.basis Q.basis (lieQuotientMap (R.filtration.layerIdeal s (r + 1)))
    (lieQuotientMap_surjective _) D.lattice Q.lattice hcover
    D.grid Q.grid H D.grid_pos Q.grid_pos hH D.outer_grid Q.outer_grid he hc
    T.observable (fun k hk x => hinv k (by
      apply (realification_mkQ_eq_zero_iff
        (R.filtration.layerIdeal s (r + 1)).toSubmodule k.coord).mp
      exact congrArg (fun z : Q.RealGroup => z.coord) (MonoidHom.mem_ker.mp hk))
      (QuotientGroup.mk x)) T.lipBound T.normBound T.lipschitz T.norm_le
  let S : Q.Niltest w := {
    orbit := R.rankQuotientOrbit Q hQF T.orbit
    observable := f
    normBound := T.normBound
    lipBound := rationalReconstructionLipschitzBound s d n H T.lipBound T.normBound
    norm_le := hfBound
    lipschitz := by
      let : MetricSpace (Q.RealGroup ⧸ Q.lattice.map realificationHom) :=
        realificationQuotientMetricSpace Q.basis Q.lattice Q.grid Q.grid_pos Q.outer_grid
      exact hfLip.weaken (by simp only [Fintype.card_fin]; exact le_rfl)
  }
  refine ⟨S, rfl, rfl, rfl, hf, ?_⟩
  intro x
  exact (congrArg (fun z : Q.RealGroup => f (QuotientGroup.mk z))
    (R.rankQuotientOrbit_eval Q hQF T.orbit x)).trans (hf _)

end Erdos3.RationalFilteredNilmanifold.DegreeRankStructure

end

section

namespace Erdos3.RationalFilteredNilmanifold.DegreeRankStructure

open scoped TensorProduct NNReal

theorem exists_rankInvariant_niltest_budget (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L σ : Type*} [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {r d n : ℕ} {D : RationalFilteredNilmanifold L s d} (R : D.DegreeRankStructure (r + 1))
      [TopologicalSpace (ℝ ⊗[ℚ] (L ⧸ R.filtration.layerIdeal s (r + 1)))]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] (L ⧸ R.filtration.layerIdeal s (r + 1)))]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] (L ⧸ R.filtration.layerIdeal s (r + 1)))]
      [T2Space (ℝ ⊗[ℚ] (L ⧸ R.filtration.layerIdeal s (r + 1)))]
      (Q : RationalFilteredNilmanifold (L ⧸ R.filtration.layerIdeal s (r + 1)) s n)
      (hQF : Q.filtration = D.filtration.quotientLie
        (R.filtration.layerIdeal s (r + 1)) R.terminal_le_topRankIdeal)
      (_hQL : Q.lattice = D.lattice.map
        (D.filtration.quotientStepHom (R.filtration.layerIdeal s (r + 1)) R.terminal_le_topRankIdeal))
      {w : σ → ℕ} (T : D.Niltest w) (p : ℝ),
      0 ≤ p → T.ComplexityLE p → Q.GeometryComplexityLE p →
      (∀ i j, rationalLogHeight (Q.basis.repr
        (lieQuotientMap (R.filtration.layerIdeal s (r + 1)) (D.basis j)) i) ≤ p) →
      (∀ z ∈ R.realSubgroup s (r + 1), ∀ x,
        T.observable (z • x) = T.observable x) →
      ∃ S : Q.Niltest w, S.orbit = R.rankQuotientOrbit Q hQF T.orbit ∧
        S.normBound = T.normBound ∧ S.ComplexityLE ((p + C) ^ C) ∧
        (∀ x : D.RealGroup, S.observable (QuotientGroup.mk
          (NilpotentLieBCHGroup.realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
            (hM := Q.filtration.lowerCentralSeries_eq_bot)
            (lieQuotientMap (R.filtration.layerIdeal s (r + 1))) x)) =
          T.observable (QuotientGroup.mk x)) ∧
        ∀ x, S.eval x = T.eval x := by
  obtain ⟨a, _, hcost⟩ := exists_rationalReconstructionLipschitzBound_exp s
  let X : Polynomial ℕ := Polynomial.X
  let P := (X + 1 + Polynomial.C a) ^ a + X + 4
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro L σ _ _ _ _ _ _ r d n D R _ _ _ _ Q hQF hQL w T p hp hT hQ he hinv
  let H := ⌈Real.exp p⌉₊
  obtain ⟨S, hSo, hSn, hSl, hSp, hSe⟩ := R.exists_rankInvariant_niltest Q hQF hQL T hinv H
    (one_le_ceil_exp p) (fun i j => rationalHeightLE_ceil_exp (he i j))
    (fun i j k => rationalHeightLE_ceil_exp (hQ.2.2.1 i j k))
  have hB : (T.normBound : ℝ) ≤ Real.exp p := by
    linarith [T.observable_budget hT, T.lipBound.coe_nonneg]
  have hL : (T.lipBound : ℝ) ≤ Real.exp p := by
    linarith [T.observable_budget hT, T.normBound.coe_nonneg]
  have hpp : Real.exp p ≤ Real.exp (p + 1) := Real.exp_le_exp.mpr (by linarith)
  let r := (p + 1 + a) ^ a
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hK : (S.lipBound : ℝ) ≤ Real.exp r := by
    rw [hSl]
    exact hcost d n H T.lipBound T.normBound (p + 1) (by linarith)
      (hT.1.1.trans (by linarith)) (hQ.1.trans (by linarith))
      (ceil_exp_le_exp_add_one hp) (hL.trans hpp) (hB.trans hpp)
  have hnum : 2 + (S.normBound : ℝ) + (S.lipBound : ℝ) ≤ Real.exp (r + p + 4) := by
    have hSn' : (S.normBound : ℝ) ≤ Real.exp (r + p) := by
      rw [hSn]
      exact hB.trans (Real.exp_le_exp.mpr (by linarith))
    have hSl' : (S.lipBound : ℝ) ≤ Real.exp (r + p) :=
      hK.trans (Real.exp_le_exp.mpr (by linarith))
    calc
      _ ≤ 4 * Real.exp (r + p) := by linarith [Real.one_le_exp (show 0 ≤ r + p by linarith)]
      _ ≤ Real.exp 4 * Real.exp (r + p) := mul_le_mul_of_nonneg_right
        (by linarith [Real.add_one_le_exp (4 : ℝ)]) (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hbound : r + p + 4 ≤ (p + C) ^ C := by
    simpa [r, P, X, Polynomial.eval₂_pow] using hbudget p hp
  refine ⟨S, hSo, hSn, ⟨hQ.mono Q ((by linarith : p ≤ r + p + 4).trans hbound), ?_⟩, hSp, hSe⟩
  exact ((Real.log_le_iff_le_exp (by positivity)).mpr hnum).trans hbound

end Erdos3.RationalFilteredNilmanifold.DegreeRankStructure

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeSubspaceFreeModel
namespace OAI

section

namespace Erdos3

open scoped TensorProduct BigOperators NNReal

theorem realify_pairDifferenceFunctional {L : Type*} [LieRing L] [LieAlgebra ℚ L]
    (η : L →ₗ[ℚ] ℚ) (x : ℝ ⊗[ℚ] (Fin 2 → L)) :
    realifyFunctional (pairDifferenceFunctional η) x =
      realifyFunctional η (realificationLieHom (liePiEval (0 : Fin 2)) x) -
        realifyFunctional η (realificationLieHom (liePiEval (1 : Fin 2)) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    simp only [realifyFunctional_tmul, pairDifferenceFunctional_apply,
      realificationLieHom_tmul, liePiEval_apply, Rat.cast_sub, mul_sub]
  | add x y hx hy => simp only [map_add, hx, hy]; ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.UnitVerticalCyclicDifference
namespace OAI

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators NNReal

variable {p : ℝ} (W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p)

noncomputable def quadraticRoot :
    NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) (tensorPowerBudget 2 p) :=
  (W.rationalDilation (1 / 2)).tensorPower 2

end Erdos3.NativeMultidegreeNilcharacter

end

end OAI
end


