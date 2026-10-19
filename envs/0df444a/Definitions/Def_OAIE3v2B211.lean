-- Prove2me | Definitions.Def_OAIE3v2B211
-- name    : OAIE3v2B211
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-18T04:09:11.052981+00:00
-- url     : https://prove2.me/theorems/f0d6fc22-de3c-4368-89ad-88ab86baad23
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 215 of 311
-- statement:
--   Definitions bundle 215 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B178`, `OAIE3v2B299`, `OAIE3v2B180`, `OAIE3v2B181`, `OAIE3v2B188`, `OAIE3v2B190`, `OAIE3v2B191`, `OAIE3v2B192`, `OAIE3v2B193` of this split.
--
--   Modules: `Estimates/FiniteMarkedFreezingCellBound.lean`, `Estimates/LowerRefilteredCyclicExpansion.lean`, `Estimates/NativeDetectorContradictionSpec.lean`, `Estimates/NativeOptionFixedSourceQuotientMarkStrong.lean`, `Estimates/NativeOptionTargetObservableRegularity.lean`, `Estimates/NativeResidualCrossInduction.lean`, `Estimates/PrescribedPartitionExpansionCore.lean`, `Fourier/PreparedCoefficientTorusCompact.lean`, `Geometry/AllocatedGeometricInputBudget.lean`, `Geometry/PreparedDeterminingCoordinates.lean`, `Lattices/QuadraticMarkedAffine.lean`, `Linear/AllocatedModularRankMixedUniform.lean`, `Linear/RankPreparationProjectedAxisBudget.lean`, `Polynomial/NativeMarkedPolynomialFreezing.lean`, `Polynomial/UniformFiniteMarkedPolynomialFreezing.lean`, `Sampling/ForecastNativeJointTestBudget.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B178
import Definitions.Def_OAIE3v2B299
import Definitions.Def_OAIE3v2B180
import Definitions.Def_OAIE3v2B181
import Definitions.Def_OAIE3v2B188
import Definitions.Def_OAIE3v2B190
import Definitions.Def_OAIE3v2B191
import Definitions.Def_OAIE3v2B192
import Definitions.Def_OAIE3v2B193

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.NativeMarkedPolynomialFreezing
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest
open NilpotentLieBCHGroup
open scoped TensorProduct NNReal
variable {σ L M : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s d t : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}

theorem observable_frozenMarked_polynomial_factors
    (T : D.Niltest w) (G : NilpotentLieFiltration M t)
    (φ : L →ₗ⁅ℚ⁆ M) (S : M →ₗ[ℚ] L)
    (hS : ∀ j, ∀ y ∈ G.layer j, S y ∈ D.filtration.layer j)
    (hsection : Function.RightInverse S φ)
    (g E P R : (D.filtration.realification.adaptedPolynomialFiltration w).Group)
    (hfac : E * P * R = g)
    (EF RF : (G.realification.adaptedPolynomialFiltration w).Group)
    (kE kR : D.RealGroup)
    (hkE : realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
      (hM := G.lowerCentralSeries_eq_bot) φ kE = 1)
    (hkR : realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
      (hM := G.lowerCentralSeries_eq_bot) φ kR = 1)
    (z : σ → ℝ)
    (hcoset : (QuotientGroup.mk (D.filtration.adaptedPolynomialRealValueHom w z
      ((D.filtration.filteredRealPolynomialSection G w S hS RF)⁻¹ * R)) : D.Space) =
        QuotientGroup.mk kR) :
    letI := rightMetricSpace
      (hnil := D.filtration.realification.lowerCentralSeries_eq_bot) (D.basis.baseChange ℝ)
    ‖T.observable (QuotientGroup.mk (D.filtration.adaptedPolynomialRealValueHom w z g)) -
      T.observable (QuotientGroup.mk (D.filtration.adaptedPolynomialRealValueHom w z
        (D.filtration.frozenMarkedLeft G w S hS EF kE * P *
          D.filtration.frozenMarkedRight G w S hS RF kR)))‖ ≤
      (T.lipBound : ℝ) * dist
        (D.filtration.adaptedPolynomialRealValueHom w z
          (E * (D.filtration.filteredRealPolynomialSection G w S hS EF)⁻¹)) kE := by
  let ρ := fun y : G.realification.Group =>
    (⟨S.baseChange ℝ y.coord⟩ : D.RealGroup)
  have he := D.filtration.filteredRealPolynomialSection_value G w S hS EF z
  have hr := D.filtration.filteredRealPolynomialSection_value G w S hS RF z
  have hc : (QuotientGroup.mk
      ((ρ (G.adaptedPolynomialRealValueHom w z RF))⁻¹ *
        D.filtration.adaptedPolynomialRealValueHom w z R) : D.Space) =
      QuotientGroup.mk kR := by
    simpa only [map_mul, map_inv, hr] using hcoset
  have hout := T.observable_freeze_marked_kernel_factors
    (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
      (hM := G.lowerCentralSeries_eq_bot) φ) ρ
    (D.filtration.real_linear_section_rightInverse G φ S hsection)
    (D.filtration.adaptedPolynomialRealValueHom w z E)
    (D.filtration.adaptedPolynomialRealValueHom w z P)
    (D.filtration.adaptedPolynomialRealValueHom w z R)
    (G.adaptedPolynomialRealValueHom w z EF) (G.adaptedPolynomialRealValueHom w z RF)
    kE kR hkE hkR hc
  rw [← hfac]
  simpa only [NilpotentLieFiltration.frozenMarkedLeft,
    NilpotentLieFiltration.frozenMarkedRight, map_mul, map_inv,
    NilpotentLieFiltration.adaptedPolynomialRealValueHom_constant, he, hr] using hout.2.2

end Erdos3.RationalFilteredNilmanifold.Niltest

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeOptionFixedSourceQuotientMarkStrong
namespace OAI

section

universe u v

namespace Erdos3.RationalFilteredNilmanifold

open Module
open scoped TensorProduct NNReal

variable {ι : Type v} [Fintype ι] {L₀ : Type u} {L : ι → Type u}
    [LieRing L₀] [∀ i, LieRing (L i)] [LieAlgebra ℚ L₀] [∀ i, LieAlgebra ℚ (L i)]
    {s d₀ : ℕ} {d : ι → ℕ}
    (D₀ : RationalFilteredNilmanifold L₀ s d₀)
    (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))
    {P : Type*} (observable : P → D₀.Space → ℂ)

section Metric

variable [TopologicalSpace (ℝ ⊗[ℚ] L₀)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L₀)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L₀)] [T2Space (ℝ ⊗[ℚ] L₀)]
    [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
    [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
    [TopologicalSpace (ℝ ⊗[ℚ] (∀ i : Option ι, optionLieSpace L₀ L i))]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ i : Option ι, optionLieSpace L₀ L i))]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] (∀ i : Option ι, optionLieSpace L₀ L i))]
    [T2Space (ℝ ⊗[ℚ] (∀ i : Option ι, optionLieSpace L₀ L i))]

theorem optionOriginalObservable_adapted_lipschitz
    (adapted : (optionProduct D₀ D).AdaptedModelData) (ℓ : ℝ≥0) (H : ℕ)
    (hH : ∀ i j, RationalHeightLE ((optionProduct D₀ D).basis.repr (adapted.basis i) j) H)
    (hLip : ∀ a, letI := D₀.metricSpace; LipschitzWith ℓ (observable a)) :
    ∀ a, letI := adapted.model.metricSpace
      LipschitzWith (optionOriginalAdaptedLipschitzBound (L₀ := L₀) (L := L)
        (d₀ := d₀) (d := d) ℓ H)
        (fun y : adapted.model.Space => optionOriginalObservable D₀ D observable a y) := by
  intro a
  let := adapted.model.metricSpace
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have horiginal := optionOriginalObservable_lipschitz D₀ D observable ℓ hLip a
  have hd : dist (optionOriginalObservable D₀ D observable a x)
      (optionOriginalObservable D₀ D observable a y) ≤
      ↑(ℓ * coordinateLipschitzBound d₀
        (Fintype.card (Σ i : Option ι, Fin (optionDimension d₀ d i))) 1) *
        @dist (optionProduct D₀ D).Space (optionProduct D₀ D).metricSpace.toDist x y := by
    let := (optionProduct D₀ D).metricSpace
    exact horiginal.dist_le_mul x y
  have hchange := adapted.original_dist_le H hH x y
  calc
    dist (optionOriginalObservable D₀ D observable a x)
        (optionOriginalObservable D₀ D observable a y) ≤
        ↑(ℓ * coordinateLipschitzBound d₀
          (Fintype.card (Σ i : Option ι, Fin (optionDimension d₀ d i))) 1) *
          @dist (optionProduct D₀ D).Space (optionProduct D₀ D).metricSpace.toDist x y := hd
    _ ≤ ↑(ℓ * coordinateLipschitzBound d₀
          (Fintype.card (Σ i : Option ι, Fin (optionDimension d₀ d i))) 1) *
        (coordinateLipschitzBound
          (Fintype.card (Σ i : Option ι, Fin (optionDimension d₀ d i)))
          (finrank ℚ (∀ i : Option ι, optionLieSpace L₀ L i)) H * dist x y) :=
      mul_le_mul_of_nonneg_left hchange (NNReal.coe_nonneg _)
    _ = _ := by simp only [optionOriginalAdaptedLipschitzBound, NNReal.coe_mul]; ring

theorem optionOriginalObservable_adapted_lipschitz_of_logHeight
    (adapted : (optionProduct D₀ D).AdaptedModelData) (ℓ : ℝ≥0) (height : ℝ)
    (hheight : ∀ i j,
      rationalLogHeight ((optionProduct D₀ D).basis.repr (adapted.basis i) j) ≤ height)
    (hLip : ∀ a, letI := D₀.metricSpace; LipschitzWith ℓ (observable a)) :
    ∀ a, letI := adapted.model.metricSpace
      LipschitzWith (optionOriginalAdaptedLipschitzBound (L₀ := L₀) (L := L)
        (d₀ := d₀) (d := d) ℓ ⌈Real.exp height⌉₊)
        (fun y : adapted.model.Space => optionOriginalObservable D₀ D observable a y) :=
  optionOriginalObservable_adapted_lipschitz D₀ D observable adapted ℓ
    ⌈Real.exp height⌉₊ (fun i j => rationalHeightLE_ceil_exp (hheight i j)) hLip

end Metric

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.LowerRefilteredCyclicExpansion
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct NNReal

theorem exists_uniform_positive_frozen_observable (s k : ℕ) :
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
            ∀ (u : E.Space → ℂ) (ℓ : ℝ≥0), (ℓ : ℝ) ≤ Real.exp p →
              (letI := E.metricSpace; LipschitzWith ℓ u) →
              (∀ x, (u x).im = 0 ∧ 0 ≤ (u x).re ∧ (u x).re ≤ 1) →
              ∃ (v : Q.Space → ℂ) (K : ℝ≥0),
                (K : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ (letI := Q.metricSpace; LipschitzWith K v) ∧
                (∀ x, (v x).im = 0 ∧ 0 ≤ (v x).re ∧ (v x).re ≤ 1) ∧ (∀ x, ‖v x‖ ≤ 1) ∧
                ∀ x : Q.RealGroup, v (QuotientGroup.mk x) = u (QuotientGroup.mk
                  (a * realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
                    (hM := E.filtration.lowerCentralSeries_eq_bot) φ x * r)) := by
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
  intro a r ha hr u ℓ hℓ hu hunit
  have hconj := D.real_conjugationPullback_property E φ q hq Λ htarget r hr
  have ha' : LipschitzWith A (fun x => a * x) := hALip a (fun i =>
    (ha i).trans (Real.exp_le_exp.mpr (pow_le_pow_left₀ (by linarith) (by dsimp [t]; linarith) _)))
  obtain ⟨v, hv, hunitv, hcap, heval⟩ :=
    Q.exists_positive_frozen_observable E φ a r hconj hBLip ha' u hu hunit
  refine ⟨v, ℓ * (A * B), ?_, hv, hunitv, hcap, heval⟩
  calc
    _ = (ℓ : ℝ) * ((A : ℝ) * B) := by simp only [NNReal.coe_mul]
    _ ≤ Real.exp p * (Real.exp ((t + c₁) ^ c₁) * Real.exp ((t + 2) ^ 2)) :=
      mul_le_mul hℓ (mul_le_mul hA hB B.coe_nonneg (Real.exp_pos _).le)
        (mul_nonneg A.coe_nonneg B.coe_nonneg) (Real.exp_pos p).le
    _ = Real.exp (p + (t + c₁) ^ c₁ + (t + 2) ^ 2) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    _ ≤ _ := Real.exp_le_exp.mpr hcostC

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct NNReal

theorem exists_uniform_frozen_reconstruction (s k : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L M N : Type*}
      [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M] [LieRing N] [LieAlgebra ℚ N]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)]
      [TopologicalSpace (ℝ ⊗[ℚ] N)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] N)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] N)] [T2Space (ℝ ⊗[ℚ] N)]
      {d e f : ℕ} (D : RationalFilteredNilmanifold L s d) (E : RationalFilteredNilmanifold M s e)
      (T : RationalFilteredNilmanifold N s f) (φ : L →ₗ⁅ℚ⁆ M) (ψ : L →ₗ⁅ℚ⁆ N) (p : ℝ),
      0 ≤ p → D.GeometryComplexityLE p → E.GeometryComplexityLE p → T.GeometryComplexityLE p →
      (∀ i j, rationalLogHeight (E.basis.repr (φ (D.basis j)) i) ≤ p) →
      (∀ i j, rationalLogHeight (T.basis.repr (ψ (D.basis j)) i) ≤ p) →
      ∀ q : ℕ, 0 < q → (q : ℝ) ≤ Real.exp p →
      ∃ Λ : Subgroup T.filtration.Group, Λ ≤ T.lattice ∧
        (Λ.subgroupOf T.lattice).Characteristic ∧ (Λ.subgroupOf T.lattice).Normal ∧
        (Λ.subgroupOf T.lattice).FiniteIndex ∧ (Λ.relIndex T.lattice : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∃ (B : ℕ) (hB : 0 < B)
          (hin : scaledIntegerGrid B ⊆ bchSubgroupCoordinates T.basis Λ)
          (hout : bchSubgroupCoordinates T.basis Λ ⊆ denominatorGrid B),
          let V := T.withLattice Λ B hB hin hout
          V.GeometryComplexityLE ((p + C) ^ C) ∧
          ∀ a r : E.RealGroup,
            (∀ i, |(E.basis.baseChange ℝ).repr a.coord i| ≤ Real.exp ((p + 2) ^ k)) →
            (E.basis.baseChange ℝ).equivFun r.coord ∈ realDenominatorGrid q →
            ∀ (u : E.Space → ℂ) (ℓ : ℝ≥0), (ℓ : ℝ) ≤ Real.exp p →
              (letI := E.metricSpace; LipschitzWith ℓ u) →
              (∀ x, (u x).im = 0 ∧ 0 ≤ (u x).re ∧ (u x).re ≤ 1) →
              (∀ z ∈ (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
                  (hM := T.filtration.lowerCentralSeries_eq_bot) ψ).ker, ∀ x : D.RealGroup,
                u (QuotientGroup.mk (a * realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
                  (hM := E.filtration.lowerCentralSeries_eq_bot) φ (z * x) * r)) =
                u (QuotientGroup.mk (a * realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
                  (hM := E.filtration.lowerCentralSeries_eq_bot) φ x * r))) →
              ∃ (v : V.Space → ℂ) (K : ℝ≥0),
                (K : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ (letI := V.metricSpace; LipschitzWith K v) ∧
                (∀ x, (v x).im = 0 ∧ 0 ≤ (v x).re ∧ (v x).re ≤ 1) ∧ (∀ x, ‖v x‖ ≤ 1) ∧
                ∀ x : D.RealGroup,
                  v (QuotientGroup.mk (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
                    (hM := T.filtration.lowerCentralSeries_eq_bot) ψ x)) =
                  u (QuotientGroup.mk (a * realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
                    (hM := E.filtration.lowerCentralSeries_eq_bot) φ x * r)) := by
  obtain ⟨a₀, _, hfreeze⟩ := exists_uniform_positive_frozen_observable s k
  obtain ⟨b₀, _, hrec⟩ := exists_uniform_native_positive_reconstruction s
  let X : Polynomial ℕ := Polynomial.X
  let R := X + (X + Polynomial.C a₀) ^ a₀
  let P := R + (R + Polynomial.C b₀) ^ b₀
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro L M N _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ d e f D E T φ ψ p hp hD hE hT hφ hψ q hq hqp
  obtain ⟨Γ, _, _, _, _, _, A, hA, hAin, hAout, hQ, hfrozen⟩ :=
    hfreeze D E φ p hp hD hE hφ q hq hqp
  let Q := D.withLattice Γ A hA hAin hAout
  let t := p + (p + a₀) ^ a₀
  have hpt : p ≤ t := le_add_of_nonneg_right (pow_nonneg (add_nonneg hp (Nat.cast_nonneg a₀)) _)
  have ht : 0 ≤ t := hp.trans hpt
  have hQt : (p + a₀) ^ a₀ ≤ t := le_add_of_nonneg_left hp
  have hsum : t + (t + b₀) ^ b₀ ≤ (p + C) ^ C := by
    simpa [P, R, X, t, Polynomial.eval₂_pow] using hbudget p hp
  have hcost : (t + b₀) ^ b₀ ≤ (p + C) ^ C := (le_add_of_nonneg_left ht).trans hsum
  obtain ⟨Λ, hΛ, hchar, hnormal, hfinite, hindex, B, hB, hBin, hBout, hV, hreconstruct⟩ :=
    hrec Q T ψ ht (hQ.mono Q hQt) (hT.mono T hpt) (fun i j => (hψ i j).trans hpt)
  refine ⟨Λ, hΛ, hchar, hnormal, hfinite, hindex.trans (Real.exp_le_exp.mpr hcost),
    B, hB, hBin, hBout, hV.mono _ hcost, ?_⟩
  intro a r ha hr u ℓ hℓ hu hunit hkernel
  obtain ⟨w, K₀, hK₀, hw, hunitw, _, hevalw⟩ := hfrozen a r ha hr u ℓ hℓ hu hunit
  have hker : ∀ z ∈ (realificationMap (hnil := Q.filtration.lowerCentralSeries_eq_bot)
      (hM := T.filtration.lowerCentralSeries_eq_bot) ψ).ker, ∀ x,
      w (QuotientGroup.mk (z * x)) = w (QuotientGroup.mk x) := by
    intro z hz x
    rw [hevalw, hevalw]
    exact hkernel z hz x
  obtain ⟨v, K, hK, hv, hunitv, hcap, hevalv⟩ := hreconstruct w K₀
    (hK₀.trans (Real.exp_le_exp.mpr hQt)) hw hunitw hker
  exact ⟨v, K, hK.trans (Real.exp_le_exp.mpr hcost), hv, hunitv, hcap,
    fun x => (hevalv x).trans (hevalw x)⟩

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.UniformFiniteMarkedPolynomialFreezing
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold
open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal

def FiniteMarkedPolynomialFreezing
    {σ κ L T : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
    [LieRing T] [LieAlgebra ℚ T]
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {s d t : ℕ} (D : RationalFilteredNilmanifold L s d)
    (F : NilpotentLieFiltration T t) (c : Basis κ ℚ T) (φ : L →ₗ⁅ℚ⁆ T)
    (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ F.layer j)
    (w : σ → ℕ) (S : T →ₗ[ℚ] L)
    (hS : ∀ j, ∀ y ∈ F.layer j, S y ∈ D.filtration.layer j)
    (l : ℕ) (Tbox : σ → ℝ) (A ε B : ℝ) : Prop :=
  ∃ N Q M m n : ℕ, 0 < N ∧ 0 < Q ∧ 0 < M ∧ 0 < m ∧ 0 < n ∧
    (Fintype.card (Fin d → Fin (N + 1)) : ℝ) ≤ B ∧
    (Fintype.card (σ → Fin (Q + 1)) : ℝ) ≤ B ∧
    (M : ℝ) ≤ B ∧ (m : ℝ) ≤ B ∧ (n : ℝ) ≤ B ∧
    (Fintype.card ((Fin d → Fin (N + 1)) × Fin n) : ℝ) ≤ B ^ 2 ∧
    ∃ (left : (Fin d → Fin (N + 1)) → D.RealGroup) (right : Fin n → D.RealGroup),
      (∀ j, realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
          (hM := F.lowerCentralSeries_eq_bot) φ (left j) = 1 ∧
        ∀ i, |(D.basis.baseChange ℝ).repr (left j).coord i| ≤ B) ∧
      (∀ j, realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
          (hM := F.lowerCentralSeries_eq_bot) φ (right j) = 1 ∧
        (∀ i, |(D.basis.baseChange ℝ).repr (right j).coord i| ≤ B) ∧
        (D.basis.baseChange ℝ).equivFun (right j).coord ∈ realDenominatorGrid m) ∧
      ∀ (E : (D.filtration.realification.adaptedPolynomialFiltration w).Group)
        (EF : (F.realification.adaptedPolynomialFiltration w).Group)
        (R : (D.filtration.realification.adaptedPolynomialFiltration w).Group)
        (RF : (F.realification.adaptedPolynomialFiltration w).Group),
        D.filtration.PolynomialSlowBound D.basis w Tbox A E →
        F.PolynomialSlowBound c w Tbox A EF →
        D.filtration.PolynomialRationalGrid D.basis w l R →
        F.PolynomialRationalGrid c w l RF →
        D.filtration.realPolynomialGroupMap F φ hφ w E = EF →
        D.filtration.realPolynomialGroupMap F φ hφ w R = RF →
        ∃ (leftLabel : (σ → Fin (Q + 1)) → (Fin d → Fin (N + 1)))
          (rightLabel : (σ → ZMod M) → Fin n),
          (∀ i j,
            D.filtration.realPolynomialGroupMap F φ hφ w
              (D.filtration.frozenMarkedLeft F w S hS EF (left i)) = EF ∧
            D.filtration.realPolynomialGroupMap F φ hφ w
              (D.filtration.frozenMarkedRight F w S hS RF (right j)) = RF) ∧
          ∀ (test : D.Niltest w)
            (g P : (D.filtration.realification.adaptedPolynomialFiltration w).Group),
            E * P * R = g →
            ∀ j (x : σ → ℤ), (∀ i, |(x i : ℝ)| ≤ Tbox i) →
              (∀ i, |(x i : ℝ) - normalizedRealBoxGrid Tbox Q j i| ≤ Tbox i * (2 / Q)) →
              ‖test.observable (QuotientGroup.mk
                  (D.filtration.adaptedPolynomialRealValueHom w (fun i => (x i : ℝ)) g)) -
                test.observable (QuotientGroup.mk
                  (D.filtration.adaptedPolynomialRealValueHom w (fun i => (x i : ℝ))
                    (D.filtration.frozenMarkedLeft F w S hS EF (left (leftLabel j)) * P *
                      D.filtration.frozenMarkedRight F w S hS RF
                        (right (rightLabel (fun i => (x i : ZMod M)))))))‖ ≤
                (test.lipBound : ℝ) * ε

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FiniteMarkedFreezingCellBound
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold
open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal

def BoundedCellMarkedPolynomialFreezing
    {σ κ L T : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
    [LieRing T] [LieAlgebra ℚ T]
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {s d t : ℕ} (D : RationalFilteredNilmanifold L s d)
    (F : NilpotentLieFiltration T t) (c : Basis κ ℚ T) (φ : L →ₗ⁅ℚ⁆ T)
    (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ F.layer j)
    (w : σ → ℕ) (S : T →ₗ[ℚ] L)
    (hS : ∀ j, ∀ y ∈ F.layer j, S y ∈ D.filtration.layer j)
    (l : ℕ) (Tbox : σ → ℝ) (A ε B : ℝ) : Prop :=
  ∃ N Q M m n : ℕ, 0 < N ∧ 0 < Q ∧ (Q : ℝ) ≤ max 1 B ∧ 0 < M ∧ 0 < m ∧ 0 < n ∧
    (Fintype.card (Fin d → Fin (N + 1)) : ℝ) ≤ B ∧
    (Fintype.card (σ → Fin (Q + 1)) : ℝ) ≤ B ∧
    (M : ℝ) ≤ B ∧ (m : ℝ) ≤ B ∧ (n : ℝ) ≤ B ∧
    (Fintype.card ((Fin d → Fin (N + 1)) × Fin n) : ℝ) ≤ B ^ 2 ∧
    ∃ (left : (Fin d → Fin (N + 1)) → D.RealGroup) (right : Fin n → D.RealGroup),
      (∀ j, realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
          (hM := F.lowerCentralSeries_eq_bot) φ (left j) = 1 ∧
        ∀ i, |(D.basis.baseChange ℝ).repr (left j).coord i| ≤ B) ∧
      (∀ j, realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
          (hM := F.lowerCentralSeries_eq_bot) φ (right j) = 1 ∧
        (∀ i, |(D.basis.baseChange ℝ).repr (right j).coord i| ≤ B) ∧
        (D.basis.baseChange ℝ).equivFun (right j).coord ∈ realDenominatorGrid m) ∧
      ∀ (E : (D.filtration.realification.adaptedPolynomialFiltration w).Group)
        (EF : (F.realification.adaptedPolynomialFiltration w).Group)
        (R : (D.filtration.realification.adaptedPolynomialFiltration w).Group)
        (RF : (F.realification.adaptedPolynomialFiltration w).Group),
        D.filtration.PolynomialSlowBound D.basis w Tbox A E →
        F.PolynomialSlowBound c w Tbox A EF →
        D.filtration.PolynomialRationalGrid D.basis w l R →
        F.PolynomialRationalGrid c w l RF →
        D.filtration.realPolynomialGroupMap F φ hφ w E = EF →
        D.filtration.realPolynomialGroupMap F φ hφ w R = RF →
        ∃ (leftLabel : (σ → Fin (Q + 1)) → (Fin d → Fin (N + 1)))
          (rightLabel : (σ → ZMod M) → Fin n),
          (∀ i j,
            D.filtration.realPolynomialGroupMap F φ hφ w
              (D.filtration.frozenMarkedLeft F w S hS EF (left i)) = EF ∧
            D.filtration.realPolynomialGroupMap F φ hφ w
              (D.filtration.frozenMarkedRight F w S hS RF (right j)) = RF) ∧
          ∀ (test : D.Niltest w)
            (g P : (D.filtration.realification.adaptedPolynomialFiltration w).Group),
            E * P * R = g →
            ∀ j (x : σ → ℤ), (∀ i, |(x i : ℝ)| ≤ Tbox i) →
              (∀ i, |(x i : ℝ) - normalizedRealBoxGrid Tbox Q j i| ≤ Tbox i * (2 / Q)) →
              ‖test.observable (QuotientGroup.mk
                  (D.filtration.adaptedPolynomialRealValueHom w (fun i => (x i : ℝ)) g)) -
                test.observable (QuotientGroup.mk
                  (D.filtration.adaptedPolynomialRealValueHom w (fun i => (x i : ℝ))
                    (D.filtration.frozenMarkedLeft F w S hS EF (left (leftLabel j)) * P *
                      D.filtration.frozenMarkedRight F w S hS RF
                        (right (rightLabel (fun i => (x i : ZMod M)))))))‖ ≤
                (test.lipBound : ℝ) * ε

theorem FiniteMarkedPolynomialFreezing.bounded_cells
    {σ κ L T : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
    [LieRing T] [LieAlgebra ℚ T]
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {s d t : ℕ} {D : RationalFilteredNilmanifold L s d}
    {F : NilpotentLieFiltration T t} {c : Basis κ ℚ T} {φ : L →ₗ⁅ℚ⁆ T}
    {hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ F.layer j}
    {w : σ → ℕ} {S : T →ₗ[ℚ] L}
    {hS : ∀ j, ∀ y ∈ F.layer j, S y ∈ D.filtration.layer j}
    {l : ℕ} {Tbox : σ → ℝ} {A ε B : ℝ}
    (h : D.FiniteMarkedPolynomialFreezing F c φ hφ w S hS l Tbox A ε B) :
    D.BoundedCellMarkedPolynomialFreezing F c φ hφ w S hS l Tbox A ε B := by
  obtain ⟨N, Q, M, m, n, hN, hQ, hM, hm, hn, hNc, hQc, hMb, hmb, hnb, hpair,
    left, right, hl, hr, hfreeze⟩ := h
  cases isEmpty_or_nonempty σ with
  | inr hne =>
    let : Nonempty σ := hne
    have hQb : (Q : ℝ) ≤ max 1 B := by
      have hQc' : ((Q + 1 : ℕ) : ℝ) ≤ B :=
        (Nat.cast_le.mpr (subdivisionCount_le_function_card (σ := σ) Q)).trans hQc
      exact (show (Q : ℝ) ≤ B by push_cast at hQc'; linarith).trans (le_max_right _ _)
    exact ⟨N, Q, M, m, n, hN, hQ, hQb, hM, hm, hn, hNc, hQc, hMb, hmb, hnb,
      hpair, left, right, hl, hr, hfreeze⟩
  | inl hempty =>
    let : IsEmpty σ := hempty
    have hone : (1 : ℝ) ≤ B :=
      (show (1 : ℝ) ≤ n by exact_mod_cast hn).trans hnb
    have hcard : (Fintype.card (σ → Fin (1 + 1)) : ℝ) ≤ B := by simpa using hone
    refine ⟨N, 1, M, m, n, hN, by omega, ?_, hM, hm, hn, hNc, hcard, hMb, hmb,
      hnb, hpair, left, right, hl, hr, ?_⟩
    · simpa only [Nat.cast_one] using le_max_left (1 : ℝ) B
    · intro E EF R RF hE hEF hR hRF hEproj hRproj
      obtain ⟨leftLabel, rightLabel, hmarks, herror⟩ := hfreeze E EF R RF
        hE hEF hR hRF hEproj hRproj
      let emptyCell : σ → Fin (Q + 1) := fun i => isEmptyElim i
      refine ⟨fun _ => leftLabel emptyCell, rightLabel, hmarks, ?_⟩
      intro test g P hfac j x hx hj
      exact herror test g P hfac emptyCell x hx (fun i => isEmptyElim i)

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PrescribedPartitionExpansionCore
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieFiltration
open scoped TensorProduct BigOperators

attribute [local instance_reducible] optionLieSpace

def PreparedHigherShiftContradictionSpec (s r b₀ k₀ k Dexp : ℕ) (epsilon : ℝ) : Prop :=
    ∀ {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
      {L : ι → Type} [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {d m : ι → ℕ}
      [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
      [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
      {K : κ → Type} [∀ j, LieRing (K j)] [∀ j, LieAlgebra ℚ (K j)] {e : κ → ℕ}
      [∀ j, TopologicalSpace (ℝ ⊗[ℚ] K j)] [∀ j, IsTopologicalAddGroup (ℝ ⊗[ℚ] K j)]
      [∀ j, ContinuousSMul ℝ (ℝ ⊗[ℚ] K j)] [∀ j, T2Space (ℝ ⊗[ℚ] K j)]
      (D : ∀ i, RationalFilteredNilmanifold (L i) ((s + 1) + 1) (d i))
      [∀ i, TopologicalSpace (ℝ ⊗[ℚ] (D i).filtration.squareLieSubalgebra)]
      [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] (D i).filtration.squareLieSubalgebra)]
      [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] (D i).filtration.squareLieSubalgebra)]
      [∀ i, T2Space (ℝ ⊗[ℚ] (D i).filtration.squareLieSubalgebra)]
      [∀ i, TopologicalSpace (ℝ ⊗[ℚ] ((D i).filtration.squareLieSubalgebra ⧸
        (D i).filtration.squareFiltration.layerIdeal ((s + 1) + 1)))]
      [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] ((D i).filtration.squareLieSubalgebra ⧸
        (D i).filtration.squareFiltration.layerIdeal ((s + 1) + 1)))]
      [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] ((D i).filtration.squareLieSubalgebra ⧸
        (D i).filtration.squareFiltration.layerIdeal ((s + 1) + 1)))]
      [∀ i, T2Space (ℝ ⊗[ℚ] ((D i).filtration.squareLieSubalgebra ⧸
        (D i).filtration.squareFiltration.layerIdeal ((s + 1) + 1)))]
      (b : ∀ i, Basis (Fin (m i)) ℚ (L i)) (v : ∀ i, Fin (m i) → ℕ)
      (hF : ∀ i j, (D i).filtration.layer j = Submodule.span ℚ (b i '' {k | j ≤ v i k}))
      (M : ι → ℕ) (hM : ∀ i, 0 < M i)
      (hin : ∀ i, scaledIntegerGrid (M i) ⊆ bchSubgroupCoordinates
        ((D i).filtration.squareFinBasis (b i) (v i) (hF i 2)) ((D i).filtration.squareLattice (D i).lattice))
      (hout : ∀ i, bchSubgroupCoordinates ((D i).filtration.squareFinBasis (b i) (v i) (hF i 2))
        ((D i).filtration.squareLattice (D i).lattice) ⊆ denominatorGrid (M i)),
      let V := fun i => (D i).filtration.squareFiltration.ofAdaptedBasis
        ((D i).filtration.squareFinBasis (b i) (v i) (hF i 2)) (squareFinWeight (v i))
        ((D i).filtration.squareFinBasis_layers (b i) (v i) (hF i))
        ((D i).filtration.squareLattice (D i).lattice) (M i) (hM i) (hin i) (hout i)
      let Q := fun i => (D i).filtration.squareFiltration.topQuotientModel
        ((D i).filtration.squareFinBasis (b i) (v i) (hF i 2)) (squareFinWeight (v i))
        ((D i).filtration.squareFinBasis_layers (b i) (v i) (hF i))
        ((D i).filtration.squareLattice (D i).lattice) (M i) (hM i) (hin i) (hout i)
      ∀ E : ∀ j, RationalFilteredNilmanifold (K j) (s + 1) (e j),
      let Z := sumFactors E Q
      ∀ {L₀ : Type} [LieRing L₀] [LieAlgebra ℚ L₀] {d₀ : ℕ}
        (D₀ : RationalFilteredNilmanifold L₀ (s + 1) d₀),
      let T := optionFactors D₀ Z
      ∀ (W : LieSubalgebra ℚ (pi T).filtration.AssociatedGraded) {dR dQ : ℕ}
        (R : RationalFilteredNilmanifold ((pi T).filtration.gradedRefiltrationSubalgebra W) (s + 1) dR)
        (Q₀ : RationalFilteredNilmanifold
          (((pi T).filtration.gradedRefiltrationSubalgebra W) ⧸ R.filtration.layerIdeal (s + 1)) s dQ)
        [TopologicalSpace (ℝ ⊗[ℚ] L₀)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L₀)]
        [ContinuousSMul ℝ (ℝ ⊗[ℚ] L₀)] [T2Space (ℝ ⊗[ℚ] L₀)] {p cost : ℝ} (q : ℕ),
      2 ≤ p → (Fintype.card ι : ℝ) ≤ p → (Fintype.card κ : ℝ) ≤ p →
      (∀ i, (D i).GeometryComplexityLE p) → (∀ i, (V i).GeometryComplexityLE p) →
      (∀ i j k, rationalLogHeight ((D i).basis.repr (b i j) k) ≤ p) →
      (∀ j, (E j).GeometryComplexityLE p) → 0 ≤ cost → cost ≤ (p + b₀) ^ b₀ →
      RefilteredProductExpansionSpec T none W R Q₀ p q r cost →
        ∀ (g : ∀ j, (E j).filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
          (g₀ : ∀ i, (D i).filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
          (c : ι → ℤ) (N : ℕ) [NeZero N],
        Odd N → Real.exp ((p + 2) ^ Dexp) ≤ N →
        ∀ (f₁ f₂ weight : ZMod N → ℝ) (sigma delta : ℝ),
          Real.exp (-((p + 2) ^ k)) ≤ sigma → Real.exp (-((p + 2) ^ k)) ≤ delta →
          (∀ n, 0 ≤ f₁ n ∧ f₁ n ≤ Real.exp p) →
          (∀ n, 0 ≤ f₂ n ∧ f₂ n ≤ Real.exp p) →
          (∀ n, 0 ≤ weight n ∧ weight n ≤ Real.exp p) →
            ∀ {J₀ : Type} (freq : J₀ → ∀ i, optionLieSpace L₀
              (sumLieSpace K (fun i => (D i).filtration.squareLieSubalgebra ⧸
                (D i).filtration.squareFiltration.layerIdeal (s + 1 + 1))) i →ₗ[ℚ] ℚ),
              (∀ j x, x ∈ (pi T).filtration.realGradedRefiltrationLayer W (s + 1) →
                realifyFunctional (piFrequency (freq j)) x = 0) →
              ∀ (S : ZMod N → (T none).Niltest (fun _ : Unit => 1)),
                (∀ h, (S h).ComplexityLE p) → (∀ h, (S h).UnitIntervalValued) →
                (∀ h z, z ∈ (T none).filtration.realification.subgroup (s + 1) →
                  (∀ j, realifyFunctional (freq j none) z.coord = 0) →
                  ∀ x, (S h).observable (z • x) = (S h).observable x) →
                ∀ (Hsh : Finset (ZMod N))
                  (gT : ZMod N → ∀ i, (T i).filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
                  (branch : ZMod N → ι → Fin 2) (η γ : ZMod N → ∀ i, (D i).RealGroup)
                  (rSq : ZMod N → ∀ i, (D i).filtration.squareFiltration.realification.PolynomialOrbit (fun _ : Unit => 1))
                  (qSq : ZMod N → ∀ i, (Q i).filtration.realification.PolynomialOrbit (fun _ : Unit => 1)),
                  (∀ h ∈ Hsh, gT h none = (S h).orbit) →
                  (∀ h ∈ Hsh, ∀ i, gT h (some i) = sumOrbits E Q g (qSq h) i) →
                  (∀ h ∈ Hsh, ∀ i, γ h i ∈ (D i).realLattice) →
                  (∀ h ∈ Hsh, ∀ i j, |((D i).basis.baseChange ℝ).repr (η h i).coord j| ≤
                    Real.exp ((p + 2) ^ k₀)) →
                  (∀ h ∈ Hsh, ∀ i (z : Unit → ℤ),
                    (D i).filtration.realSquareFstHom
                      ((D i).filtration.squareFiltration.realification.polynomialOrbitEval
                        (fun _ : Unit => 1) z (rSq h i)) =
                        (η h i)⁻¹ * (D i).filtration.realification.polynomialOrbitEval (fun _ : Unit => 1)
                          (z + fun _ => (h.val : ℤ) - ((branch h i).val : ℤ) * N) (g₀ i) * (γ h i)⁻¹ ∧
                    (D i).filtration.realSquareSndHom
                      ((D i).filtration.squareFiltration.realification.polynomialOrbitEval
                        (fun _ : Unit => 1) z (rSq h i)) =
                        (D i).filtration.realification.polynomialOrbitEval (fun _ : Unit => 1)
                          (z + fun _ => c i) (g₀ i)) →
                  (∀ h ∈ Hsh, ∀ i, qSq h i = (D i).filtration.squareFiltration.realQuotientPolynomialOrbit
                    ((D i).filtration.squareFiltration.layerIdeal (s + 1 + 1)) (t := s + 1) le_rfl (rSq h i)) →
                  ∀ (slow middle rat : ZMod N →
                      ((pi T).filtration.realification.adaptedPolynomialFiltration (fun _ : Unit => 1)).Group)
                    (δ : ZMod N → (pi T).RealGroup),
                    (∀ h ∈ Hsh, δ h ∈ (pi T).realLattice) →
                    (∀ h ∈ Hsh, slow h * middle h * rat h *
                      (pi T).filtration.realification.adaptedConstantGroupHom (fun _ : Unit => 1) (δ h) =
                        ⟨⟨(piRealOrbit (fun i => (T i).filtration) (gT h)).log,
                          (piRealOrbit (fun i => (T i).filtration) (gT h)).property⟩⟩) →
                    (∀ h ∈ Hsh, (pi T).filtration.PolynomialSlowBound (pi T).basis (fun _ : Unit => 1)
                      (fun _ => (N : ℝ)) (Real.exp ((p + 2) ^ r)) (slow h)) →
                    (∀ h ∈ Hsh, (pi T).filtration.PolynomialRationalGrid (pi T).basis (fun _ : Unit => 1) q (rat h)) →
                    (∀ h ∈ Hsh, ∀ α, VectorPolynomial.coefficients
                      ((middle h).coord : VectorPolynomial Unit ℚ (ℝ ⊗[ℚ] (∀ i,
                        optionLieSpace L₀ (sumLieSpace K (fun i => (D i).filtration.squareLieSubalgebra ⧸
                          (D i).filtration.squareFiltration.layerIdeal (s + 1 + 1))) i))) α ∈
                        (pi T).filtration.realGradedRefiltrationLayer W (Finsupp.weight (fun _ : Unit => 1) α)) →
                    (∀ h ∈ Hsh, VectorPolynomial.coefficients
                      ((middle h).coord : VectorPolynomial Unit ℚ (ℝ ⊗[ℚ] (∀ i,
                        optionLieSpace L₀ (sumLieSpace K (fun i => (D i).filtration.squareLieSubalgebra ⧸
                          (D i).filtration.squareFiltration.layerIdeal (s + 1 + 1))) i))) 0 = 0) →
                    sigma * N ≤ (Hsh.card : ℝ) →
                    CyclicNiltestUpperComparison.{0} (s + 2) N ((p + 2) ^ Dexp)
                      (Real.exp (-((p + 2) ^ Dexp))) f₁ f₂ →
                    (∀ h ∈ Hsh, delta < 𝔼 n,
                      (f₁ n - (1 + epsilon) * f₂ n) * weight (n + h) *
                        ((S h).evalCyclic N (fun _ => n)).re) → False

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeDetectorContradictionSpec
namespace OAI

section

namespace Erdos3.PositiveShiftBasis

open Module NilpotentLieFiltration CircleFourier
open scoped TensorProduct BigOperators

attribute [local instance] PositiveShiftBasis.lie PositiveShiftBasis.algebra
  PositiveShiftBasis.topology PositiveShiftBasis.topologicalAdd
  PositiveShiftBasis.continuousSMul PositiveShiftBasis.hausdorff

def NativePartnerContradictionSpec (s C : ℕ) (epsilon : ℝ) : Prop :=
    ∀ {N : ℕ} [NeZero N] {q : ℝ} {f₁ f₂ weight : ZMod N → ℝ}
      (B : PositiveShiftBasis.{0} (s + 1) N q (fun n => f₁ n - (1 + epsilon) * f₂ n) weight) (w : Fin B.dim → ℕ),
      (∀ k, B.model.filtration.layer k = Submodule.span ℚ (B.model.basis '' {i | k ≤ w i})) →
      ∀ {L : (Fin B.count × Bool) → Type}
        [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {d : (Fin B.count × Bool) → ℕ}
        [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
        [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
        (D : ∀ i, RationalFilteredNilmanifold (L i) (s + 1 + 1) (d i))
        [∀ i, TopologicalSpace (ℝ ⊗[ℚ] (D i).filtration.squareLieSubalgebra)]
        [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] (D i).filtration.squareLieSubalgebra)]
        [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] (D i).filtration.squareLieSubalgebra)]
        [∀ i, T2Space (ℝ ⊗[ℚ] (D i).filtration.squareLieSubalgebra)]
        [∀ i, TopologicalSpace (ℝ ⊗[ℚ] ((D i).filtration.squareLieSubalgebra ⧸
          (D i).filtration.squareFiltration.layerIdeal (s + 1 + 1)))]
        [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] ((D i).filtration.squareLieSubalgebra ⧸
          (D i).filtration.squareFiltration.layerIdeal (s + 1 + 1)))]
        [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] ((D i).filtration.squareLieSubalgebra ⧸
          (D i).filtration.squareFiltration.layerIdeal (s + 1 + 1)))]
        [∀ i, T2Space (ℝ ⊗[ℚ] ((D i).filtration.squareLieSubalgebra ⧸
          (D i).filtration.squareFiltration.layerIdeal (s + 1 + 1)))]
        (T : ∀ i, (D i).Niltest (fun _ : Unit => 1)) (H : Finset (ZMod N)),
      H ⊆ B.shifts → ∀ {p : ℝ}, 2 ≤ p → q ≤ p → Real.exp (-p) * N ≤ (H.card : ℝ) →
      (∀ i, (T i).ComplexityLE p) → (∀ i, (T i).normBound ≤ 1) →
      ∀ χ : ∀ i, (D i).RealGroup → CircleFourier.Circle,
      (∀ i z, z ∈ (D i).filtration.realification.subgroup (s + 1 + 1) → ∀ x,
        (T i).observable (z • x) = character (χ i z) * (T i).observable x) →
      (∀ h ∈ H, ∀ j, Real.exp (-p) ≤ ‖𝔼 n,
        (B.mode h j).evalCyclic N (fun _ => n) * (T (j, true)).evalCyclic N (fun _ => n) *
          (T (j, false)).evalCyclic N (fun _ => n + h)‖) →
      Odd N → Real.exp ((p + C) ^ C) ≤ N →
      (∀ n, 0 ≤ f₁ n ∧ f₁ n ≤ Real.exp p) →
      (∀ n, 0 ≤ f₂ n ∧ f₂ n ≤ Real.exp p) →
      (∀ n, 0 ≤ weight n ∧ weight n ≤ Real.exp p) →
      CyclicNiltestUpperComparison.{0} (s + 2) N ((p + C) ^ C)
        (Real.exp (-((p + C) ^ C))) f₁ f₂ → False

end Erdos3.PositiveShiftBasis

end

section

namespace Erdos3.PositiveShiftBasis

open Module NilpotentLieFiltration CircleFourier
open scoped TensorProduct BigOperators

attribute [local instance] PositiveShiftBasis.lie PositiveShiftBasis.algebra
  PositiveShiftBasis.topology PositiveShiftBasis.topologicalAdd
  PositiveShiftBasis.continuousSMul PositiveShiftBasis.hausdorff

def NativePartnerPairContradictionSpec (s C : ℕ) (epsilon : ℝ) : Prop :=
    ∀ {N : ℕ} [NeZero N] {q : ℝ} {f₁ f₂ weight : ZMod N → ℝ}
      (B : PositiveShiftBasis.{0} (s + 1) N q (fun n => f₁ n - (1 + epsilon) * f₂ n) weight)
      (w : Fin B.dim → ℕ),
      (∀ k, B.model.filtration.layer k = Submodule.span ℚ (B.model.basis '' {i | k ≤ w i})) →
      ∀ {L M : Fin B.count → Type}
        [∀ j, LieRing (L j)] [∀ j, LieAlgebra ℚ (L j)]
        [∀ j, LieRing (M j)] [∀ j, LieAlgebra ℚ (M j)] {d e : Fin B.count → ℕ}
        [∀ j, TopologicalSpace (ℝ ⊗[ℚ] L j)] [∀ j, IsTopologicalAddGroup (ℝ ⊗[ℚ] L j)]
        [∀ j, ContinuousSMul ℝ (ℝ ⊗[ℚ] L j)] [∀ j, T2Space (ℝ ⊗[ℚ] L j)]
        [∀ j, TopologicalSpace (ℝ ⊗[ℚ] M j)] [∀ j, IsTopologicalAddGroup (ℝ ⊗[ℚ] M j)]
        [∀ j, ContinuousSMul ℝ (ℝ ⊗[ℚ] M j)] [∀ j, T2Space (ℝ ⊗[ℚ] M j)]
        (D : ∀ j, RationalFilteredNilmanifold (L j) (s + 1 + 1) (d j))
        (E : ∀ j, RationalFilteredNilmanifold (M j) (s + 1 + 1) (e j))
        (V : ∀ j, (D j).Niltest (fun _ : Unit => 1))
        (W : ∀ j, (E j).Niltest (fun _ : Unit => 1)) (H : Finset (ZMod N)),
      H ⊆ B.shifts → ∀ {p : ℝ}, 2 ≤ p → q ≤ p → Real.exp (-p) * N ≤ (H.card : ℝ) →
      (∀ j, (V j).ComplexityLE p) → (∀ j, (W j).ComplexityLE p) →
      (∀ j, (V j).normBound ≤ 1) → (∀ j, (W j).normBound ≤ 1) →
      ∀ (χ : ∀ j, (D j).RealGroup → CircleFourier.Circle)
        (χ' : ∀ j, (E j).RealGroup → CircleFourier.Circle),
      (∀ j z, z ∈ (D j).filtration.realification.subgroup (s + 1 + 1) → ∀ x,
        (V j).observable (z • x) = character (χ j z) * (V j).observable x) →
      (∀ j z, z ∈ (E j).filtration.realification.subgroup (s + 1 + 1) → ∀ x,
        (W j).observable (z • x) = character (χ' j z) * (W j).observable x) →
      (∀ h ∈ H, ∀ j, Real.exp (-p) ≤ ‖𝔼 n,
        (B.mode h j).evalCyclic N (fun _ => n) * (V j).evalCyclic N (fun _ => n) *
          (W j).evalCyclic N (fun _ => n + h)‖) →
      Odd N → Real.exp ((p + C) ^ C) ≤ N →
      (∀ n, 0 ≤ f₁ n ∧ f₁ n ≤ Real.exp p) →
      (∀ n, 0 ≤ f₂ n ∧ f₂ n ≤ Real.exp p) →
      (∀ n, 0 ≤ weight n ∧ weight n ≤ Real.exp p) →
      CyclicNiltestUpperComparison.{0} (s + 2) N ((p + C) ^ C)
        (Real.exp (-((p + C) ^ C))) f₁ f₂ → False

end Erdos3.PositiveShiftBasis

end

section

namespace Erdos3.PositiveShiftBasis

open Module
open scoped TensorProduct BigOperators

attribute [local instance] PositiveShiftBasis.lie PositiveShiftBasis.algebra
  PositiveShiftBasis.topology PositiveShiftBasis.topologicalAdd
  PositiveShiftBasis.continuousSMul PositiveShiftBasis.hausdorff

def TwoSiteModelContradictionSpec (s C : ℕ) (epsilon : ℝ) : Prop :=
    ∀ {N : ℕ} [NeZero N] {q : ℝ} {f₁ f₂ weight : ZMod N → ℝ}
      (B : PositiveShiftBasis.{0} (s + 1) N q (fun n => f₁ n - (1 + epsilon) * f₂ n) weight)
      (w : Fin B.dim → ℕ),
      (∀ k, B.model.filtration.layer k = Submodule.span ℚ (B.model.basis '' {i | k ≤ w i})) →
      ∀ {I : Type} {K : I → Type} [Fintype I] [∀ i, Fintype (K i)]
        {L : I → Type} {M : ∀ i, K i → Type}
        [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)]
        [∀ i k, LieRing (M i k)] [∀ i k, LieAlgebra ℚ (M i k)]
        [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
        [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
        [∀ i k, TopologicalSpace (ℝ ⊗[ℚ] M i k)] [∀ i k, IsTopologicalAddGroup (ℝ ⊗[ℚ] M i k)]
        [∀ i k, ContinuousSMul ℝ (ℝ ⊗[ℚ] M i k)] [∀ i k, T2Space (ℝ ⊗[ℚ] M i k)]
        {d : I → ℕ} {e : ∀ i, K i → ℕ}
        (D : ∀ i, RationalFilteredNilmanifold (L i) (s + 1 + 1) (d i))
        (E : ∀ i k, RationalFilteredNilmanifold (M i k) (s + 1 + 1) (e i k))
        (Q : ∀ i, (D i).Niltest (fun _ : Unit => 1))
        (R : ∀ i k, (E i k).Niltest (fun _ : Unit => 1))
        (ea : ZMod N → ℂ) (eb : I → ZMod N → ℂ) (c : I → ℂ) (b : ∀ i, K i → ℂ),
      (∀ n, ((f₁ n - (1 + epsilon) * f₂ n : ℝ) : ℂ) =
        (∑ i, c i * (Q i).evalCyclic N (fun _ => n)) + ea n) →
      (∀ i n, (weight n : ℂ) = (∑ k, b i k * (R i k).evalCyclic N (fun _ => n)) + eb i n) →
      ∀ {p : ℝ}, 2 ≤ p → q ≤ p →
      (∑ i, ‖c i‖) ≤ Real.exp p → (∀ i, (∑ k, ‖b i k‖) ≤ Real.exp p) →
      (∀ i, (Q i).ComplexityLE p) → (∀ i k, (R i k).ComplexityLE p) →
      (∀ i, (Q i).normBound ≤ 1) → (∀ i k, (R i k).normBound ≤ 1) →
      (shiftTestingSeminorm (fun n => (weight n : ℂ)) B.testingFamily ea +
        ∑ i, ‖c i‖ * shiftTestingSeminorm (fun n => (Q i).evalCyclic N (fun _ => n))
          (translatedTestFamily B.testingFamily) (eb i) ≤ Real.exp (-(2 * q + 2))) →
      (Fintype.card (Sigma K) : ℝ) ≤ Real.exp p →
      Odd N → Real.exp ((p + C) ^ C) ≤ N →
      (∀ n, 0 ≤ f₁ n ∧ f₁ n ≤ Real.exp p) →
      (∀ n, 0 ≤ f₂ n ∧ f₂ n ≤ Real.exp p) →
      (∀ n, 0 ≤ weight n ∧ weight n ≤ Real.exp p) →
      CyclicNiltestUpperComparison.{0} (s + 2) N ((p + C) ^ C)
        (Real.exp (-((p + C) ^ C))) f₁ f₂ → False

end Erdos3.PositiveShiftBasis

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeOptionTargetObservableRegularity
namespace OAI

section

universe u v w₀ w₁ w₂

namespace Erdos3.RationalFilteredNilmanifold

open Module
open scoped TensorProduct NNReal

variable {Pivot : Type v} {LQ : Type u} {LS : Type w₀} {Param : Type w₁} {σ : Type w₂}
    [Fintype Pivot] {LP : Pivot → Type u}
    [LieRing LQ] [LieAlgebra ℚ LQ] [LieRing LS] [LieAlgebra ℚ LS]
    [∀ j, LieRing (LP j)] [∀ j, LieAlgebra ℚ (LP j)]
    {s t dQ dS : ℕ} {dp : Pivot → ℕ}
    (Q : RationalFilteredNilmanifold LQ s dQ)
    (partners : ∀ j, RationalFilteredNilmanifold (LP j) s (dp j))
    {Source : RationalFilteredNilmanifold LS t dS}
    {ψ : LS →ₗ⁅ℚ⁆ (∀ i : Option Pivot, optionLieSpace LQ LP i)}
    [TopologicalSpace (ℝ ⊗[ℚ] LQ)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] LQ)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] LQ)] [T2Space (ℝ ⊗[ℚ] LQ)]
    [∀ j, TopologicalSpace (ℝ ⊗[ℚ] LP j)] [∀ j, IsTopologicalAddGroup (ℝ ⊗[ℚ] LP j)]
    [∀ j, ContinuousSMul ℝ (ℝ ⊗[ℚ] LP j)] [∀ j, T2Space (ℝ ⊗[ℚ] LP j)]
    [TopologicalSpace (ℝ ⊗[ℚ] (∀ i : Option Pivot, optionLieSpace LQ LP i))]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ i : Option Pivot, optionLieSpace LQ LP i))]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] (∀ i : Option Pivot, optionLieSpace LQ LP i))]
    [T2Space (ℝ ⊗[ℚ] (∀ i : Option Pivot, optionLieSpace LQ LP i))]

theorem AdaptedMapGeometryData.optionTarget_observable_regularity
    {p0 q : ℝ}
    (geometry : Source.AdaptedMapGeometryData (optionProduct Q partners) ψ ((p0 + 3) ^ 2) q)
    {w : σ → ℕ} (descended : Param → Q.Niltest w)
    (hp0 : 0 ≤ p0) (hQ : Q.GeometryComplexityLE p0)
    (hunit : ∀ x, (descended x).UnitIntervalValued)
    (hcomplexity : ∀ x, (descended x).ComplexityLE p0) :
    (∀ x (y : geometry.target.model.Space),
      (optionOriginalObservable Q partners (fun x => (descended x).observable) x y).im = 0 ∧
      0 ≤ (optionOriginalObservable Q partners (fun x => (descended x).observable) x y).re ∧
      (optionOriginalObservable Q partners (fun x => (descended x).observable) x y).re ≤ 1) ∧
    (∀ x (y : geometry.target.model.Space),
      ‖optionOriginalObservable Q partners (fun x => (descended x).observable) x y‖ ≤ 1) ∧
    (∀ x, letI := geometry.target.model.metricSpace;
      LipschitzWith ⟨Real.exp (nativeOptionTargetObservableBudget p0), Real.exp_nonneg _⟩
        (fun y : geometry.target.model.Space =>
          optionOriginalObservable Q partners (fun x => (descended x).observable) x y)) ∧
    ∀ (sites : Set Param) (entropy : ℝ → ℝ),
      (∀ η : ℝ, 0 < η → η ≤ 1 → ∃ n : ℕ,
        (n : ℝ) ≤ entropy η ∧ ∃ rep : Fin n → {x : Param // x ∈ sites},
          ∀ x ∈ sites, ∃ i, ∀ y,
            ‖(descended x).observable y - (descended (rep i).val).observable y‖ ≤ η) →
      ∀ η : ℝ, 0 < η → η ≤ 1 → ∃ n : ℕ,
        (n : ℝ) ≤ entropy η ∧ ∃ rep : Fin n → {x : Param // x ∈ sites},
          ∀ x ∈ sites, ∃ i, ∀ y : geometry.target.model.Space,
            ‖optionOriginalObservable Q partners (fun x => (descended x).observable) x y -
              optionOriginalObservable Q partners (fun x => (descended x).observable)
                (rep i).val y‖ ≤ η := by
  classical
  let ℓ : ℝ≥0 := ⟨Real.exp p0, Real.exp_nonneg _⟩
  have hLip (x : Param) : letI := Q.metricSpace; LipschitzWith ℓ (descended x).observable := by
    let := Q.metricSpace
    apply (descended x).lipschitz.weaken
    change ((descended x).lipBound : ℝ) ≤ Real.exp p0
    have hb := (descended x).observable_budget (hcomplexity x)
    linarith [(descended x).normBound.coe_nonneg]
  let jointGeo := (p0 + 3) ^ 2
  let r := jointGeo + 2
  have hjoint : 0 ≤ jointGeo := by dsimp [jointGeo]; positivity
  have hr : 0 ≤ r := by dsimp [r]; linarith
  have hpr : p0 ≤ r := by dsimp [r, jointGeo]; nlinarith
  have htotal : (Fintype.card (Σ i : Option Pivot, Fin (optionDimension dQ dp i)) : ℝ) ≤
      jointGeo := by
    simpa only [finrank_eq_card_basis (optionProduct Q partners).basis, Fintype.card_fin] using
      geometry.target_dimension
  have hH : (⌈Real.exp (jointGeo + 1)⌉₊ : ℝ) ≤ Real.exp r := by
    simpa only [r, show jointGeo + 1 + 1 = jointGeo + 2 by ring] using
      ceil_exp_le_exp_add_one (show 0 ≤ jointGeo + 1 by linarith)
  have hbound := optionOriginalAdaptedLipschitzBound_le_exp Q partners ℓ
    ⌈Real.exp (jointGeo + 1)⌉₊ hr (Real.exp_le_exp.mpr hpr) (hQ.1.trans hpr)
    (htotal.trans (by dsimp [r]; linarith)) hH
  refine ⟨optionOriginalObservable_adapted_unit_interval Q partners
      (fun x => (descended x).observable) geometry.target hunit,
    fun x y => (hunit x).norm_le_one (optionOriginalSpaceProjection Q partners y), ?_, ?_⟩
  · intro x
    let := geometry.target.model.metricSpace
    have hl := optionOriginalObservable_adapted_lipschitz_of_logHeight Q partners
      (fun x => (descended x).observable) geometry.target ℓ (jointGeo + 1)
      geometry.target_forward hLip x
    apply hl.weaken
    change (optionOriginalAdaptedLipschitzBound (L₀ := LQ) (L := LP)
      (d₀ := dQ) (d := dp) ℓ ⌈Real.exp (jointGeo + 1)⌉₊ : ℝ) ≤
        Real.exp (nativeOptionTargetObservableBudget p0)
    convert hbound using 1
    unfold nativeOptionTargetObservableBudget r jointGeo
    congr 1
    ring
  · intro sites entropy hnets
    exact optionOriginalObservable_adapted_member_nets Q partners
      (fun x => (descended x).observable) geometry.target sites entropy hnets

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.QuadraticMarkedAffine
namespace OAI

section

namespace Erdos3.QuadraticMarked

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct BigOperators

noncomputable def seedCoordinate (η : RationalTorus.BottomQuotient 1 →ₗ[ℚ] ℚ) :
    (ℝ ⊗[ℚ] Seed) →ₗ[ℝ] ℝ :=
  (realifyFunctional η).comp ((lieQuotientMap (⊥ : LieIdeal ℚ Seed)).toLinearMap.baseChange ℝ)

end Erdos3.QuadraticMarked

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeResidualCrossInduction
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem mean_derivative_gowers_power_le {G : Type*} [AddCommGroup G] [Fintype G]
    (s : ℕ) (f : G → ℂ) :
    (𝔼 k, gowersNorm (s + 1) (multiplicativeDerivative f k)) ^ (2 ^ (s + 1)) ≤
      gowersNorm (s + 2) f ^ (2 ^ (s + 2)) := by
  rw [gowersNorm_derivative]
  exact expect_pow_two_pow_le (s + 1) _ (fun k => gowersNorm_nonneg s _)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.AllocatedGeometricInputBudget
namespace OAI

section

namespace Erdos3

open Module Submodule MeasureTheory

namespace VectorPolynomial

theorem exists_allocated_uniform_charts {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    {p : ℝ} (hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ p) :
    ∃ b : ∀ j, Basis (Fin (finrank ℝ (euclideanSubspace (U j))ᗮ)) ℝ (euclideanSubspace (U j))ᗮ,
      (∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))) ∧
      (∀ j z, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) z‖ ≤
        Real.exp (allocatedUniformChartLog p) * ‖z‖) ∧
      (∀ j z, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm z‖ ≤
        Real.exp (allocatedUniformChartLog p) * ‖z‖) ∧
      (∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
        mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ Real.exp (allocatedUniformChartLog p)) := by
  choose b hb hf hi hv0 hv using (fun j => exists_uniform_projected_chart (euclideanSubspace (U j)) (hJ j))
  exact ⟨b, hb, hf, hi, fun j => ⟨hv0 j, hv j⟩⟩

end VectorPolynomial
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RankPreparationProjectedAxisBudget
namespace OAI

section

namespace Erdos3.RankPreparationFamily

open VectorPolynomial
open scoped BigOperators

variable {I J : Type} [Fintype J] [DecidableEq J] {j : ℕ}

noncomputable def initial (p : VectorPolynomial I ℝ (J → ℝ)) : RankPreparationFamily I J (j + 1) :=
  fun i => if i = Fin.last j then RankPreparationLayer.initial p else RankPreparationLayer.empty

end Erdos3.RankPreparationFamily

end

section

namespace Erdos3

open scoped BigOperators
open VectorPolynomial

namespace RankPreparationFamily

variable {I J : Type} {m q : ℕ}

theorem pad_coefficients_mem (L : RankPreparationFamily I J m)
    (hL : ∀ j α, coefficients (L j).poly α ∈ (L j).space) :
    ∀ j α, coefficients (L.pad q j).poly α ∈ (L.pad q j).space := by
  intro j
  by_cases hj : j.val < m
  · rw [pad_apply_lt L j hj]
    exact hL ⟨j.val, hj⟩
  · rw [pad_apply_ge L j (by omega)]
    exact (RankPreparationLayer.empty_valid 0 0 0).2.1

end RankPreparationFamily
end Erdos3

end

section

namespace Erdos3

open Module Submodule VectorPolynomial
open scoped BigOperators

namespace RankPreparationLayer

variable {I J : Type} (L : RankPreparationLayer I J)

noncomputable def euclideanEquiv : euclideanSubspace L.space ≃ₗ[ℝ] L.space :=
  (euclideanSubspaceArrayEquiv L.space).toLinearEquiv.trans
    (LinearEquiv.piUnique ℝ (fun _ : Unit => L.space))

theorem euclidean_finrank : finrank ℝ (euclideanSubspace L.space) = L.rank :=
  L.euclideanEquiv.finrank_eq

theorem rank_add_orthogonal_finrank :
    L.rank + finrank ℝ (euclideanSubspace L.space)ᗮ = Fintype.card L.Coord := by
  rw [← L.euclidean_finrank, Submodule.finrank_add_finrank_orthogonal, finrank_euclideanSpace]

theorem lattice_full {d H R : ℕ} (hL : L.Valid d H R) (hH : 1 ≤ H) (hR : 1 ≤ R) :
    IsZLattice ℝ (latticeSection (standardEuclideanLattice L.Coord) (euclideanSubspace L.space)) :=
  jointRationalSpaceLattice_full L.basis L.rows hH hR hL.2.2.1 hL.2.2.2

end RankPreparationLayer

namespace RankPreparationFamily

variable {I J : Type} {s : ℕ} (L : RankPreparationFamily I J s)

theorem PreparedHeights.lattice_full {p : ℝ} {R : ℕ} (hL : L.PreparedHeights p R)
    (hp : 0 ≤ p) (hR : 1 ≤ R) (i : Fin s) :
    IsZLattice ℝ (latticeSection (standardEuclideanLattice (L i).Coord)
      (euclideanSubspace (L i).space)) :=
  (L i).lattice_full (hL i) (preparationHeight_pos hp _) hR

theorem PreparedHeights.coefficientTorus_compact {K : Type*} [Fintype K]
    {p : ℝ} {R : ℕ} (hL : L.PreparedHeights p R) (hp : 0 ≤ p) (hR : 1 ≤ R) :
    CompactSpace (CoefficientTorus (K := K) (fun i => (L i).space)) := by
  let := fun i => hL.lattice_full L hp hR i
  exact coefficientTorus_compact_of_lattice (fun i => (L i).space)

theorem PreparedHeights.exists_uniform_charts {p c : ℝ} {R : ℕ}
    (hL : L.PreparedHeights p R) (hp : 0 ≤ p) (hR : 1 ≤ R)
    (hC : ∀ i, (Fintype.card (L i).Coord : ℝ) ≤ c) :
    ∃ b : ∀ i, Basis (Fin (finrank ℝ (euclideanSubspace (L i).space)ᗮ)) ℝ
        (euclideanSubspace (L i).space)ᗮ,
      (∀ i, span ℤ (Set.range (b i)) = projectedIntegerLattice (euclideanSubspace (L i).space)) ∧
      (∀ i z, ‖normalizedOrthogonalChart (euclideanSubspace (L i).space) (b i) z‖ ≤
        Real.exp (allocatedUniformChartLog c) * ‖z‖) ∧
      (∀ i z, ‖(normalizedOrthogonalChart (euclideanSubspace (L i).space) (b i)).symm z‖ ≤
        Real.exp (allocatedUniformChartLog c) * ‖z‖) ∧
      (∀ i, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (L i).space) (b i) ∧
        mixedDensityCovolumeRatio (euclideanSubspace (L i).space) (b i) ≤
          Real.exp (allocatedUniformChartLog c)) := by
  let := fun i => hL.lattice_full L hp hR i
  exact exists_allocated_uniform_charts (fun i => (L i).space) hC

end RankPreparationFamily
end Erdos3

end

section

namespace Erdos3.RankPreparationLayer

open Module Submodule

variable {X J E : Type} [Fintype E] (L : RankPreparationLayer X J)
variable [IsZLattice ℝ
  (latticeSection (standardEuclideanLattice L.Coord) (euclideanSubspace L.space))]

noncomputable def integralCoordinateBasis
    (bW : Basis E ℤ
      (latticeSection (standardEuclideanLattice L.Coord) (euclideanSubspace L.space))) :
    Basis E ℝ L.space :=
  (bW.ofZLatticeBasis ℝ _).map L.euclideanEquiv

omit [Fintype E] in
theorem integralCoordinateBasis_integer
    (bW : Basis E ℤ
      (latticeSection (standardEuclideanLattice L.Coord) (euclideanSubspace L.space)))
    (i : L.Coord) (e : E) :
    ∃ z : ℤ, (L.integralCoordinateBasis bW e).val i = (z : ℝ) := by
  have h := (mem_standardEuclideanLattice L.Coord (bW e).val.val).mp (bW e).property i
  obtain ⟨z, hz⟩ := h
  refine ⟨z, ?_⟩
  change ((bW.ofZLatticeBasis ℝ _) e).val i = (z : ℝ)
  rw [Basis.ofZLatticeBasis_apply]
  exact hz.symm

noncomputable def integralCoordinateMatrix
    (bW : Basis E ℤ
      (latticeSection (standardEuclideanLattice L.Coord) (euclideanSubspace L.space))) :
    L.Coord → E → ℤ :=
  fun i e => Classical.choose (L.integralCoordinateBasis_integer bW i e)

end Erdos3.RankPreparationLayer

end

section

namespace Erdos3.RankPreparationLayer

open Module Submodule VectorPolynomial BohrLattice.MinkowskiSecondBox

variable {X J : Type} (L : RankPreparationLayer X J)

theorem exists_short_integral_basis {d H R : ℕ}
    (hL : L.Valid d H R) (hH : 1 ≤ H) (hR : 1 ≤ R) :
    ∃ bW : Basis (Fin L.rank) ℤ
      (latticeSection (standardEuclideanLattice L.Coord) (euclideanSubspace L.space)),
      ∀ a, ‖(bW a).val‖ ≤ L.shortIntegralBasisNormBound H R := by
  let := L.lattice_full hL hH hR
  obtain ⟨P, hP, hspace⟩ := exists_jointRationalSpace_generators
    L.basis L.rows hH hR hL.2.2.1 hL.2.2.2
  obtain ⟨v, hvspan, hvmem, hvnorm⟩ :=
    exists_bounded_integral_span_of_rational_range P L.space hspace hP
  let o : OrthonormalBasis (Fin L.rank) ℝ (euclideanSubspace L.space) :=
    (stdOrthonormalBasis ℝ (euclideanSubspace L.space)).reindex
      (finCongr L.euclidean_finrank)
  obtain ⟨b, hbspan, _hbprod, hbnorm⟩ := exists_short_euclidean_lattice_basis
    (latticeSection (standardEuclideanLattice L.Coord) (euclideanSubspace L.space))
    o v hvspan hvmem hvnorm
  refine ⟨integerBasisOfReal _ b hbspan, ?_⟩
  intro a
  rw [integerBasisOfReal_apply]
  exact hbnorm a

end Erdos3.RankPreparationLayer

end

section

namespace Erdos3

open Module Submodule

theorem basisAxisScale_jointRationalSpace_le_exp
    {J C V K : Type*} [Fintype J] [Fintype C] [Fintype V]
    (B : Matrix J C ℚ) (A : Matrix V J ℚ) {H R : ℕ}
    (hH : 1 ≤ H) (hB : ∀ i j, RationalHeightLE (B i j) H)
    (hA : ∀ v j, RationalHeightLE (A v j) R)
    (b : Basis K ℝ (euclideanSubspace (VectorPolynomial.jointRationalSpace B A))ᗮ)
    (hb : span ℤ (Set.range b) =
      projectedIntegerLattice (euclideanSubspace (VectorPolynomial.jointRationalSpace B A)))
    {p : ℝ} (hp : 0 ≤ p)
    (hJ : (Fintype.card J : ℝ) ≤ p) (hC : (Fintype.card C : ℝ) ≤ p)
    (hV : (Fintype.card V : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p) (hRp : (R : ℝ) ≤ Real.exp p)
    (i : K) :
    (basisAxisScale b i : ℝ) ≤ Real.exp ((p+2)^28) := by
  obtain ⟨Q, hQ, hQker⟩ :=
    VectorPolynomial.exists_jointRationalSpace_defining_matrix B A hH hB hA
  have hscale := basisAxisScale_le_of_rational_kernel Q _ hQker hQ b hb i
  have hrow : (Fintype.card (J ⊕ V) : ℝ) ≤ 2*p := by
    rw [Fintype.card_sum, Nat.cast_add]
    linarith only [hJ, hV]
  have hcol : (Fintype.card J : ℝ) ≤ 2*p := by linarith only [hJ, hp]
  have hheight :
      ((max (imageDefiningHeight (Fintype.card C) (Fintype.card J) H) R : ℕ) : ℝ) ≤
        Real.exp ((2*p+2)^10) := by
    apply (jointSpaceDefiningHeight_le_exp _ _ H R hp hJ hC hHp hRp).trans
    apply Real.exp_le_exp.mpr
    exact pow_le_pow_left₀ (show 0 ≤ p+2 by positivity) (show p+2 ≤ 2*p+2 by linarith only [hp]) 10
  have hceil := rationalKernelSeparationConstant_ceil_le_exp_power Q
    (show 0 ≤ 2*p by positivity) 10 (by decide) hrow hcol hheight hQ
  have hpower : (2*p+2)^14 ≤ (p+2)^28 := by
    calc
      _ ≤ ((p+2)^2)^14 := pow_le_pow_left₀ (show 0 ≤ 2*p+2 by positivity)
        (show 2*p+2 ≤ (p+2)^2 by nlinarith only [hp, sq_nonneg p]) 14
      _ = _ := by rw [← pow_mul]
  calc
    _ ≤ (⌈rationalKernelAxisBound Q
        (max (imageDefiningHeight (Fintype.card C) (Fintype.card J) H) R)⌉₊ : ℝ) :=
      Nat.cast_le.mpr hscale
    _ ≤ Real.exp ((2*p+2)^14) := hceil
    _ ≤ _ := Real.exp_le_exp.mpr hpower

namespace RankPreparationLayer

theorem basisAxisScale_le_exp {X J : Type} (L : RankPreparationLayer X J)
    {degree H R : ℕ} (hL : L.Valid degree H R) (hH : 1 ≤ H)
    {K : Type*} (b : Basis K ℝ (euclideanSubspace L.space)ᗮ)
    (hb : span ℤ (Set.range b) = projectedIntegerLattice (euclideanSubspace L.space))
    {p : ℝ} (hp : 0 ≤ p)
    (hCoord : (Fintype.card L.Coord : ℝ) ≤ p)
    (hColumn : (Fintype.card L.Column : ℝ) ≤ p)
    (hRow : (Fintype.card L.Row : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p) (hRp : (R : ℝ) ≤ Real.exp p)
    (i : K) :
    (basisAxisScale b i : ℝ) ≤ Real.exp ((p+2)^28) :=
  basisAxisScale_jointRationalSpace_le_exp L.basis L.rows hH hL.2.2.1 hL.2.2.2
    b hb hp hCoord hColumn hRow hHp hRp i

end RankPreparationLayer

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.PreparedCoefficientTorusCompact
namespace OAI

section

namespace Erdos3.RankPreparationFamily

open Module Submodule VectorPolynomial

variable {X J : Type} {m : ℕ} (L : RankPreparationFamily X J m)

theorem PreparedHeights.euclideanLayerTorus_compact
    {p : ℝ} {R : ℕ} (hL : L.PreparedHeights p R)
    (hp : 0 ≤ p) (hR : 1 ≤ R) (j : Fin m) :
    CompactSpace (euclideanSubspace (L j).space ⧸
      (latticeSection (standardEuclideanLattice (L j).Coord)
        (euclideanSubspace (L j).space)).toAddSubgroup) := by
  let Λ := latticeSection (standardEuclideanLattice (L j).Coord)
    (euclideanSubspace (L j).space)
  let : IsZLattice ℝ Λ := hL.lattice_full L hp hR j
  have hc := IsZLattice.isCompact_range_of_periodic Λ
    (QuotientAddGroup.mk' Λ.toAddSubgroup)
    (QuotientAddGroup.isQuotientMap_mk Λ.toAddSubgroup).continuous (by
      intro x z hz
      rw [map_add]
      have hz0 : QuotientAddGroup.mk' Λ.toAddSubgroup z = 0 :=
        (QuotientAddGroup.eq_zero_iff z).mpr hz
      rw [hz0, add_zero])
  rw [Set.range_eq_univ.mpr (QuotientAddGroup.mk'_surjective Λ.toAddSubgroup)] at hc
  exact ⟨hc⟩

end Erdos3.RankPreparationFamily

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.PreparedDeterminingCoordinates
namespace OAI

section

namespace Erdos3.RankPreparationFamily

open Module Submodule VectorPolynomial
open scoped BigOperators

variable {X J : Type} {m : ℕ}

variable (L : RankPreparationFamily X J m) (E : Fin m → Type)

variable {E} [∀ u, Fintype (E u)]
variable [∀ u, IsZLattice ℝ
  (latticeSection (standardEuclideanLattice (L u).Coord) (euclideanSubspace (L u).space))]
variable (bW : ∀ u, Basis (E u) ℤ
  (latticeSection (standardEuclideanLattice (L u).Coord) (euclideanSubspace (L u).space)))
variable (hmem : ∀ u α, coefficients (L u).poly α ∈ (L u).space)

noncomputable def determiningPolynomial (a : L.DeterminingIndex E) : MvPolynomial X ℝ :=
  integralBasisPolynomialCoordinates (L a.1).space
    ((L a.1).integralCoordinateBasis (bW a.1)) (L a.1).poly (hmem a.1) a.2

noncomputable def determiningMatrix
    (r : L.PreparedCoordinate) (a : L.DeterminingIndex E) : ℤ :=
  if h : a.1 = r.1 then (L r.1).integralCoordinateMatrix (bW r.1) r.2 (h ▸ a.2)
  else 0

end Erdos3.RankPreparationFamily

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

def AllocatedRankComponentCoefficient
    (inactive : LayerSamplerAxis I n → Prop) (j : Fin m) :
    AllocatedCongruenceRankOutput X E inactive j → Type _
  | .inl _ => Option (LayerSamplerVariables G I n B)
  | .inr _ => BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ForecastNativeJointTestBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module
open scoped Classical NNReal
variable {m : ℕ} {X : Type*} [Fintype X]
variable {I E : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
variable {n : Fin m → ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (Lsize : ℕ)
local notation "short" => allocatedShortAxis (I := I) U b Lsize
local notation "Grid" => AllocatedShortIntegerAxis U b Lsize →
  ((Finset.univ : Finset (Finset Empty)) : Type) → ℤ

def forecastShortGridSheet (grid : Grid) :
    ∀ j, {i : Fin (n j) // short ⟨j, .inr i⟩} → ℤ :=
  fun j i => grid ⟨⟨j, i.val⟩, i.property⟩ ⟨∅, Finset.mem_univ _⟩

end Erdos3.VectorPolynomial

end

end OAI
end


