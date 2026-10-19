-- Prove2me | Definitions.Def_OAIE3v2B135
-- name    : OAIE3v2B135
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T11:13:36.000649+00:00
-- url     : https://prove2.me/theorems/35730220-81f2-4c20-a534-c472a28eff2a
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 137 of 311
-- statement:
--   Definitions bundle 137 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B114`, `OAIE3v2B115`, `OAIE3v2B116`, `OAIE3v2B117`, `OAIE3v2B118`, `OAIE3v2B119`, `OAIE3v2B120`, `OAIE3v2B121`, `OAIE3v2B122` of this split.
--
--   Modules: `Estimates/CommonCoefficientFourAnnihilators.lean`, `Estimates/CommonRefilteredFactorization.lean`, `Estimates/ControlledProductReconstruction.lean`, `Estimates/CurrentLayerPreservation.lean`, `Estimates/HomogeneousSubspaceCorrections.lean`, `Estimates/ImageRepresentatives.lean`, `Estimates/NativeCentralSeed.lean`, `Estimates/NativeSquarefreeCoefficientBases.lean`, `Estimates/RationalPowerHeight.lean`, `Estimates/ReplicatedLieAction.lean`, `Estimates/StepDropTerminalContainment.lean`, `Estimates/VerticalTranslations.lean`, `Fourier/ControlledReplicatedFrequency.lean`, `Fourier/JoinedFrequencyQuotientInjectivity.lean`, `Fourier/LogCharacterBudget.lean`, `Geometry/HorizontalCoordinateBounds.lean`, `Geometry/RealSubspaceCoordinateRetraction.lean`, `Geometry/SymbolRepresentativeTransport.lean`, `Linear/ComparisonChosenLayerBasis.lean`, `Linear/RankQuotientHeightBudget.lean`, `Nilpotent/BCHSmoothPartitionBudget.lean`, `Nilpotent/NiltestAffineProjection.lean`, `Nilpotent/NiltestBasepointNormalization.lean`, `Polynomial/ControlledPositivePolynomialDownsets.lean`, `Polynomial/NativeTotalDegreeMultifiltration.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B114
import Definitions.Def_OAIE3v2B115
import Definitions.Def_OAIE3v2B116
import Definitions.Def_OAIE3v2B117
import Definitions.Def_OAIE3v2B118
import Definitions.Def_OAIE3v2B119
import Definitions.Def_OAIE3v2B120
import Definitions.Def_OAIE3v2B121
import Definitions.Def_OAIE3v2B122

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.BCHSmoothPartitionBudget
namespace OAI

section

namespace Erdos3.NilpotentLieBCHGroup

open Module
open scoped NNReal

variable {ι κ L M : Type*} [Fintype ι] [Fintype κ]
  [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L] [IsScalarTower ℚ ℝ L]
  [LieRing M] [LieAlgebra ℚ M] [LieAlgebra ℝ M] [IsScalarTower ℚ ℝ M]
  [TopologicalSpace L] [IsTopologicalAddGroup L] [ContinuousSMul ℝ L] [T2Space L]
  [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousSMul ℝ M] [T2Space M]
  {s t H : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}
  {hM : LieModule.lowerCentralSeries ℚ M M t = ⊥}

theorem exists_local_metric_lifts_on_image (e : Basis ι ℝ L) (f : Basis κ ℝ M)
    (φ : L →ₗ⁅ℝ⁆ M) (σ : M →ₗ[ℝ] L)
    (hσ : (φ.toLinearMap.comp σ).comp φ.toLinearMap = φ.toLinearMap)
    (B : ℝ≥0) (hσB : ∀ i j, |e.repr (σ (f j)) i| ≤ B)
    (c : κ → κ → κ → ℚ)
    (hstructure : ∀ i j k, algebraMap ℚ ℝ (c i j k) = f.repr ⁅f i, f j⁆ k)
    (hc : ∀ i j k, RationalHeightLE (c i j k) H) :
    letI := rightMetricSpace (hnil := hnil) e
    letI := rightMetricSpace (hnil := hM) f
    let C := bchLogMetricConstant t (Fintype.card κ) H 1
    let K := coordinateLipschitzBound (Fintype.card ι) (Fintype.card κ) B *
      ((Fintype.card κ : ℝ≥0) + 1) * C
    ∀ g ∈ (mapReal (hnil := hnil) (hM := hM) φ).range, dist 1 g < (C⁻¹ : ℝ≥0) →
      ∃ h : NilpotentLieBCHGroup L s hnil,
        mapReal φ h = g ∧ dist 1 h ≤ K * dist 1 g := by
  let := rightMetricSpace (hnil := hnil) e
  let := rightMetricSpace (hnil := hM) f
  dsimp only
  intro g hgrange hg
  obtain ⟨x, hx⟩ := hgrange
  have hcoord : φ x.coord = g.coord := congrArg NilpotentLieBCHGroup.coord hx
  have hs := DFunLike.congr_fun hσ x.coord
  change φ (σ (φ x.coord)) = φ x.coord at hs
  rw [hcoord] at hs
  exact ⟨⟨σ g.coord⟩, ext hs, dist_linear_lift_le e f σ B hσB c hstructure hc g hg⟩

end Erdos3.NilpotentLieBCHGroup

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ImageRepresentatives
namespace OAI

section

namespace Erdos3

open Module NilpotentLieBCHGroup
open scoped Matrix TensorProduct NNReal

theorem exists_bounded_image_representatives (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {ι κ L M : Type*} [Fintype ι] [Fintype κ]
      [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)]
      (hL : LieModule.lowerCentralSeries ℚ L L s = ⊥)
      (hM : LieModule.lowerCentralSeries ℚ M M s = ⊥)
      (e : Basis ι ℚ L) (f : Basis κ ℚ M) (φ : L →ₗ⁅ℚ⁆ M)
      (Λ : Subgroup (NilpotentLieBCHGroup M s hM)) (l H : ℕ) (p : ℝ),
      0 < l → scaledIntegerGrid l ⊆ bchSubgroupCoordinates f Λ →
      (∀ i j k, RationalHeightLE (lieStructureConstants e i j k) H) →
      (∀ i j, RationalHeightLE (f.repr (φ (e j)) i) H) →
      0 ≤ p → (Fintype.card ι : ℝ) ≤ p → (Fintype.card κ : ℝ) ≤ p →
      (H : ℝ) ≤ Real.exp p → (l : ℝ) ≤ Real.exp p →
      ∀ y : CosetImage (realificationMap (hnil := hL) (hM := hM) φ) (Λ.map realificationHom),
        ∃ x, projectToCosetImage (realificationMap (hnil := hL) (hM := hM) φ)
            (Λ.map realificationHom) x = y ∧
          ∀ i, |(f.baseChange ℝ).repr (realificationMap (hnil := hL) (hM := hM) φ x).coord i| ≤
            Real.exp ((((p + 2) ^ 4 + C) ^ C) + (p + 2) ^ 2) := by
  obtain ⟨C, hC, hrep⟩ := exists_realification_representatives_exp_bound s
  refine ⟨C, hC, ?_⟩
  intro ι κ L M _ _ _ _ _ _ _ _ _ hL hM e f φ Λ l H p hl hΛ hc hφ hp hι hκ hH hlp y
  classical
  let Γ := Λ.comap (map (hnil := hL) φ)
  let A := LinearMap.toMatrix e f φ.toLinearMap
  let q := l * matrixDenominator A
  have hA : ∀ i j, RationalHeightLE (A i j) H := by
    intro i j
    change RationalHeightLE (LinearMap.toMatrix e f φ.toLinearMap i j) H
    rw [LinearMap.toMatrix_apply]
    exact hφ i j
  have hq : 0 < q := Nat.mul_pos hl (matrixDenominator_pos A)
  have hqbound := matrixDenominator_allowance_le_exp A l H hA hp hκ hι hH hlp
  have hp' : p ≤ (p + 2) ^ 4 := le_power_budget hp (by decide)
  obtain ⟨g, hg⟩ := projectToCosetImage_surjective
    (realificationMap (hnil := hL) (hM := hM) φ) (Λ.map realificationHom) y
  obtain ⟨r, hr, γ, hγ, heq⟩ := hrep e hL Γ q H ((p + 2) ^ 4) hq
    (bch_comap_inner_grid e f φ Λ l hΛ) hc (by positivity) (hι.trans hp')
    (hH.trans (Real.exp_le_exp.mpr hp')) hqbound g
  have hγmap : realificationMap (hnil := hL) (hM := hM) φ γ ∈ Λ.map realificationHom :=
    realificationMap_subgroup φ Γ Λ le_rfl hγ
  refine ⟨r, ?_, ?_⟩
  · apply Subtype.ext
    have hgy := congrArg Subtype.val hg
    change (QuotientGroup.mk (realificationMap (hnil := hL) (hM := hM) φ g) :
      _ ⧸ Λ.map realificationHom) = y.val at hgy
    rw [← hgy, heq, map_mul]
    exact (quotient_mk_mul_mem (Λ.map realificationHom)
      (realificationMap (hnil := hL) (hM := hM) φ r) ⟨_, hγmap⟩).symm
  · intro i
    have hnorm : ‖(e.baseChange ℝ).equivFun r.coord‖ ≤ Real.exp (((p + 2) ^ 4 + C) ^ C) := by
      apply (pi_norm_le_iff_of_nonneg (Real.exp_nonneg _)).mpr
      intro j
      simpa only [Basis.equivFun_apply, Real.norm_eq_abs] using hr j
    have hbound := abs_matrix_mulVec_le (fun i j => (A i j : ℝ)) (H : ℝ≥0)
      (fun i j => (hA i j).abs_real_le) ((e.baseChange ℝ).equivFun r.coord) i
    dsimp only [A] at hbound
    rw [baseChange_matrix_apply e f φ.toLinearMap] at hbound
    have hfac : ((Fintype.card ι : ℝ) + 1) * ((H : ℝ) + 1) ≤
        (coordinateLipschitzBound (Fintype.card κ) (Fintype.card ι) H : ℝ) := by
      change _ ≤ ((Fintype.card κ : ℝ) + Fintype.card ι + 1) * ((H : ℝ) + 1)
      gcongr
      exact le_add_of_nonneg_left (Nat.cast_nonneg _)
    calc
      _ ≤ ((Fintype.card ι : ℝ) + 1) * ((H : ℝ) + 1) * ‖(e.baseChange ℝ).equivFun r.coord‖ := hbound
      _ ≤ (coordinateLipschitzBound (Fintype.card κ) (Fintype.card ι) H : ℝ) *
          Real.exp (((p + 2) ^ 4 + C) ^ C) := mul_le_mul hfac hnorm (norm_nonneg _) (NNReal.coe_nonneg _)
      _ ≤ Real.exp ((p + 2) ^ 2) * Real.exp (((p + 2) ^ 4 + C) ^ C) :=
        mul_le_mul_of_nonneg_right (coordinateLipschitzBound_le_exp _ _ _ hp hκ hι hH) (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.NiltestBasepointNormalization
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct NNReal

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  (D : RationalFilteredNilmanifold L s d)

namespace Niltest

variable {D} {w : σ → ℕ}

theorem norm_evalCyclic_le (T : D.Niltest w) (N : ℕ) [NeZero N] (x : σ → ZMod N) :
    ‖T.evalCyclic N x‖ ≤ T.normBound := T.norm_eval_le _

end Niltest
end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ControlledProductReconstruction
namespace OAI

section

namespace Erdos3

open Module NilpotentLieBCHGroup
open scoped NNReal TensorProduct

theorem exists_controlled_rational_image_reconstruction (s : ℕ) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ {ι κ L M : Type*} [Fintype ι] [Fintype κ]
      [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)]
      (hL : LieModule.lowerCentralSeries ℚ L L s = ⊥)
      (hM : LieModule.lowerCentralSeries ℚ M M s = ⊥)
    (e : Basis ι ℚ L) (f : Basis κ ℚ M) (φ : L →ₗ⁅ℚ⁆ M)
    (Γ : Subgroup (NilpotentLieBCHGroup L s hL))
    (Λ : Subgroup (NilpotentLieBCHGroup M s hM))
    (l m H : ℕ) (hl : 0 < l) (hm : 0 < m) (_hH : 1 ≤ H)
    (hΓ : bchSubgroupCoordinates e Γ ⊆ denominatorGrid l)
    (_hΛin : scaledIntegerGrid m ⊆ bchSubgroupCoordinates f Λ)
    (hΛout : bchSubgroupCoordinates f Λ ⊆ denominatorGrid m)
    (_hcL : ∀ i j k, RationalHeightLE (lieStructureConstants e i j k) H)
    (_hcM : ∀ i j k, RationalHeightLE (lieStructureConstants f i j k) H)
    (_hφ : ∀ i j, RationalHeightLE (f.repr (φ (e j)) i) H)
    (_hcover : Λ.map realificationHom ⊓ (realificationMap (hnil := hL) (hM := hM) φ).range ≤
      (Γ.map realificationHom).map (realificationMap (hnil := hL) (hM := hM) φ))
    (u : (NilpotentLieBCHGroup (ℝ ⊗[ℚ] L) s (realification_lowerCentralSeries_eq_bot hL) ⧸
      Γ.map realificationHom) → ℂ)
    (_hker : ∀ k ∈ (realificationMap (hnil := hL) (hM := hM) φ).ker, ∀ x,
      u (QuotientGroup.mk (k * x)) = u (QuotientGroup.mk x))
    (ℓ B : ℝ≥0)
    (_hu : letI := realificationQuotientMetricSpace e Γ l hl hΓ; LipschitzWith ℓ u)
    (_hub : ∀ x, ‖u x‖ ≤ B)
    (p : ℝ) (_hp : 0 ≤ p) (_hι : (Fintype.card ι : ℝ) ≤ p) (_hκ : (Fintype.card κ : ℝ) ≤ p)
    (_hHp : (H : ℝ) ≤ Real.exp p) (_hmp : (m : ℝ) ≤ Real.exp p)
    (_hℓp : (ℓ : ℝ) ≤ Real.exp p) (_hBp : (B : ℝ) ≤ Real.exp p),
    letI := realificationQuotientMetricSpace f Λ m hm hΛout
    ∃ (v : (NilpotentLieBCHGroup (ℝ ⊗[ℚ] M) s (realification_lowerCentralSeries_eq_bot hM) ⧸
      Λ.map realificationHom) → ℂ) (K : ℝ≥0),
      (K : ℝ) ≤ Real.exp ((p + N) ^ N) ∧ LipschitzWith K v ∧ (∀ y, ‖v y‖ ≤ 2 * B) ∧
      ∀ x, v (QuotientGroup.mk (realificationMap (hnil := hL) (hM := hM) φ x)) = u (QuotientGroup.mk x) := by
  obtain ⟨C, _, hrep⟩ := exists_bounded_image_representatives s
  obtain ⟨D, _, hprod⟩ := exists_bch_triple_product_exp_bound s 1
  obtain ⟨F, _, hleft⟩ := exists_uniform_left_lipschitz_exp_bound s 1
  obtain ⟨E, _, hbox⟩ := exists_bchBoxMetricConstant_exp_bound s D
  obtain ⟨Z, _, hlog⟩ := exists_bchLogMetricConstant_exp_bound s
  obtain ⟨N, hN, hbudget⟩ := exists_generalReconstructionLogBudget_bound C D E F Z
  refine ⟨N, hN, ?_⟩
  intro ι κ L M _ _ _ _ _ _ _ _ _ _ _ _ _ _ hL hM e f φ Γ Λ l m H hl hm hH
    hΓ hΛin hΛout hcL hcM hφ hcover u hker ℓ B hu hub p hp hι hκ hHp hmp hℓp hBp

  classical
  let : FiniteDimensional ℝ (ℝ ⊗[ℚ] L) := (e.baseChange ℝ).finiteDimensional_of_finite
  let : FiniteDimensional ℝ (ℝ ⊗[ℚ] M) := (f.baseChange ℝ).finiteDimensional_of_finite
  let := rightMetricSpace (hnil := realification_lowerCentralSeries_eq_bot hL) (e.baseChange ℝ)
  let := rightMetricSpace (hnil := realification_lowerCentralSeries_eq_bot hM) (f.baseChange ℝ)
  let := rightMetricSpace_isIsometricSMul (hnil := realification_lowerCentralSeries_eq_bot hL) (e.baseChange ℝ)
  let := rightMetricSpace_isIsometricSMul (hnil := realification_lowerCentralSeries_eq_bot hM) (f.baseChange ℝ)
  let Φ := realificationMap (hnil := hL) (hM := hM) φ
  let J := Φ.range
  obtain ⟨Q, hQ, hJ⟩ := exists_realified_image_defining_matrix (hL := hL) (hM := hM) e f φ hH hφ
  let HQ : ℝ≥0 := (2 * ((Fintype.card ι + 1) * (H * rationalKernelHeight (Fintype.card κ) H) ^ Fintype.card ι) : ℕ)
  have hQabs : ∀ i j, |(Q i j : ℝ)| ≤ HQ := by
    intro i j
    change |(Q i j : ℝ)| ≤ ((2 * ((Fintype.card ι + 1) *
      (H * rationalKernelHeight (Fintype.card κ) H) ^ Fintype.card ι) : ℕ) : ℝ)
    exact (hQ i j).abs_real_le
  let R := (((p + 2) ^ 4 + C) ^ C) + (p + 2) ^ 2
  have hR : 0 ≤ R := by dsimp [R]; positivity
  let q := p + R + 1
  have hq : 0 ≤ q := by dsimp [q]; linarith
  have hpq : p ≤ q := by dsimp [q]; linarith
  let S := {g | g ∈ J ∧ ∀ i, |(f.baseChange ℝ).repr g.coord i| ≤ Real.exp R}
  have hrepS : ∀ y : CosetImage Φ (Λ.map realificationHom),
      ∃ x, projectToCosetImage Φ (Λ.map realificationHom) x = y ∧ Φ x ∈ S := by
    intro y
    obtain ⟨x, hx, hxb⟩ := hrep hL hM e f φ Λ m H p hm hΛin hcL hφ hp hι hκ hHp hmp y
    exact ⟨x, hx, ⟨⟨x, rfl⟩, hxb⟩⟩
  have hlarge {g} (hg : g ∈ S) : ∀ i, |(f.baseChange ℝ).repr g.coord i| ≤ Real.exp ((q + 2) ^ 1) := by
    intro i
    apply (hg.2 i).trans
    apply Real.exp_le_exp.mpr
    dsimp [q]
    simp only [pow_one]
    linarith
  let W : ℝ≥0 := ⟨Real.exp ((q + D) ^ D), Real.exp_nonneg _⟩
  have hW : 1 ≤ W := Real.one_le_exp (by positivity)
  have hprodS : ∀ x ∈ S, ∀ y ∈ S, ∀ i, |(f.baseChange ℝ).repr (y⁻¹ * x).coord i| ≤ W := by
    intro x hx y hy i
    have h := hprod (f.baseChange ℝ) (lieStructureConstants f) H q
      (realification_lowerCentralSeries_eq_bot hM) y⁻¹ x 1
      (fun i j k => (realLieBasis_structure f i j k).symm) hq (hκ.trans hpq)
      (hHp.trans (Real.exp_le_exp.mpr hpq)) hcM
      (fun j => by simpa only [coord_inv, map_neg, Finsupp.neg_apply, abs_neg] using hlarge hy j)
      (hlarge hx) (fun j => by simp only [coord_one, map_zero, Finsupp.zero_apply, abs_zero]; positivity) i
    change |(f.baseChange ℝ).repr (y⁻¹ * x).coord i| ≤ Real.exp ((q + D) ^ D)
    simpa only [mul_one] using h
  obtain ⟨Kleft, _, hKleftBound, hKleft⟩ := hleft (f.baseChange ℝ) (lieStructureConstants f) H q
    (realification_lowerCentralSeries_eq_bot hM)
    (fun i j k => (realLieBasis_structure f i j k).symm) hq (hκ.trans hpq)
    (hHp.trans (Real.exp_le_exp.mpr hpq)) hcM
  obtain ⟨ε, hε, hεinv, hgap⟩ := exists_uniform_lattice_image_gap (f.baseChange ℝ)
    (lieStructureConstants f) (fun i j k => (realLieBasis_structure f i j k).symm) hcM
    Q HQ W Kleft hW hQabs m hm J (Λ.map realificationHom) hJ
    (realification_subgroup_grid f Λ m hΛout) S (fun _ h => h.1) hprodS
    (fun y hy => hKleft y⁻¹ (fun j => by
      simpa only [coord_inv, map_neg, Finsupp.neg_apply, abs_neg] using hlarge hy j))
  obtain ⟨σ, hσ, hσH⟩ := exists_bounded_linear_image_section e f φ.toLinearMap hH hφ
  have hσB : ∀ i j, |(e.baseChange ℝ).repr (σ.baseChange ℝ ((f.baseChange ℝ) j)) i| ≤
      (rationalKernelHeight (Fintype.card κ) H : ℝ) := by
    intro i j
    rw [linearMap_baseChange_basis]
    exact (hσH i j).abs_real_le
  let T := bchLogMetricConstant s (Fintype.card κ) H 1
  let K := coordinateLipschitzBound (Fintype.card ι) (Fintype.card κ)
    (rationalKernelHeight (Fintype.card κ) H) * ((Fintype.card κ : ℝ≥0) + 1) * T
  have hlift := exists_local_metric_lifts_on_image
    (hnil := realification_lowerCentralSeries_eq_bot hL) (hM := realification_lowerCentralSeries_eq_bot hM)
    (e.baseChange ℝ) (f.baseChange ℝ) (realificationLieHom φ) (σ.baseChange ℝ)
    (linearMap_baseChange_image_section φ.toLinearMap σ hσ) (rationalKernelHeight (Fintype.card κ) H)
    hσB (lieStructureConstants f) (fun i j k => (realLieBasis_structure f i j k).symm) hcM
  let := realificationQuotientMetricSpace e Γ l hl hΓ
  have hpull : LipschitzWith ℓ (fun x => u (QuotientGroup.mk x)) := by
    simpa only [mul_one, Function.comp_def] using hu.comp
      (quotientMetricSpace_lipschitz_mk (e.baseChange ℝ) (Γ.map realificationHom)
        (realification_subgroup_closed_discrete e Γ l hl hΓ).1)
  obtain ⟨v, hv, hLip, hbound⟩ := exists_ambient_image_reconstruction Φ (Γ.map realificationHom)
    (Λ.map realificationHom) (realification_subgroup_closed_discrete f Λ m hm hΛout).1
    hcover (fun x => u (QuotientGroup.mk x)) hker
    (fun γ hγ x => congrArg u (QuotientGroup.eq.mpr (by
      simpa only [mul_inv_rev, inv_mul_cancel_left, inv_mul_cancel_right] using
        (Γ.map realificationHom).inv_mem hγ)))
    S ℓ K B T⁻¹ ε (inv_pos.mpr (bchLogMetricConstant_pos _ _ _ _)) hε hpull
    (fun x => hub _) hrepS hgap hlift
  let r := generalReconstructionLogBudget C D E F Z p
  obtain ⟨hr, hpr, h18, h48, h24, hZr, hEr, hFr⟩ :=
    generalReconstructionLogBudget_bounds C D E F Z hp
  have hexp : Real.exp p ≤ Real.exp r := Real.exp_le_exp.mpr hpr
  let Asec := coordinateLipschitzBound (Fintype.card ι) (Fintype.card κ)
    (rationalKernelHeight (Fintype.card κ) H)
  let Ndim : ℝ≥0 := (Fintype.card κ : ℝ≥0) + 1
  let Den : ℝ≥0 := (matrixDenominator Q * m : ℕ)
  let Row : ℝ≥0 := Ndim * (HQ + 1)
  let Box : ℝ≥0 := ⟨bchBoxCoordinateBound s (Fintype.card κ) H W,
    bchBoxCoordinateBound_nonneg _ _ _ W.coe_nonneg⟩
  have hAsec : (Asec : ℝ) ≤ Real.exp r :=
    (imageSection_bound_le_exp _ _ H hp hι hκ hHp).trans (Real.exp_le_exp.mpr h18)
  have hNdim : (Ndim : ℝ) ≤ Real.exp r := by
    apply le_trans _ hexp
    change (Fintype.card κ : ℝ) + 1 ≤ Real.exp p
    exact (by linarith : (Fintype.card κ : ℝ) + 1 ≤ p + 1).trans (Real.add_one_le_exp p)
  have hT : (T : ℝ) ≤ Real.exp r :=
    (hlog _ H p hp hκ hHp).trans (Real.exp_le_exp.mpr hZr)
  have hDen : (Den : ℝ) ≤ Real.exp r :=
    (imageDefiningDenominator_le_exp Q (Fintype.card ι) H m hQ hp hι hκ hHp hmp).trans
      (Real.exp_le_exp.mpr h48)
  have hRow : (Row : ℝ) ≤ Real.exp r := by
    apply le_trans _ (Real.exp_le_exp.mpr h24)
    exact imageDefiningRow_bound_le_exp _ _ H hp hι hκ hHp
  have hBox : (Box : ℝ) ≤ Real.exp r := by
    have hpqd : p ≤ q + D := hpq.trans (le_add_of_nonneg_right (Nat.cast_nonneg D))
    have hwbound : (W : ℝ) ≤ Real.exp ((q + D + 2) ^ D) := by
      change Real.exp ((q + D) ^ D) ≤ _
      exact Real.exp_le_exp.mpr (pow_le_pow_left₀ (by positivity) (by linarith) D)
    have hh := (bchBoxCoordinateBound_le_bchBoxMetricConstant s (Fintype.card κ) H W).trans
      (hbox _ H W (q + D) (by positivity) (hκ.trans hpqd)
        (hHp.trans (Real.exp_le_exp.mpr hpqd)) hwbound)
    exact hh.trans (Real.exp_le_exp.mpr hEr)
  have hY : (Kleft : ℝ) ≤ Real.exp r := hKleftBound.trans (Real.exp_le_exp.mpr hFr)
  have hεformula : (ε : ℝ)⁻¹ = (T : ℝ) * Kleft + Den * Row * Box * T * Kleft + 1 := by
    rw [hεinv]
    change _ = (bchLogMetricConstant s (Fintype.card κ) H 1 : ℝ) * Kleft +
      ((matrixDenominator Q * m : ℕ) : ℝ) * (((Fintype.card κ : ℝ) + 1) * ((HQ : ℝ) + 1)) *
        bchBoxCoordinateBound s (Fintype.card κ) H W *
        (bchLogMetricConstant s (Fintype.card κ) H 1 : ℝ) * Kleft + 1
    ring
  have htotal := generalReconstructionConstant_le_exp ℓ B Asec Ndim T Den Row Box Kleft ε r hr
    (hℓp.trans hexp) (hBp.trans hexp) hAsec hNdim hT hDen hRow hBox hY hεformula
  exact ⟨v, _, htotal.trans (Real.exp_le_exp.mpr (hbudget p hp)), hLip, hbound, hv⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ReplicatedLieAction
namespace OAI

section

namespace Erdos3

namespace RationalFilteredNilmanifold.MultidegreeStructure

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s d : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  (M : D.MultidegreeStructure bound)

noncomputable def restrictBound (bound' : σ → ℕ) (hbound : bound' ≤ bound)
    (hzero : ∀ a, ¬a ≤ bound' → M.filtration.layer a = ⊥) :
    D.MultidegreeStructure bound' where
  filtration := M.filtration.restrictBound bound' hzero
  ordinary := M.ordinary
  basis a := M.basis (fun i => ⟨(a i).val, lt_of_lt_of_le (a i).isLt (Nat.add_le_add_right (hbound i) 1)⟩)

theorem restrictBound_complexity (bound' : σ → ℕ) (hbound : bound' ≤ bound)
    (hzero : ∀ a, ¬a ≤ bound' → M.filtration.layer a = ⊥)
    {p : ℝ} (hM : M.ComplexityLE p) :
    (M.restrictBound bound' hbound hzero).ComplexityLE p :=
  ⟨hM.1, fun a => hM.2 (fun i =>
    ⟨(a i).val, lt_of_lt_of_le (a i).isLt (Nat.add_le_add_right (hbound i) 1)⟩)⟩

end RationalFilteredNilmanifold.MultidegreeStructure

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RationalPowerHeight
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped NNReal TensorProduct

theorem exists_native_complex_reconstruction (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L M : Type*} [LieRing L] [LieAlgebra ℚ L]
      [LieRing M] [LieAlgebra ℚ M]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)]
      {d e : ℕ} (D : RationalFilteredNilmanifold L s d) (E : RationalFilteredNilmanifold M s e)
      (φ : L →ₗ⁅ℚ⁆ M) {p : ℝ}, 0 ≤ p → D.GeometryComplexityLE p → E.GeometryComplexityLE p →
      (∀ i j, rationalLogHeight (E.basis.repr (φ (D.basis j)) i) ≤ p) →
      (E.realLattice ⊓ (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
          (hM := E.filtration.lowerCentralSeries_eq_bot) φ).range ≤
        D.realLattice.map (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
          (hM := E.filtration.lowerCentralSeries_eq_bot) φ)) →
      ∀ (u : D.Space → ℂ) (ℓ : ℝ≥0), (ℓ : ℝ) ≤ Real.exp p →
      (letI := D.metricSpace; LipschitzWith ℓ u) → (∀ x, ‖u x‖ ≤ 1) →
      (∀ k ∈ (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
          (hM := E.filtration.lowerCentralSeries_eq_bot) φ).ker, ∀ x,
        u (QuotientGroup.mk (k * x)) = u (QuotientGroup.mk x)) →
      ∃ (v : E.Space → ℂ) (K : ℝ≥0),
        (K : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ (letI := E.metricSpace; LipschitzWith K v) ∧
        (∀ y, ‖v y‖ ≤ 2) ∧
        ∀ x, v (QuotientGroup.mk (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
          (hM := E.filtration.lowerCentralSeries_eq_bot) φ x)) = u (QuotientGroup.mk x) := by
  obtain ⟨c, _, hrec⟩ := exists_controlled_rational_image_reconstruction s
  let P : Polynomial ℕ := (Polynomial.X + 1 + Polynomial.C c) ^ c
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro L M _ _ _ _ _ _ _ _ _ _ _ _ d e D E φ p hp hD hE hφ hcover u ℓ hℓ hu hub hker
  have ht : 0 ≤ p + 1 := by linarith
  have hpt : p ≤ p + 1 := by linarith
  have hexp : Real.exp p ≤ Real.exp (p + 1) := Real.exp_le_exp.mpr hpt
  obtain ⟨v, K, hK, hv, hb, heval⟩ := hrec D.filtration.lowerCentralSeries_eq_bot
    E.filtration.lowerCentralSeries_eq_bot D.basis E.basis φ D.lattice E.lattice
    D.grid E.grid ⌈Real.exp p⌉₊ D.grid_pos E.grid_pos (one_le_ceil_exp p)
    D.outer_grid E.inner_grid E.outer_grid
    (fun i j k => rationalHeightLE_ceil_exp (hD.2.2.1 i j k))
    (fun i j k => rationalHeightLE_ceil_exp (hE.2.2.1 i j k))
    (fun i j => rationalHeightLE_ceil_exp (hφ i j)) hcover u hker ℓ 1 hu hub
    (p + 1) ht
    (by simpa only [Fintype.card_fin] using hD.1.trans hpt)
    (by simpa only [Fintype.card_fin] using hE.1.trans hpt)
    (ceil_exp_le_exp_add_one hp) (hE.2.1.trans hexp) (hℓ.trans hexp)
    (by simpa only [NNReal.coe_one] using Real.one_le_exp ht)
  have hcost : (p + 1 + c) ^ c ≤ (p + C) ^ C := by
    simpa [P, Polynomial.eval₂_pow] using hbudget p hp
  exact ⟨v, K, hK.trans (Real.exp_le_exp.mpr hcost), hv,
    fun y => by simpa only [NNReal.coe_one, mul_one] using hb y, heval⟩

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.LogCharacterBudget
namespace OAI

section

namespace Erdos3

open scoped NNReal

theorem exists_logCharacterMetricConstant_exp_bound (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (d H : ℕ) (A : ℝ≥0) (p : ℝ),
      0 ≤ p → (d : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p → (A : ℝ) ≤ Real.exp p →
      ((2 * logCharacterMetricConstant s d H A : ℝ≥0) : ℝ) ≤ Real.exp ((p + C) ^ C) := by
  obtain ⟨a, _, hbound⟩ := exists_bchInverseBoxConstant_exp_bound s 0
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hpoly⟩ := exists_natPolynomial_eval_budget (X + 11 + (X + Polynomial.C a) ^ a)
  refine ⟨C, hC, ?_⟩
  intro d H A p hp hd hH hA
  have hlog : (bchLogMetricConstant s d H 1 : ℝ) ≤ Real.exp ((p + a) ^ a) :=
    (show (bchLogMetricConstant s d H 1 : ℝ) ≤ bchInverseBoxConstant s d H 1 from
      bchLogMetricConstant_le_inverse s d H).trans
      (hbound d H 1 p hp hd hH (by simp only [NNReal.coe_one, pow_zero]; exact Real.one_le_exp zero_le_one))
  have hfront : 2 + (CircleFourier.characterLipConstant : ℝ) * A ≤ Real.exp (p + 10) := by
    have hpi : (CircleFourier.characterLipConstant : ℝ) ≤ 8 := by
      rw [CircleFourier.coe_characterLipConstant]
      linarith [Real.pi_lt_four]
    have hten : (10 : ℝ) ≤ Real.exp 10 := by linarith [Real.add_one_le_exp (10 : ℝ)]
    have hone := Real.one_le_exp hp
    rw [Real.exp_add]
    nlinarith [mul_le_mul_of_nonneg_right hpi A.coe_nonneg]
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hsmall : ((2 * logCharacterMetricConstant s d H A : ℝ≥0) : ℝ) ≤
      Real.exp (p + 11 + (p + a) ^ a) := by
    change 2 * ((2 + (CircleFourier.characterLipConstant : ℝ) * A) *
      (bchLogMetricConstant s d H 1 : ℝ)) ≤ _
    calc
      _ ≤ Real.exp 1 * (Real.exp (p + 10) * Real.exp ((p + a) ^ a)) :=
        mul_le_mul htwo (mul_le_mul hfront hlog (by positivity) (Real.exp_pos _).le)
          (by positivity) (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  apply hsmall.trans (Real.exp_le_exp.mpr ?_)
  simpa [X, Polynomial.eval₂_pow] using hpoly p hp

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeCentralSeed
namespace OAI

section

namespace Erdos3.NilpotentLieBCHGroup

open Module
open scoped NNReal

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [IsScalarTower ℚ ℝ L] [TopologicalSpace L] [IsTopologicalAddGroup L]
  [ContinuousSMul ℝ L] [T2Space L]
  {s H : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem exists_central_character_extension (e : Basis ι ℝ L) (c : ι → ι → ι → ℚ)
    (hstructure : ∀ i j k, algebraMap ℚ ℝ (c i j k) = e.repr ⁅e i, e j⁆ k)
    (hc : ∀ i j k, RationalHeightLE (c i j k) H)
    (Γ T : Subgroup (NilpotentLieBCHGroup L s hnil))
    (hΓ : IsClosed (Γ : Set (NilpotentLieBCHGroup L s hnil)))
    (hT : ∀ z ∈ T, ∀ v : L, ⁅z.coord, v⁆ = 0)
    (η : L →ₗ[ℝ] ℝ) (A : ℝ≥0) (hη : ∀ x, |η x| ≤ A * ‖e.equivFun x‖)
    (hint : ∀ γ ∈ Γ, ∃ n : ℤ, η γ.coord = n) :
    letI := quotientMetricSpace e Γ hΓ
    ∃ f : NilpotentLieBCHGroup L s hnil ⧸ Γ → ℂ,
      LipschitzWith (2 * logCharacterMetricConstant s (Fintype.card ι) H A) f ∧
      (∀ z ∈ T, f (QuotientGroup.mk z) = logCharacter η z) ∧ ∀ x, ‖f x‖ ≤ 2 := by
  let := quotientMetricSpace e Γ hΓ
  obtain ⟨f, hf, heq, hbound⟩ := exists_complex_extension_along_map
    (fun z : T => (QuotientGroup.mk z.val : _ ⧸ Γ)) (fun z : T => logCharacter η z.val)
    (logCharacterMetricConstant s (Fintype.card ι) H A) 1
    (central_logCharacter_coset_dist_le e c hstructure hc Γ T hΓ hT η A hη hint)
    (fun z => (logCharacter_norm η z.val).le)
  exact ⟨f, hf, fun z hz => heq ⟨z, hz⟩, by simpa only [NNReal.coe_one, mul_one] using hbound⟩

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal

theorem exists_native_central_seed (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L : Type*} [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)] {d : ℕ}
      (D : RationalFilteredNilmanifold L s d) {p : ℝ},
      0 ≤ p → D.GeometryComplexityLE p → ∀ η : L →ₗ[ℚ] ℚ,
      (∀ i, rationalLogHeight (η (D.basis i)) ≤ p) →
      (∀ z : D.RealGroup, z ∈ D.realLattice → ∃ n : ℤ, realifyFunctional η z.coord = n) →
      ∃ K : ℝ≥0, (K : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
      ∃ f : D.Space → ℂ, (letI := D.metricSpace; LipschitzWith K f) ∧
        (∀ x, ‖f x‖ ≤ 2) ∧ ∀ z : D.RealGroup, z ∈ D.filtration.realification.subgroup s →
          f (QuotientGroup.mk z) = logCharacter (realifyFunctional η) z := by
  obtain ⟨a, _, hcost⟩ := exists_logCharacterMetricConstant_exp_bound s
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hpoly⟩ := exists_natPolynomial_eval_budget ((2 * X + 1 + Polynomial.C a) ^ a)
  refine ⟨C, hC, ?_⟩
  intro L _ _ _ _ _ _ d D p hp hD η hη hint
  let := D.metricSpace
  let H := ⌈Real.exp p⌉₊
  let A : ℝ≥0 := d * H
  have hlinear (x : ℝ ⊗[ℚ] L) : |realifyFunctional η x| ≤
      A * ‖(D.basis.baseChange ℝ).equivFun x‖ := by
    have h := abs_linearMap_le_basis_bound (D.basis.baseChange ℝ) (realifyFunctional η)
      (H : ℝ≥0) (fun i => by
        simpa only [Basis.baseChange_apply, realifyFunctional_tmul, one_mul, NNReal.coe_natCast] using
          (rationalHeightLE_ceil_exp (hη i)).abs_real_le) x
    simpa only [Fintype.card_fin, A, NNReal.coe_mul, NNReal.coe_natCast] using h
  obtain ⟨f, hf, hseed, hnorm⟩ := exists_central_character_extension (D.basis.baseChange ℝ)
    (lieStructureConstants D.basis) (fun i j k => (realLieBasis_structure D.basis i j k).symm)
    (fun i j k => rationalHeightLE_ceil_exp (hD.2.2.1 i j k))
    D.realLattice (D.filtration.realification.subgroup s) D.realLattice_closed_discrete.1
    (fun z hz v => D.filtration.realification.top_layer_central hz v)
    (realifyFunctional η) A hlinear hint
  let K := 2 * logCharacterMetricConstant s d H A
  have hH : (H : ℝ) ≤ Real.exp (p + 1) := ceil_exp_le_exp_add_one hp
  have hA : (A : ℝ) ≤ Real.exp (2 * p + 1) := by
    have hd : (d : ℝ) ≤ Real.exp p := hD.1.trans (by linarith [Real.add_one_le_exp p])
    calc
      _ ≤ Real.exp p * Real.exp (p + 1) := mul_le_mul hd hH (Nat.cast_nonneg H) (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hK : (K : ℝ) ≤ Real.exp ((2 * p + 1 + a) ^ a) :=
    hcost d H A (2 * p + 1) (by positivity) (hD.1.trans (by linarith))
      (hH.trans (Real.exp_le_exp.mpr (by linarith))) hA
  have hpc : (2 * p + 1 + a) ^ a ≤ (p + C) ^ C := by
    simpa [X, Polynomial.eval₂_pow] using hpoly p hp
  refine ⟨K, hK.trans (Real.exp_le_exp.mpr hpc), f, ?_, hnorm, hseed⟩
  simp only [Fintype.card_fin] at hf
  convert hf using 1
  rfl

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CurrentLayerPreservation
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open NilpotentLieBCHGroup

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

theorem removal_adjoint_relation (a g c : F.Group) (x y : L)
    (hxy : x = dualAdjoint g y) :
    dualAdjoint a⁻¹ x = dualAdjoint (a⁻¹ * g * c⁻¹) (dualAdjoint c y) := by
  rw [dualAdjoint_mul, dualAdjoint_mul, dualAdjoint_inv_cancel, hxy]

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3

open Module

namespace NilpotentLieFiltration

open NilpotentLieBCHGroup
open scoped TensorProduct

variable {ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (w : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ w i}))

include hlayers in
theorem real_current_bracket_remainder (V : Submodule ℝ (ℝ ⊗[ℚ] L)) (j : ℕ)
    (x k : ℝ ⊗[ℚ] L) (hk : k ∈ F.realification.layer 1)
    (hlower : ∀ d < j, ⁅basisGradeProjection (b.baseChange ℝ) w d x, k⁆ ∈ V) :
    ⁅x - basisGradeProjection (b.baseChange ℝ) w j x, k⁆ ∈
      V ⊔ (F.realLayer (j + 2)).toSubmodule := by
  have hlow : ⁅basisBelowProjection (b.baseChange ℝ) w j x, k⁆ ∈ V := by
    rw [basisBelowProjection_eq_sum_grades, sum_lie]
    exact V.sum_mem (fun d hd => hlower d (Finset.mem_range.mp hd))
  have hhigh : ⁅x - basisBelowProjection (b.baseChange ℝ) w (j + 1) x, k⁆ ∈
      F.realification.layer (j + 2) := by
    have h := F.realification.lie_mem (i := j + 1) (j := 1)
      (F.sub_realGradeTruncation_mem b w hlayers (j + 1) x) hk
    simpa only [Nat.add_assoc] using h
  have h := (V ⊔ (F.realLayer (j + 2)).toSubmodule).add_mem
    (Submodule.mem_sup_right hhigh) (Submodule.mem_sup_left hlow)
  rw [basisBelowProjection_succ, sub_lie, add_lie] at h
  convert h using 1
  rw [sub_lie]
  abel

end NilpotentLieFiltration
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.JoinedFrequencyQuotientInjectivity
namespace OAI

section

namespace Erdos3

theorem rationalLogHeight_nat_inv_mul (n : ℕ) (hn : 0 < n) {x : ℚ} {p : ℝ}
    (hx : rationalLogHeight x ≤ p) : rationalLogHeight ((n : ℚ)⁻¹ * x) ≤ p + n + 1 := by
  have hp : 0 ≤ p := (rationalLogHeight_nonneg x).trans hx
  have hnheight : RationalHeightLE (n : ℚ) (n + 1) := by simp [RationalHeightLE]
  have hinv := hnheight.inv (by exact_mod_cast hn.ne')
  apply rationalLogHeight_le_of_height (hinv.mul (rationalHeightLE_ceil_exp hx))
  calc
    (((n + 1) * ⌈Real.exp p⌉₊ : ℕ) : ℝ) = ((n : ℝ) + 1) * (⌈Real.exp p⌉₊ : ℝ) := by push_cast; rfl
    _ ≤ Real.exp (n : ℝ) * Real.exp (p + 1) :=
      mul_le_mul (Real.add_one_le_exp _) (ceil_exp_le_exp_add_one hp)
        (Nat.cast_nonneg _) (Real.exp_pos _).le
    _ = Real.exp (p + n + 1) := by rw [← Real.exp_add]; congr 1; ring

variable {L : Type*} [AddCommGroup L] [Module ℚ L]

theorem dividedFrequency_height (n : ℕ) (hn : 0 < n) (η : L →ₗ[ℚ] ℚ)
    {p : ℝ} (x : L) (hx : rationalLogHeight (η x) ≤ p) :
    rationalLogHeight (dividedFrequency n η x) ≤ p + n + 1 :=
  rationalLogHeight_nat_inv_mul n hn hx

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.HorizontalCoordinateBounds
namespace OAI

section

namespace Erdos3

open Module
open scoped TensorProduct

variable {ι κ : Type*} [Fintype ι]

theorem realFourCoordinateEquiv_tmul (a : ℝ) (x : Fin 4 → ι → ℚ) (j : Σ _ : Fin 4, ι) :
    DegreeRankLieFiltration.realFourCoordinateEquiv (a ⊗ₜ[ℚ] x) j = a * (x j.1 j.2 : ℝ) := by
  change ((Pi.basis (fun _ : Fin 4 => Pi.basisFun ℚ ι)).baseChange ℝ).repr
    (a ⊗ₜ[ℚ] x) j = _
  rw [Basis.baseChange_repr_tmul, Pi.basis_repr]
  change (x j.1 j.2) • a = _
  simp only [Rat.smul_def, mul_comm]

noncomputable def realFourCoordinateSpan (J : Submodule ℚ (Fin 4 → ι → ℚ)) :
    Submodule ℝ ((Σ _ : Fin 4, ι) → ℝ) :=
  (J.baseChange ℝ).map DegreeRankLieFiltration.realFourCoordinateEquiv.toLinearMap

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.RealSubspaceCoordinateRetraction
namespace OAI

section

namespace Erdos3

open Module
open scoped TensorProduct

variable {ι κ V W E : Type*} [AddCommGroup V] [Module ℚ V]
  [AddCommGroup W] [Module ℚ W] [AddCommGroup E] [Module ℝ E]

theorem scalarExtension_grid_of_height_one [Fintype ι] [Fintype κ]
    (e : Basis ι ℚ V) (f : Basis κ ℚ W) (q : V →ₗ[ℚ] W)
    (hq : ∀ i j, RationalHeightLE (f.repr (q (e j)) i) 1)
    (l : ℕ) (x : ℝ ⊗[ℚ] V)
    (hx : (fun i => (e.baseChange ℝ).repr x i) ∈ realDenominatorGrid l) :
    (fun i => (f.baseChange ℝ).repr (q.baseChange ℝ x) i) ∈ realDenominatorGrid l := by
  classical
  let D := LinearMap.toMatrix e f q
  have hD : LinearMap.toMatrix (e.baseChange ℝ) (f.baseChange ℝ) (q.baseChange ℝ) =
      D.map (Rat.castHom ℝ) := by
    ext i j
    simp only [D, LinearMap.toMatrix_apply, Matrix.map_apply,
      scalarExtension_basis_coordinates, Rat.coe_castHom]
  have hden : matrixDenominator D = 1 := by
    apply Nat.le_antisymm
    · have hb : ∀ i j, RationalHeightLE (D i j) 1 := by
        simpa only [D, LinearMap.toMatrix_apply] using hq
      simpa using matrixDenominator_le D hb
    · exact matrixDenominator_pos D
  have h := rational_coordinate_map_grid (e.baseChange ℝ) (f.baseChange ℝ)
    (q.baseChange ℝ) D hD l x hx
  simpa only [hden, one_mul, Basis.equivFun_apply] using h

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.NiltestAffineProjection
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open Module VectorPolynomial
open scoped TensorProduct BigOperators

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}

theorem mean_translate_box [Fintype σ] [DecidableEq σ]
    (T : D.Niltest w) (hw : ∀ i, 0 < w i) (a : σ → ℤ) (N : σ → ℕ) :
    (𝔼 x ∈ integerBox N, (T.translate hw a).eval x) =
      𝔼 x ∈ translatedIntegerBox a N, T.eval x := by
  rw [translatedIntegerBox, translateSupport,
    Finset.expect_image (add_right_injective a).injOn]
  apply Finset.expect_congr rfl
  intro x _
  rw [T.eval_translate, add_comm]

end Erdos3.RationalFilteredNilmanifold.Niltest

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.StepDropTerminalContainment
namespace OAI

section

namespace Erdos3

open Module

variable {R L ι : Type*} [Field R] [LieRing L] [LieAlgebra R L]

theorem basisGradeProjection_one_lie_eq_zero [Fintype ι]
    (b : Basis ι R L) (w : ι → ℕ) (hw : ∀ i, 0 < w i)
    (hgraded : BasisHomogeneousBrackets b w) (x y : L) :
    basisGradeProjection b w 1 ⁅x, y⁆ = 0 := by
  classical
  have hb (i j : ι) : basisGradeProjection b w 1 ⁅b i, b j⁆ = 0 := by
    apply b.repr.injective
    ext k
    simp only [basisGradeProjection_repr, map_zero, Finsupp.zero_apply]
    split_ifs with hk
    · exact hgraded i j k (by have := hw i; have := hw j; omega)
    · rfl
  rw [← b.sum_repr x, ← b.sum_repr y]
  simp only [sum_lie_sum, smul_lie, lie_smul, map_sum, map_smul, hb, smul_zero,
    Finset.sum_const_zero]

theorem stepDropSubmodule_lie_mem [Fintype ι]
    (b : Basis ι R L) (w : ι → ℕ) (hw : ∀ i, 0 < w i)
    (hgraded : BasisHomogeneousBrackets b w) (U : LieSubalgebra R L) (V K : Submodule R L)
    (hU : BasisGradedSubmodule b w U.toSubmodule)
    (hUV : ∀ u ∈ U, ∀ v ∈ V, ⁅u, v⁆ ∈ V)
    {x y : L} (hx : x ∈ stepDropSubmodule b w U V K) (hy : y ∈ stepDropSubmodule b w U V K) :
    ⁅x, y⁆ ∈ stepDropSubmodule b w U V K := by
  obtain ⟨hxU, _, hxbr, hxV⟩ := (mem_stepDropSubmodule b w U V K x).mp hx
  obtain ⟨hyU, hyK, _, hyV⟩ := (mem_stepDropSubmodule b w U V K y).mp hy
  have hbr : ⁅x, y⁆ ∈ V := by
    have h₁ := hxbr (basisGradeProjection b w 1 y) hyK
    have h₂ := hUV _ (hU 1 x hxU) _ hyV
    have h₃ : ⁅x - basisGradeProjection b w 1 x, y⁆ ∈ V := by
      rw [← lie_skew]
      exact V.neg_mem (hUV y hyU _ hxV)
    have he : ⁅x, y⁆ =
        ⁅basisGradeProjection b w 1 x, basisGradeProjection b w 1 y⁆ +
        ⁅basisGradeProjection b w 1 x, y - basisGradeProjection b w 1 y⁆ +
        ⁅x - basisGradeProjection b w 1 x, y⁆ := by
      rw [lie_sub, sub_lie]
      abel
    rw [he]
    exact V.add_mem (V.add_mem h₁ h₂) h₃
  have hz := basisGradeProjection_one_lie_eq_zero b w hw hgraded x y
  apply (mem_stepDropSubmodule b w U V K _).mpr
  refine ⟨U.lie_mem hxU hyU, ?_, ?_, ?_⟩
  · rw [hz]
    exact K.zero_mem
  · intro k _
    rw [hz, zero_lie]
    exact V.zero_mem
  · rwa [hz, sub_zero]

noncomputable def stepDropSubalgebra [Fintype ι]
    (b : Basis ι R L) (w : ι → ℕ) (hw : ∀ i, 0 < w i)
    (hgraded : BasisHomogeneousBrackets b w) (U : LieSubalgebra R L) (V K : Submodule R L)
    (hU : BasisGradedSubmodule b w U.toSubmodule)
    (hUV : ∀ u ∈ U, ∀ v ∈ V, ⁅u, v⁆ ∈ V) : LieSubalgebra R L :=
  { stepDropSubmodule b w U V K with
    lie_mem' := stepDropSubmodule_lie_mem b w hw hgraded U V K hU hUV }

theorem stepDropSubmodule_graded (b : Basis ι R L) (w : ι → ℕ)
    (U : LieSubalgebra R L) (V K : Submodule R L)
    (hU : BasisGradedSubmodule b w U.toSubmodule) (hV : BasisGradedSubmodule b w V) :
    BasisGradedSubmodule b w (stepDropSubmodule b w U V K) := by
  intro j x hx
  obtain ⟨hxU, hxK, hxbr, hxV⟩ := (mem_stepDropSubmodule b w U V K x).mp hx
  apply (mem_stepDropSubmodule b w U V K _).mpr
  by_cases hj : j = 1
  · subst j
    have hi := basisCoordinateProjection_idempotent b {i | w i = 1} x
    refine ⟨hU 1 x hxU, ?_, ?_, ?_⟩
    · simpa only [basisGradeProjection, hi] using hxK
    · intro k hk
      simpa only [basisGradeProjection, hi] using hxbr k hk
    · rw [show basisGradeProjection b w 1 (basisGradeProjection b w 1 x) =
        basisGradeProjection b w 1 x from hi, sub_self]
      exact V.zero_mem
  · have hz := basisGradeProjection_other b w (Ne.symm hj) x
    have hback := basisGradeProjection_other b w hj x
    have hv := hV j _ hxV
    rw [map_sub, hback, sub_zero] at hv
    refine ⟨hU j x hxU, ?_, ?_, ?_⟩
    · rw [hz]
      exact K.zero_mem
    · intro k _
      rw [hz, zero_lie]
      exact V.zero_mem
    · rwa [hz, sub_zero]

theorem stepDropSubmodule_mem_higher_grade (b : Basis ι R L) (w : ι → ℕ)
    (U : LieSubalgebra R L) (V K : Submodule R L) {j : ℕ} (hj : j ≠ 1)
    {x : L} (hx : basisGradeProjection b w j x = x) :
    x ∈ stepDropSubmodule b w U V K ↔ x ∈ U ∧ x ∈ V := by
  have hz : basisGradeProjection b w 1 x = 0 := by
    rw [← hx]
    exact basisGradeProjection_other b w (Ne.symm hj) x
  rw [mem_stepDropSubmodule]
  constructor
  · rintro ⟨hU, _, _, hV⟩
    exact ⟨hU, by simpa only [hz, sub_zero] using hV⟩
  · rintro ⟨hU, hV⟩
    refine ⟨hU, ?_, ?_, ?_⟩
    · rw [hz]
      exact K.zero_mem
    · intro k _
      rw [hz, zero_lie]
      exact V.zero_mem
    · rwa [hz, sub_zero]

end Erdos3

end

section

namespace Erdos3

open Module
open scoped TensorProduct

variable {R L μ : Type*} [Field R] [AddCommGroup L] [Module R L]

theorem mem_homogeneousIntersection (b : Basis μ R L) (w : μ → ℕ) (j : ℕ)
    (U V : Submodule R L) (x : L) :
    x ∈ homogeneousIntersection b w j U V ↔
      x ∈ U ∧ x ∈ V ∧ basisGradeProjection b w j x = x := by
  simp only [homogeneousIntersection, Submodule.mem_inf, LinearMap.mem_ker,
    LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]

theorem homogeneousIntersection_finrank_le [Fintype μ]
    (b : Basis μ R L) (w : μ → ℕ) (j : ℕ) (U V : Submodule R L) :
    Module.finrank R (homogeneousIntersection b w j U V) ≤ Fintype.card μ := by
  let : FiniteDimensional R L := b.finiteDimensional_of_finite
  have h := LinearMap.finrank_le_finrank_of_injective
    (f := (homogeneousIntersection b w j U V).subtype) (fun _ _ h => Subtype.ext h)
  simpa only [Module.finrank_eq_card_basis b] using h

end Erdos3

end

section

namespace Erdos3

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

theorem stepDropSubmodule_top_frequency
    {R L ι : Type*} [Field R] [LieRing L] [LieAlgebra R L]
    (b : Basis ι R L) (w : ι → ℕ) (U : LieSubalgebra R L) (V K : Submodule R L)
    (hU : BasisGradedSubmodule b w U.toSubmodule) (hV : BasisGradedSubmodule b w V)
    (η : L →ₗ[R] R) {s : ℕ} (hs : 2 ≤ s)
    (hη : ∀ x ∈ V, basisGradeProjection b w s x = x → η x = 0)
    {x : L} (hx : x ∈ stepDropSubmodule b w U V K) :
    η (basisGradeProjection b w s x) = 0 := by
  have hmem := stepDropSubmodule_graded b w U V K hU hV s x hx
  have hpure : basisGradeProjection b w s (basisGradeProjection b w s x) =
      basisGradeProjection b w s x := basisCoordinateProjection_idempotent b {i | w i = s} x
  exact hη _ ((stepDropSubmodule_mem_higher_grade b w U V K (by omega) hpure).mp hmem).2 hpure

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RankQuotientHeightBudget
namespace OAI

section

namespace Erdos3

open Module

variable {ν L : Type*} [AddCommGroup L] [Module ℚ L] [FiniteDimensional ℚ L]
  (e : Basis ν ℚ L) (H : ℕ)

theorem chosenBoundedSubmoduleBasis_height (U : Submodule ℚ L)
    (h : ∃ b : Basis (Fin (finrank ℚ U)) ℚ U,
      ∀ j k, RationalHeightLE (e.repr (b j).val k) H) (j k) :
    RationalHeightLE (e.repr (chosenBoundedSubmoduleBasis e H U j).val k) H := by
  classical
  unfold chosenBoundedSubmoduleBasis
  rw [dif_pos h]
  exact h.choose_spec j k

end Erdos3

end

section

namespace Erdos3

open Module

variable {ν L : Type*} [AddCommGroup L] [Module ℚ L] [FiniteDimensional ℚ L]

theorem chosenBasis_smul_coordinate_height (e : Basis ν ℚ L) (H : ℕ)
    (U V : Submodule ℚ L) (hUV : U = V)
    (j : Fin (finrank ℚ U)) (v : V) (q : ℚ) {K : ℕ}
    (hq : RationalHeightLE q K)
    (hv : v.val = q • (chosenBoundedSubmoduleBasis e H U j).val)
    (k : Fin (finrank ℚ V)) :
    RationalHeightLE ((chosenBoundedSubmoduleBasis e H V).repr v k) K := by
  subst V
  have he : v = q • chosenBoundedSubmoduleBasis e H U j := Subtype.ext hv
  rw [he, map_smul, Finsupp.smul_apply, smul_eq_mul]
  have hb : RationalHeightLE ((chosenBoundedSubmoduleBasis e H U).repr
      (chosenBoundedSubmoduleBasis e H U j) k) 1 := by
    classical
    rw [Basis.repr_self]
    by_cases hkj : k = j <;> simp [hkj, RationalHeightLE]
  simpa only [Nat.mul_one] using hq.mul hb

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeSquarefreeCoefficientBases
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open Module

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s d : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  (M : D.MultidegreeStructure bound)

theorem exists_squarefree_coefficient_basis (a : SquarefreeIndex (ReplicatedIndex bound))
    {p : ℝ} (hM : M.ComplexityLE p) :
    ∃ b : Basis (Fin (finrank ℚ
        (M.filtration.squarefreeCoefficientLayer (fun j : ReplicatedIndex bound => j.1) a))) ℚ
        (M.filtration.squarefreeCoefficientLayer (fun j : ReplicatedIndex bound => j.1) a),
      ∀ j k, RationalHeightLE (D.basis.repr (b j).val k) ⌈Real.exp p⌉₊ := by
  classical
  let : FiniteDimensional ℚ L := D.basis.finiteDimensional_of_finite
  by_cases ha : a.val = 0
  · have hU : M.filtration.squarefreeCoefficientLayer (fun j : ReplicatedIndex bound => j.1) a = ⊥ := by
      simp only [MultidegreeLieFiltration.squarefreeCoefficientLayer, ha, ite_true]
    rw [hU]
    refine ⟨Module.finBasis ℚ (⊥ : Submodule ℚ L), ?_⟩
    intro j k
    have hz : (Module.finBasis ℚ (⊥ : Submodule ℚ L) j).val = 0 :=
      (Module.finBasis ℚ (⊥ : Submodule ℚ L) j).property
    rw [hz, map_zero, Finsupp.zero_apply]
    exact rationalHeightLE_zero (one_le_ceil_exp p)
  · have hU : M.filtration.squarefreeCoefficientLayer (fun j : ReplicatedIndex bound => j.1) a =
        M.filtration.layer (blockDegree (fun j : ReplicatedIndex bound => j.1) a.val) := by
      simp only [MultidegreeLieFiltration.squarefreeCoefficientLayer, ha, ite_false]
    rw [hU]
    obtain ⟨b, hb⟩ := M.exists_layer_basis _ (replicated_blockDegree_le bound a) hM
    exact ⟨b, fun j k => rationalHeightLE_ceil_exp (hb j k)⟩

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.ComparisonChosenLayerBasis
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open Module
open scoped BigOperators

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s d : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  (M : D.MultidegreeStructure bound)

theorem squarefreeCoefficientBasis_card_le (a : SquarefreeIndex (ReplicatedIndex bound)) :
    finrank ℚ (M.filtration.squarefreeCoefficientLayer (fun j : ReplicatedIndex bound => j.1) a) ≤ d := by
  let : FiniteDimensional ℚ L := D.basis.finiteDimensional_of_finite
  simpa only [finrank_eq_card_basis D.basis, Fintype.card_fin] using
    (M.filtration.squarefreeCoefficientLayer (fun j : ReplicatedIndex bound => j.1) a).finrank_le

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open Module

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s d : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  (M : D.MultidegreeStructure bound)

noncomputable def comparisonLayerBasis (p : ℝ) (a : σ → ℕ) :
    Basis (Fin (finrank ℚ (M.filtration.layer a))) ℚ (M.filtration.layer a) := by
  letI : FiniteDimensional ℚ L := D.basis.finiteDimensional_of_finite
  exact chosenBoundedSubmoduleBasis D.basis ⌈Real.exp p⌉₊ _

theorem comparisonLayerBasis_height {p : ℝ} (hM : M.ComplexityLE p)
    (a : σ → ℕ) (ha : a ≤ bound) (j k) :
    RationalHeightLE (D.basis.repr (M.comparisonLayerBasis p a j).val k) ⌈Real.exp p⌉₊ := by
  let : FiniteDimensional ℚ L := D.basis.finiteDimensional_of_finite
  apply chosenBoundedSubmoduleBasis_height
  obtain ⟨b, hb⟩ := M.exists_layer_basis a ha hM
  exact ⟨b, fun j k => rationalHeightLE_ceil_exp (hb j k)⟩

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.SymbolRepresentativeTransport
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι κ M : Type*} [Fintype ι] [Fintype κ] [LieRing M] [LieAlgebra ℚ M] {s : ℕ}
  (F : NilpotentLieFiltration M s) (b : Basis ι ℚ M) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})) (e : Basis κ ℚ M)

theorem realSymbolRepresentative_original_grid (w : σ → ℕ) (l : ℕ)
    (R : F.RealPolynomialSymbolGroup w) (hR : F.SymbolRationalGrid b ω hF w l R)
    (α : σ →₀ ℕ) :
    (fun i => (e.baseChange ℝ).repr (coefficients (F.realSymbolRepresentative b ω hF w R.coord) α) i)
      ∈ realDenominatorGrid (matrixDenominator (fun i j => e.repr (b j) i) * l) := by
  obtain ⟨z, hz⟩ := F.realSymbolRepresentative_rational_coefficients b ω hF w l R hR
  apply real_basis_coordinates_grid b e l
  exact ⟨fun j => z (α, j), funext (fun j => congrFun hz (α, j))⟩

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.ControlledReplicatedFrequency
namespace OAI

section

namespace Erdos3

theorem exists_squarefreeFrequency_cost (t : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p → squarefreeFrequencyModelBudget t p ≤ (p + C) ^ C := by
  let X : Polynomial ℕ := Polynomial.X
  let K := bchIntegralDenominatorBound t + 5
  let A := Polynomial.C (2 ^ t) * X + (X + 3) ^ 8 + Polynomial.C (2 ^ t) * (X + 3) ^ 5
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget (A + (A + Polynomial.C K) ^ K)
  refine ⟨C, hC, ?_⟩
  intro p hp
  simpa [X, K, A, squarefreeFrequencyModelBudget, squarefreeFrequencyInputBudget,
    squarefreeInputBudget, replicatedFrequencyDenominatorBudget, Polynomial.eval₂_pow] using hbound p hp

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CommonRefilteredFactorization
namespace OAI

section

namespace Erdos3

open Module
open scoped BigOperators

theorem exists_intersection_spanning_logHeight {ι κ J V : Type*}
    [Fintype ι] [Fintype κ] [Fintype J] [LieRing V] [LieAlgebra ℚ V]
    (b : Basis ι ℚ V) (U : J → LieSubalgebra ℚ V) (v : J → κ → V)
    (hv : ∀ j, Submodule.span ℚ (Set.range (v j)) = (U j).toSubmodule)
    {p : ℝ} (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p)
    (hκ : (Fintype.card κ : ℝ) ≤ p) (hJ : (Fintype.card J : ℝ) ≤ p)
    (hheight : ∀ j a i, rationalLogHeight (b.repr (v j a) i) ≤ p) :
    ∃ w : Fin (Fintype.card ι) → V,
      Submodule.span ℚ (Set.range w) = (⨅ j, U j).toSubmodule ∧
      ∀ a i, rationalLogHeight (b.repr (w a) i) ≤ ((p + 2) ^ 2 + 2) ^ 63 + 1 := by
  classical
  let A : J → Matrix ι κ ℚ := fun j i k => b.equivFun (v j k) i
  let W := ⨅ j, U j
  let Wc : Submodule ℚ (ι → ℚ) := ⨅ j, LinearMap.range (A j).mulVecLin
  have hA (j : J) : LinearMap.range (A j).mulVecLin = (U j).toSubmodule.map b.equivFun.toLinearMap :=
    coordinate_spanning_range b (v j) (U j).toSubmodule (hv j)
  have hmem (x : V) : b.equivFun x ∈ Wc ↔ x ∈ W := by
    constructor
    · intro hx
      simp only [Wc, Submodule.mem_iInf] at hx
      apply (lieSubalgebra_mem_iInf U x).mpr
      intro j
      have hxj := hx j
      rw [hA j] at hxj
      obtain ⟨y, hy, he⟩ := hxj
      have he' : y = x := b.equivFun.injective he
      exact he' ▸ hy
    · intro hx
      simp only [Wc, Submodule.mem_iInf]
      intro j
      rw [hA j]
      exact ⟨x, (lieSubalgebra_mem_iInf U x).mp hx j, rfl⟩
  let e : W ≃ₗ[ℚ] Wc :=
    { toFun := fun x => ⟨b.equivFun x, (hmem x).mpr x.property⟩
      invFun := fun x => ⟨b.equivFun.symm x, (hmem _).mp (by
        simpa only [LinearEquiv.apply_symm_apply] using x.property)⟩
      map_add' := fun x y => Subtype.ext (b.equivFun.map_add x y)
      map_smul' := fun c x => Subtype.ext (b.equivFun.map_smul c x)
      left_inv := fun x => Subtype.ext (b.equivFun.symm_apply_apply x)
      right_inv := fun x => Subtype.ext (b.equivFun.apply_symm_apply x) }
  let q := (p + 2) ^ 2
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hpq : p ≤ q := by dsimp [q]; nlinarith [sq_nonneg p]
  have hp1q : p + 1 ≤ q := by dsimp [q]; nlinarith [sq_nonneg p]
  have hcols : ((∑ _j : J, Fintype.card κ : ℕ) : ℝ) ≤ q := by
    simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, Nat.cast_mul]
    have hprod := mul_le_mul hJ hκ (Nat.cast_nonneg _) hp
    dsimp [q]
    nlinarith
  obtain ⟨bc, hbc⟩ := exists_image_intersection_basis_exp_height A (one_le_ceil_exp p)
    (fun j i k => rationalHeightLE_ceil_exp (hheight j k i)) hq
    (hJ.trans hpq) (hι.trans hpq) hcols
    ((ceil_exp_le_exp_add_one hp).trans (Real.exp_le_exp.mpr hp1q))
  let bw := bc.map e.symm
  let H := ⌈Real.exp ((q + 2) ^ 63)⌉₊
  have hH : 1 ≤ H := one_le_ceil_exp _
  have hbheight (a : Fin (finrank ℚ Wc)) (i : ι) : RationalHeightLE (b.repr (bw a : V) i) H := by
    have hb := rationalHeightLE_ceil_exp ((rationalLogHeight_le_iff _ _).mpr (hbc a i))
    change RationalHeightLE (b.repr (b.equivFun.symm (bc a : ι → ℚ)) i) H
    simpa only [← Basis.equivFun_apply, LinearEquiv.apply_symm_apply] using hb
  obtain ⟨w, hw, hh⟩ := exists_bounded_ambient_spanning b W bw bw.span_eq hH hbheight
  refine ⟨w, hw, ?_⟩
  intro a i
  exact rationalLogHeight_le_of_height (hh a i) (ceil_exp_le_exp_add_one (by positivity))

end Erdos3

end

section

namespace Erdos3

open Module

theorem exists_binary_intersection_basis_logHeight
    {ι α β L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
    (e : Basis ι ℚ L) (U V : LieSubalgebra ℚ L)
    (bU : Basis α ℚ U) (bV : Basis β ℚ V)
    {p : ℝ} (hp : 0 ≤ p) (hd : (Fintype.card ι : ℝ) ≤ p)
    (hU : ∀ a i, rationalLogHeight (e.repr (bU a : L) i) ≤ p)
    (hV : ∀ a i, rationalLogHeight (e.repr (bV a : L) i) ≤ p) :
    ∃ b : Basis (Fin (finrank ℚ (U ⊓ V : LieSubalgebra ℚ L))) ℚ
        (U ⊓ V : LieSubalgebra ℚ L),
      ∀ a i, rationalLogHeight (e.repr (b a : L) i) ≤ ((p + 4) ^ 2 + 2) ^ 63 + 2 := by
  classical
  obtain ⟨u, hu, hhu⟩ := exists_bounded_ambient_spanning e U bU bU.span_eq
    (one_le_ceil_exp p) (fun a i => rationalHeightLE_ceil_exp (hU a i))
  obtain ⟨v, hv, hhv⟩ := exists_bounded_ambient_spanning e V bV bV.span_eq
    (one_le_ceil_exp p) (fun a i => rationalHeightLE_ceil_exp (hV a i))
  let W : Bool → LieSubalgebra ℚ L := fun j => if j then U else V
  let z : Bool → Fin (Fintype.card ι) → L := fun j => if j then u else v
  have hz (j : Bool) : Submodule.span ℚ (Set.range (z j)) = (W j).toSubmodule := by
    cases j
    · exact hv
    · exact hu
  have hh (j : Bool) (a) (i) : rationalLogHeight (e.repr (z j a) i) ≤ p + 2 := by
    have hceil := ceil_exp_le_exp_add_one hp
    cases j
    · exact (rationalLogHeight_le_of_height (hhv a i) hceil).trans (by linarith)
    · exact (rationalLogHeight_le_of_height (hhu a i) hceil).trans (by linarith)
  obtain ⟨w, hw, hhw⟩ := exists_intersection_spanning_logHeight e W z hz
    (by linarith : 0 ≤ p + 2) (hd.trans (by linarith))
    (by simpa only [Fintype.card_fin] using hd.trans (show p ≤ p + 2 by linarith))
    (by simpa using (show (2 : ℝ) ≤ p + 2 by linarith)) hh
  have hW : (⨅ j, W j) = U ⊓ V := by
    ext x
    simp [lieSubalgebra_mem_iInf, W, Bool.forall_bool, and_comm]
  rw [hW] at hw
  obtain ⟨b, hb⟩ := exists_bounded_submodule_basis_from_spanning e
    (U ⊓ V).toSubmodule w hw (fun a i => rationalHeightLE_ceil_exp (hhw a i))
  refine ⟨b, fun a i => ?_⟩
  have h := rationalLogHeight_le_of_height (hb a i)
    (ceil_exp_le_exp_add_one (by positivity : 0 ≤ ((p + 2 + 2) ^ 2 + 2) ^ 63 + 1))
  simpa only [show p + 2 + 2 = p + 4 by ring, add_assoc, one_add_one_eq_two] using h

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.VerticalTranslations
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup CircleFourier

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  (D : RationalFilteredNilmanifold L s d)

theorem vertical_left_translate (F : D.Space → ℂ) (eta : L →ₗ[ℚ] ℚ)
    (hF : ∀ z, z ∈ D.filtration.realification.subgroup s → ∀ x,
      F (z • x) = character ((realifyFunctional eta z.coord : ℝ) : CircleFourier.Circle) * F x)
    (a : D.RealGroup) (z : D.RealGroup) (hz : z ∈ D.filtration.realification.subgroup s)
    (x : D.Space) :
    F (a • (z • x)) =
      character ((realifyFunctional eta z.coord : ℝ) : CircleFourier.Circle) * F (a • x) := by
  have hc : Commute z a := commute_of_lie_eq_zero z a
    (D.filtration.realification.top_layer_central hz a.coord)
  rw [← mul_smul, hc.eq.symm, mul_smul]
  exact hF z hz (a • x)

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.ControlledPositivePolynomialDownsets
namespace OAI

section

namespace Erdos3

theorem positivePolynomialDenominatorBudget_le_model (t : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    positivePolynomialDenominatorBudget t p ≤ positivePolynomialModelBudget t p := by
  have h := (positivePolynomialInputBudget_nonneg t hp).trans
    (positivePolynomialInputBudget_le_denominator t p)
  exact le_add_of_nonneg_right (pow_nonneg (add_nonneg h (Nat.cast_nonneg _)) _)

theorem exists_positivePolynomialModel_budget (t : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p →
      positivePolynomialModelBudget t p ≤ (p + C) ^ C := by
  let Q : Polynomial ℕ := Polynomial.X + 1 +
    (Polynomial.C (2 ^ t) * Polynomial.X + (Polynomial.X + 3) ^ 8)
  let R : Polynomial ℕ := Q + (Q + 2) ^ 4
  let K := bchIntegralDenominatorBound t + 5
  obtain ⟨C, hC, h⟩ := exists_natPolynomial_eval_budget (R + (R + Polynomial.C K) ^ K)
  refine ⟨C, hC, ?_⟩
  intro p hp
  simpa only [positivePolynomialModelBudget, positivePolynomialDenominatorBudget,
    positivePolynomialInputBudget, squarefreeInputBudget, R, Q, K,
    Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_pow,
    Polynomial.eval₂_X, Polynomial.eval₂_C, Polynomial.eval₂_one,
    Polynomial.eval₂_ofNat, map_pow, map_ofNat, Nat.coe_castRingHom] using h p hp

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.NativeTotalDegreeMultifiltration
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module
open scoped BigOperators

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  (D : RationalFilteredNilmanifold L s d)

theorem exists_totalDegree_layer_basis (n : ℕ) {p : ℝ} (hD : D.GeometryComplexityLE p) :
    ∃ b : Basis (Fin (finrank ℚ (D.filtration.layer n))) ℚ (D.filtration.layer n),
      ∀ j k, rationalLogHeight (D.basis.repr (b j : L) k) ≤ p := by
  by_cases hn : n = 0
  · subst n
    have hzero : D.filtration.layer 0 = D.filtration.layer 1 :=
      D.filtration.totalDegree_zero_layer.trans D.filtration.one_eq_top.symm
    rw [hzero]
    exact D.exists_positive_layer_basis 1 le_rfl hD
  · exact D.exists_positive_layer_basis n (by omega) hD

noncomputable def totalDegreeMultidegree (σ : Type*) [Fintype σ] [Nonempty σ]
    {p : ℝ} (hD : D.GeometryComplexityLE p) : D.MultidegreeStructure (fun _ : σ => s) where
  filtration := D.filtration.totalDegreeMultifiltration σ
  ordinary := rfl
  basis a := Classical.choose (D.exists_totalDegree_layer_basis (∑ i, (a i).val) hD)

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.HomogeneousSubspaceCorrections
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

variable {σ V : Type*} [Fintype σ] [AddCommGroup V] [Module ℚ V]

theorem reconstructDerivatives_coordinate_grid {ι : Type*} {d : ℕ} (hd : 0 < d)
    (f : V →ₗ[ℚ] (ι → ℝ)) (P : σ → VectorPolynomial σ ℚ V) (l : ℕ)
    (hP : ∀ i α, f (coefficients (P i) α) ∈ realDenominatorGrid l) (β : σ →₀ ℕ) :
    f (coefficients (reconstructDerivatives d P) β) ∈ realDenominatorGrid (l * d) := by
  classical
  let v : σ → ι → ℝ := fun i =>
    if i ∈ β.support then f (coefficients (P i) (β - Finsupp.single i 1)) else 0
  have hv (i : σ) : v i ∈ realDenominatorGrid l := by
    dsimp [v]
    split_ifs
    · exact hP i _
    · exact ⟨0, by ext j; simp⟩
  have hsum : (∑ i, v i) ∈ realDenominatorGrid l := by
    have h := realDenominatorGrid_linear_combination 1 l (fun _ : σ => (1 : ℝ)) v
      (by exact ⟨fun _ => 1, by ext i; simp⟩) hv
    simpa only [one_smul, Nat.mul_one] using h
  have hc : f (coefficients (reconstructDerivatives d P) β) = (d : ℝ)⁻¹ • ∑ i, v i := by
    rw [coefficients_reconstructDerivatives, map_smul, map_sum]
    simp only [apply_ite, map_zero]
    change (d : ℚ)⁻¹ • (∑ i, v i) = (d : ℝ)⁻¹ • ∑ i, v i
    ext j
    simp [Pi.smul_apply, Rat.smul_def]
  rw [hc]
  exact realDenominatorGrid_div_nat l d hd _ hsum

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

open Module VectorPolynomial
open scoped Matrix TensorProduct

variable {L μ ι ν σ : Type*} [LieRing L] [LieAlgebra ℚ L]
  [Fintype μ] [Fintype ι] [Fintype ν] [Fintype σ] {E V : Submodule ℚ L}

theorem exists_homogeneous_subspace_corrections_from_derivatives
    (b : Basis μ ℚ L) (e : Basis ν ℚ E) (f : Basis ι ℚ (L ⧸ V))
    {H J l d : ℕ} (hH : 1 ≤ H) (hl : 0 < l) (hd : 0 < d)
    (hA : ∀ i n, RationalHeightLE (subspaceQuotientMatrix e f i n) H)
    (he : ∀ i j, RationalHeightLE (b.repr (e j : L) i) J)
    {p : ℝ} (hp : 0 ≤ p) (hrows : (Fintype.card ι : ℝ) ≤ p)
    (hcols : (Fintype.card ν : ℝ) ≤ p) (hHp : (H : ℝ) ≤ Real.exp p)
    (hlp : ((l * d : ℕ) : ℝ) ≤ Real.exp p)
    (T : σ → ℝ) (hT : ∀ i, Real.exp (separationBudget p) ≤ T i)
    (P : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (hPE : ∀ α, coefficients P α ∈ E.baseChange ℝ)
    (hP : ∀ α, Finsupp.weight (fun _ : σ => (1 : ℕ)) α ≠ d → coefficients P α = 0)
    (S R : σ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (hS : ∀ i α, Finsupp.weight (fun _ : σ => (1 : ℕ)) α ≠ d - 1 → coefficients (S i) α = 0)
    (hR : ∀ i α, Finsupp.weight (fun _ : σ => (1 : ℕ)) α ≠ d - 1 → coefficients (R i) α = 0)
    (hsplit : ∀ i α, coefficients
      ((MvPolynomial.pderiv i).toLinearMap.rTensor (ℝ ⊗[ℚ] L) P - S i - R i) α ∈ V.baseChange ℝ)
    {M : ℝ} (hM : 0 ≤ M) (hbudget : (Fintype.card σ : ℝ) / d * M ≤ Real.exp p)
    (hslow : ∀ i α n, |realQuotientCoordinateMap f (coefficients (S i) α) n| ≤
      M / (T i * monomialScale T α))
    (hrational : ∀ i α, realQuotientCoordinateMap f (coefficients (R i) α) ∈
      realDenominatorGrid l) :
    ∃ (m : ℕ) (A B : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)),
      0 < m ∧ (m : ℝ) ≤ Real.exp ((p + 2) ^ 36) ∧
      map ((realQuotientCoordinateMap f).restrictScalars ℚ) A =
        map ((realQuotientCoordinateMap f).restrictScalars ℚ) (reconstructDerivatives d S) ∧
      map ((realQuotientCoordinateMap f).restrictScalars ℚ) B =
        map ((realQuotientCoordinateMap f).restrictScalars ℚ) (reconstructDerivatives d R) ∧
      (∀ α, coefficients A α ∈ E.baseChange ℝ ∧ coefficients B α ∈ E.baseChange ℝ) ∧
      (∀ α, Finsupp.weight (fun _ : σ => (1 : ℕ)) α ≠ d → coefficients A α = 0) ∧
      (∀ α, Finsupp.weight (fun _ : σ => (1 : ℕ)) α ≠ d → coefficients B α = 0) ∧
      (∀ α, ‖(b.baseChange ℝ).equivFun (coefficients A α)‖ ≤
        (((Fintype.card ν : ℝ) + 1) * (J + 1)) *
          Real.exp ((p + 2) ^ 18 + p) / monomialScale T α) ∧
      (∀ α, (b.baseChange ℝ).equivFun (coefficients B α) ∈
        realDenominatorGrid (matrixDenominator (bracketLiftMatrix b e) * m)) ∧
      ∀ α, coefficients (P - A - B) α ∈ (E ⊓ V).baseChange ℝ := by
  have hTpos (i : σ) : 0 < T i := (Real.exp_pos _).trans_le (hT i)
  let q := (realQuotientCoordinateMap f).restrictScalars ℚ
  have hShom := reconstructDerivatives_homogeneous hd S hS
  have hRhom := reconstructDerivatives_homogeneous hd R hR
  have hS0 : coefficients (reconstructDerivatives d S) 0 = 0 :=
    hShom 0 (by simpa using Nat.ne_of_lt hd)
  have hR0 : coefficients (reconstructDerivatives d R) 0 = 0 :=
    hRhom 0 (by simpa using Nat.ne_of_lt hd)
  have hSnorm (α : σ →₀ ℕ) :
      ‖realQuotientCoordinateMap f (coefficients (reconstructDerivatives d S) α)‖ ≤
        Real.exp p / monomialScale T α := by
    apply (pi_norm_le_iff_of_nonneg (div_nonneg (Real.exp_nonneg _)
      (monomialScale_pos T hTpos α).le)).mpr
    intro n
    rw [Real.norm_eq_abs]
    have hbound := reconstructDerivatives_coordinate_bound hd ((LinearMap.proj n).comp q)
      S T hTpos hM (fun i β => hslow i β n) α
    exact hbound.trans (div_le_div_of_nonneg_right hbudget (monomialScale_pos T hTpos α).le)
  have hRgrid (α : σ →₀ ℕ) :
      realQuotientCoordinateMap f (coefficients (reconstructDerivatives d R) α) ∈
        realDenominatorGrid (l * d) :=
    reconstructDerivatives_coordinate_grid hd q R l hrational α
  have hres := homogeneous_derivative_split_mod ((V.baseChange ℝ).restrictScalars ℚ)
    hd P hP S R hsplit
  have h := exists_controlled_subspace_correction_polynomials b e f hH (Nat.mul_pos hl hd)
    hA he hp hrows hcols hHp hlp T hT P (reconstructDerivatives d S)
    (reconstructDerivatives d R) hPE hS0 hR0 hSnorm hRgrid hres
  obtain ⟨m, A, B, hm, hmp, hAQ, hBQ, hE, hAz, hBz, hAnorm, hBgrid, hresidual⟩ := h
  exact ⟨m, A, B, hm, hmp, hAQ, hBQ, hE,
    fun α hα => hAz α (hShom α hα), fun α hα => hBz α (hRhom α hα),
    hAnorm, hBgrid, hresidual⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CommonCoefficientFourAnnihilators
namespace OAI

section

namespace Erdos3

open Module

variable {R V ι κ : Type*} [Field R] [AddCommGroup V] [Module R V]

noncomputable def fourBasisVectors (D : Submodule R V) (b : Basis κ R D) :
    (Σ _ : Fin 4, κ) → (Fin 4 → V) :=
  (LinearMap.pi (fun k => D.subtype.comp (LinearMap.proj k))) ∘
    Pi.basis (fun _ : Fin 4 => b)

end Erdos3

end

end OAI
end


