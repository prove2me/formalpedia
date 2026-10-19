-- Prove2me | Definitions.Def_OAIE3v2B122
-- name    : OAIE3v2B122
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T11:10:35.602992+00:00
-- url     : https://prove2.me/theorems/086ec15a-ca97-4d83-a459-c5885da3cbad
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 124 of 311
-- statement:
--   Definitions bundle 124 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B101`, `OAIE3v2B102`, `OAIE3v2B104`, `OAIE3v2B106`, `OAIE3v2B107`, `OAIE3v2B108` of this split.
--
--   Modules: `Dynamics/MarkedEvaluationHeightBudget.lean`, `Dynamics/NativeHorizontalLiftBudget.lean`, `Estimates/CoefficientSliceEmbedding.lean`, `Estimates/CommonDependentIntegralModel.lean`, `Estimates/CommonInducedCorrelation.lean`, `Estimates/DescendedLinearMapBounds.lean`, `Estimates/ImageRepresentatives.lean`, `Estimates/RealSubspaceIntersectionCorrections.lean`, `Estimates/RealSymbolRepresentativeSplitting.lean`, `Geometry/MarkedLocalObservableMetric.lean`, `Geometry/RealSubspaceCoordinateRetraction.lean`, `Linear/ImageDefiningMatrix.lean`, `Linear/WeightedTranslationBasisHeight.lean`, `Nilpotent/BCHLatticeImageGap.lean`, `Nilpotent/BCHSmoothPartitionBudget.lean`, `Polynomial/TotalDegreeSplitDownsets.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B101
import Definitions.Def_OAIE3v2B102
import Definitions.Def_OAIE3v2B104
import Definitions.Def_OAIE3v2B106
import Definitions.Def_OAIE3v2B107
import Definitions.Def_OAIE3v2B108

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.BCHLatticeImageGap
namespace OAI

section

namespace Erdos3

open scoped NNReal

namespace NilpotentLieBCHGroup

open Module

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [IsScalarTower ℚ ℝ L] [TopologicalSpace L] [IsTopologicalAddGroup L]
  [ContinuousSMul ℝ L] [T2Space L]
  {s H : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem dist_coordinates_le_of_near_box
    (e : Basis ι ℝ L) (c : ι → ι → ι → ℚ)
    (hstructure : ∀ i j k, algebraMap ℚ ℝ (c i j k) = e.repr ⁅e i, e j⁆ k)
    (hc : ∀ i j k, RationalHeightLE (c i j k) H)
    (B : ℝ≥0) (hB : 1 ≤ B) (g h : NilpotentLieBCHGroup L s hnil)
    (hg : ∀ i, |e.repr g.coord i| ≤ B) :
    letI := rightMetricSpace (hnil := hnil) e
    let C := bchLogMetricConstant s (Fintype.card ι) H 1
    (C : ℝ) * dist g h < 1 →
      dist (basisHomeomorph e g) (basisHomeomorph e h) ≤
        bchBoxCoordinateBound s (Fintype.card ι) H B * C * dist g h := by
  let := rightMetricSpace (hnil := hnil) e
  let C := bchLogMetricConstant s (Fintype.card ι) H 1
  dsimp only
  intro hnear
  let z := h * g⁻¹
  have hdist : dist 1 z = dist g h := by
    simpa only [mul_inv_cancel] using (rightMetricSpace_isometry_mul_right e g⁻¹).dist_eq g h
  have hz : ‖basisHomeomorph e z‖ ≤ (C : ℝ) * dist g h := by
    have hn : (C : ℝ) * dist 1 z < (1 : ℝ≥0) := by simpa only [hdist, NNReal.coe_one] using hnear
    simpa only [hdist] using norm_coordinates_le_of_near_one e c hstructure hc 1 le_rfl z hn
  have hzbox (i) : |basisHomeomorph e z i| ≤ B := by
    have hi : |basisHomeomorph e z i| ≤ ‖basisHomeomorph e z‖ := by
      simpa only [Real.norm_eq_abs] using norm_le_pi_norm (basisHomeomorph e z) i
    exact ((hi.trans hz).trans hnear.le).trans hB
  have hzero : basisHomeomorph (hnil := hnil) e 1 = 0 := by
    simp only [basisHomeomorph_apply, coord_one, map_zero]
  have hRzero : rightTranslate e g 0 = basisHomeomorph e g := by
    rw [← hzero, rightTranslate_coordinates, one_mul]
  have hzg : z * g = h := by simp only [z, inv_mul_cancel_right]
  have hLip := (lipschitzOn_rightTranslate_box e c hstructure hc g B hB hg).dist_le_mul
    (basisHomeomorph e z) hzbox 0 (by
      intro i
      simpa only [Pi.zero_apply, abs_zero] using B.coe_nonneg)
  rw [rightTranslate_coordinates, hzg, hRzero, dist_zero_right] at hLip
  calc
    _ ≤ bchBoxCoordinateBound s (Fintype.card ι) H B * ‖basisHomeomorph e z‖ := by
      simpa only [dist_comm, NNReal.toReal] using hLip
    _ ≤ bchBoxCoordinateBound s (Fintype.card ι) H B * ((C : ℝ) * dist g h) :=
      mul_le_mul_of_nonneg_left hz (bchBoxCoordinateBound_nonneg s _ H B.coe_nonneg)
    _ = _ := by ring

end NilpotentLieBCHGroup
end Erdos3

end

section

namespace Erdos3.NilpotentLieBCHGroup

open Module
open scoped Matrix NNReal

variable {ι κ L : Type*} [Fintype ι] [Fintype κ]
  [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L] [IsScalarTower ℚ ℝ L]
  [TopologicalSpace L] [IsTopologicalAddGroup L] [ContinuousSMul ℝ L] [T2Space L]
  {s H : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem rational_kernel_of_near_bounded_point
    (e : Basis κ ℝ L) (c : κ → κ → κ → ℚ)
    (hstructure : ∀ i j k, algebraMap ℚ ℝ (c i j k) = e.repr ⁅e i, e j⁆ k)
    (hc : ∀ i j k, RationalHeightLE (c i j k) H)
    (Q : Matrix ι κ ℚ) (HQ B : ℝ≥0) (hB : 1 ≤ B)
    (hQ : ∀ i j, |(Q i j : ℝ)| ≤ HQ) (l : ℕ) (hl : 0 < l)
    (g γ : NilpotentLieBCHGroup L s hnil)
    (hg : ∀ i, |e.repr g.coord i| ≤ B)
    (hγ : basisHomeomorph e γ ∈ realDenominatorGrid l)
    (hkernel : (fun i j => (Q i j : ℝ)) *ᵥ basisHomeomorph e g = 0) :
    letI := rightMetricSpace (hnil := hnil) e
    let C := bchLogMetricConstant s (Fintype.card κ) H 1
    let A := bchBoxCoordinateBound s (Fintype.card κ) H B
    (C : ℝ) * dist g γ < 1 →
    ((matrixDenominator Q * l : ℕ) : ℝ) * (((Fintype.card κ : ℝ) + 1) * (HQ + 1)) *
      (A * C) * dist g γ < 1 →
    (fun i j => (Q i j : ℝ)) *ᵥ basisHomeomorph e γ = 0 := by
  let := rightMetricSpace (hnil := hnil) e
  dsimp only
  intro hnear hsmall
  apply rational_matrix_kernel_separation Q HQ hQ l hl (basisHomeomorph e γ) (basisHomeomorph e g)
    hγ hkernel
  have hcoord := dist_coordinates_le_of_near_box e c hstructure hc B hB g γ hg hnear
  rw [dist_comm] at hcoord
  calc
    _ ≤ ((matrixDenominator Q * l : ℕ) : ℝ) * (((Fintype.card κ : ℝ) + 1) * (HQ + 1)) *
        (bchBoxCoordinateBound s (Fintype.card κ) H B *
          (bchLogMetricConstant s (Fintype.card κ) H 1 : ℝ) * dist g γ) := by
      exact mul_le_mul_of_nonneg_left hcoord (by positivity)
    _ < 1 := by nlinarith [hsmall]

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3.NilpotentLieBCHGroup

open Module
open scoped Matrix NNReal

variable {ι κ L : Type*} [Fintype ι] [Fintype κ]
  [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L] [IsScalarTower ℚ ℝ L]
  [TopologicalSpace L] [IsTopologicalAddGroup L] [ContinuousSMul ℝ L] [T2Space L]
  {s H : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem lattice_translate_mem_of_small_dist
    (e : Basis κ ℝ L) (c : κ → κ → κ → ℚ)
    (hstructure : ∀ i j k, algebraMap ℚ ℝ (c i j k) = e.repr ⁅e i, e j⁆ k)
    (hc : ∀ i j k, RationalHeightLE (c i j k) H)
    (Q : Matrix ι κ ℚ) (HQ B K : ℝ≥0) (hB : 1 ≤ B)
    (hQ : ∀ i j, |(Q i j : ℝ)| ≤ HQ) (l : ℕ) (hl : 0 < l)
    (J : Subgroup (NilpotentLieBCHGroup L s hnil))
    (hJ : ∀ g, g ∈ J ↔ (fun i j => (Q i j : ℝ)) *ᵥ basisHomeomorph e g = 0)
    (x y γ : NilpotentLieBCHGroup L s hnil) (hx : x ∈ J) (hy : y ∈ J)
    (hγ : basisHomeomorph e γ ∈ realDenominatorGrid l)
    (hxy : ∀ i, |e.repr (y⁻¹ * x).coord i| ≤ B)
    (hleft : letI := rightMetricSpace (hnil := hnil) e; LipschitzWith K (fun z => y⁻¹ * z)) :
    letI := rightMetricSpace (hnil := hnil) e
    let C := bchLogMetricConstant s (Fintype.card κ) H 1
    let A := bchBoxCoordinateBound s (Fintype.card κ) H B
    (C : ℝ) * K * dist x (y * γ) < 1 →
    ((matrixDenominator Q * l : ℕ) : ℝ) * (((Fintype.card κ : ℝ) + 1) * (HQ + 1)) *
      (A * C) * K * dist x (y * γ) < 1 → γ ∈ J := by
  let := rightMetricSpace (hnil := hnil) e
  dsimp only
  intro hnear hsmall
  have hdist : dist (y⁻¹ * x) γ ≤ (K : ℝ) * dist x (y * γ) := by
    simpa only [inv_mul_cancel_left] using hleft.dist_le_mul x (y * γ)
  apply (hJ γ).mpr
  apply rational_kernel_of_near_bounded_point e c hstructure hc Q HQ B hB hQ l hl (y⁻¹ * x) γ
    hxy hγ ((hJ _).mp (J.mul_mem (J.inv_mem hy) hx))
  · calc
      _ ≤ (bchLogMetricConstant s (Fintype.card κ) H 1 : ℝ) * (K * dist x (y * γ)) :=
        mul_le_mul_of_nonneg_left hdist (NNReal.coe_nonneg _)
      _ < 1 := by nlinarith [hnear]
  · have hA := bchBoxCoordinateBound_nonneg s (Fintype.card κ) H B.coe_nonneg
    calc
      _ ≤ ((matrixDenominator Q * l : ℕ) : ℝ) * (((Fintype.card κ : ℝ) + 1) * (HQ + 1)) *
          (bchBoxCoordinateBound s (Fintype.card κ) H B *
            (bchLogMetricConstant s (Fintype.card κ) H 1 : ℝ)) * (K * dist x (y * γ)) :=
        mul_le_mul_of_nonneg_left hdist (by positivity)
      _ < 1 := by nlinarith [hsmall]

theorem exists_uniform_lattice_image_gap
    (e : Basis κ ℝ L) (c : κ → κ → κ → ℚ)
    (hstructure : ∀ i j k, algebraMap ℚ ℝ (c i j k) = e.repr ⁅e i, e j⁆ k)
    (hc : ∀ i j k, RationalHeightLE (c i j k) H)
    (Q : Matrix ι κ ℚ) (HQ B K : ℝ≥0) (hB : 1 ≤ B)
    (hQ : ∀ i j, |(Q i j : ℝ)| ≤ HQ) (l : ℕ) (hl : 0 < l)
    (J Λ : Subgroup (NilpotentLieBCHGroup L s hnil))
    (hJ : ∀ g, g ∈ J ↔ (fun i j => (Q i j : ℝ)) *ᵥ basisHomeomorph e g = 0)
    (hΛ : ∀ γ ∈ Λ, basisHomeomorph e γ ∈ realDenominatorGrid l)
    (S : Set (NilpotentLieBCHGroup L s hnil)) (hS : S ⊆ J)
    (hprod : ∀ x ∈ S, ∀ y ∈ S, ∀ i, |e.repr (y⁻¹ * x).coord i| ≤ B)
    (hleft : letI := rightMetricSpace (hnil := hnil) e;
      ∀ y ∈ S, LipschitzWith K (fun z => y⁻¹ * z)) :
    letI := rightMetricSpace (hnil := hnil) e
    let C := bchLogMetricConstant s (Fintype.card κ) H 1
    let A := bchBoxCoordinateBound s (Fintype.card κ) H B
    ∃ ε : ℝ≥0, 0 < ε ∧
      (ε : ℝ)⁻¹ = (C : ℝ) * K +
        ((matrixDenominator Q * l : ℕ) : ℝ) * (((Fintype.card κ : ℝ) + 1) * (HQ + 1)) *
          (A * C) * K + 1 ∧
      ∀ x ∈ S, ∀ y ∈ S, ∀ γ ∈ Λ, dist x (y * γ) < ε → γ ∈ J := by
  let := rightMetricSpace (hnil := hnil) e
  let a : ℝ := (bchLogMetricConstant s (Fintype.card κ) H 1 : ℝ) * K
  let b : ℝ := ((matrixDenominator Q * l : ℕ) : ℝ) *
    (((Fintype.card κ : ℝ) + 1) * (HQ + 1)) *
    (bchBoxCoordinateBound s (Fintype.card κ) H B *
      (bchLogMetricConstant s (Fintype.card κ) H 1 : ℝ)) * K
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hb : 0 ≤ b := by
    have := bchBoxCoordinateBound_nonneg s (Fintype.card κ) H B.coe_nonneg
    dsimp [b]
    positivity
  have hr : 0 < a + b + 1 := by linarith
  let ε : ℝ≥0 := ⟨(a + b + 1)⁻¹, (inv_pos.mpr hr).le⟩
  refine ⟨ε, show (0 : ℝ) < (a + b + 1)⁻¹ from inv_pos.mpr hr, ?_, ?_⟩
  · exact inv_inv (a + b + 1)
  · intro x hx y hy γ hγ hnear
    have hscaled : (a + b + 1) * dist x (y * γ) < 1 := by
      have h := mul_lt_mul_of_pos_left hnear hr
      change (a + b + 1) * dist x (y * γ) < (a + b + 1) * (a + b + 1)⁻¹ at h
      simpa only [mul_inv_cancel₀ hr.ne'] using h
    apply lattice_translate_mem_of_small_dist e c hstructure hc Q HQ B K hB hQ l hl
      J hJ x y γ (hS hx) (hS hy) (hΛ γ hγ) (hprod x hx y hy) (hleft y hy)
    · change a * dist x (y * γ) < 1
      nlinarith [dist_nonneg (x := x) (y := y * γ)]
    · change b * dist x (y * γ) < 1
      nlinarith [dist_nonneg (x := x) (y := y * γ)]

end Erdos3.NilpotentLieBCHGroup

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.BCHSmoothPartitionBudget
namespace OAI

section

namespace Erdos3

open scoped NNReal

theorem exists_bchInverseBoxConstant_exp_bound (s a : ℕ) :
    ∃ D : ℕ, 2 ≤ D ∧ ∀ (d H : ℕ) (B : ℝ≥0) (p : ℝ),
      0 ≤ p → (d : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p →
      (B : ℝ) ≤ Real.exp ((p + 2) ^ a) →
      (bchInverseBoxConstant s d H B : ℝ) ≤ Real.exp ((p + D) ^ D) := by
  obtain ⟨C₁, hC₁, hbox⟩ := exists_bchBoxMetricConstant_exp_bound s a
  obtain ⟨C₂, hC₂, hone⟩ := exists_bchBoxMetricConstant_exp_bound s 0
  let C := C₁ + C₂ + a + 4
  have hC : 2 ≤ C := by dsimp [C]; omega
  refine ⟨C + 5, by omega, ?_⟩
  intro d H B p hp hd hH hB
  let q := (p + C) ^ C
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hC' : (2 : ℝ) ≤ C := by exact_mod_cast hC
  have hBq : (B : ℝ) ≤ Real.exp q := by
    apply hB.trans
    apply Real.exp_le_exp.mpr
    apply (pow_le_pow_left₀ (by linarith) (show p + 2 ≤ p + C by linarith) a).trans
    exact pow_le_pow_right₀ (by linarith) (by dsimp [C]; omega)
  have hAq : bchBoxCoordinateBound s d H B ≤ Real.exp q :=
    (bchBoxCoordinateBound_le_bchBoxMetricConstant s d H B).trans
      ((hbox d H B p hp hd hH hB).trans (Real.exp_le_exp.mpr
        (shifted_power_self_mono (C := C₁) (D := C) hp (by omega) (by dsimp [C]; omega))))
  have hA1q : bchBoxCoordinateBound s d H 1 ≤ Real.exp q := by
    apply (bchBoxCoordinateBound_le_bchBoxMetricConstant s d H 1).trans
    have hunit : ((1 : ℝ≥0) : ℝ) ≤ Real.exp ((p + 2) ^ 0) := by
      simpa only [NNReal.coe_one, pow_zero] using
        Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 1)
    apply (hone d H 1 p hp hd hH hunit).trans
    exact Real.exp_le_exp.mpr
      (shifted_power_self_mono (C := C₂) (D := C) hp (by omega) (by dsimp [C]; omega))
  have hnum : bchBoxCoordinateBound s d H B + 2 * (B : ℝ) ≤ 3 * Real.exp q := by linarith
  have hden : bchBoxCoordinateBound s d H 1 + 1 ≤ 2 * Real.exp q := by
    linarith [Real.one_le_exp hq]
  have h6 : (6 : ℝ) ≤ Real.exp 16 := by linarith [Real.add_one_le_exp (16 : ℝ)]
  change (bchBoxCoordinateBound s d H B + 2 * (B : ℝ)) *
    (bchBoxCoordinateBound s d H 1 + 1) ≤ _
  calc
    _ ≤ (3 * Real.exp q) * (2 * Real.exp q) :=
      mul_le_mul hnum hden (by have := bchBoxCoordinateBound_nonneg s d H (B := 1) (by norm_num); linarith)
        (by positivity)
    _ = 6 * Real.exp (2 * q) := by rw [show 2 * q = q + q by ring, Real.exp_add]; ring
    _ ≤ Real.exp 16 * Real.exp (2 * q) := mul_le_mul_of_nonneg_right h6 (Real.exp_nonneg _)
    _ = Real.exp (2 * q + 16) := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ _ := Real.exp_le_exp.mpr (enlarged_power_dominates_twice_add_sixteen hp C hC)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.WeightedTranslationBasisHeight
namespace OAI

section

namespace Erdos3.PolynomialTranslationLie

open _root_.MvPolynomial
variable {σ : Type*} [Fintype σ]

noncomputable def relationSpace (U : LieSubalgebra ℚ (PolynomialTranslationLie σ)) :
    Submodule ℚ ((σ → ℚ) × MvPolynomial σ ℚ) :=
  U.toSubmodule.comap toProdl.symm.toLinearMap

end Erdos3.PolynomialTranslationLie

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.ImageDefiningMatrix
namespace OAI

section

namespace Erdos3

open Module
open scoped Matrix TensorProduct

variable {ι κ L M : Type*} [Fintype ι] [Fintype κ]
  [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]

open NilpotentLieBCHGroup

variable {s : ℕ} {hL : LieModule.lowerCentralSeries ℚ L L s = ⊥}
  {hM : LieModule.lowerCentralSeries ℚ M M s = ⊥}

theorem realificationMap_mem_range_iff (φ : L →ₗ⁅ℚ⁆ M)
    (g : NilpotentLieBCHGroup (ℝ ⊗[ℚ] M) s (realification_lowerCentralSeries_eq_bot hM)) :
    g ∈ (realificationMap (hnil := hL) (hM := hM) φ).range ↔
      g.coord ∈ LinearMap.range (φ.toLinearMap.baseChange ℝ) := by
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x.coord, congrArg NilpotentLieBCHGroup.coord hx⟩
  · rintro ⟨x, hx⟩
    exact ⟨⟨x⟩, ext hx⟩

theorem exists_realified_image_defining_matrix (e : Basis ι ℚ L) (f : Basis κ ℚ M)
    (φ : L →ₗ⁅ℚ⁆ M) {H : ℕ} (hH : 1 ≤ H)
    (hentries : ∀ i j, RationalHeightLE (f.repr (φ (e j)) i) H) :
    ∃ Q : Matrix κ κ ℚ,
      (∀ i j, RationalHeightLE (Q i j)
        (2 * ((Fintype.card ι + 1) * (H * rationalKernelHeight (Fintype.card κ) H) ^ Fintype.card ι))) ∧
      ∀ g : NilpotentLieBCHGroup (ℝ ⊗[ℚ] M) s (realification_lowerCentralSeries_eq_bot hM),
        g ∈ (realificationMap (hnil := hL) (hM := hM) φ).range ↔
          (fun i j => (Q i j : ℝ)) *ᵥ (f.baseChange ℝ).equivFun g.coord = 0 := by
  classical
  obtain ⟨σ, hσ, hσH⟩ := exists_bounded_linear_image_section e f φ.toLinearMap hH hentries
  let P : M →ₗ[ℚ] M := LinearMap.id - φ.toLinearMap.comp σ
  let Q := LinearMap.toMatrix f f P
  have hQ : Q = 1 - LinearMap.toMatrix e f φ.toLinearMap * LinearMap.toMatrix f e σ := by
    dsimp [Q, P]
    rw [map_sub, LinearMap.toMatrix_id, LinearMap.toMatrix_comp f e f]
  refine ⟨Q, ?_, ?_⟩
  · intro i j
    have hI : RationalHeightLE ((1 : Matrix κ κ ℚ) i j) 1 := by
      by_cases hij : i = j
      · simpa [Matrix.one_apply, hij] using rationalHeightLE_one (by decide : 1 ≤ 1)
      · simpa [Matrix.one_apply, hij] using rationalHeightLE_zero (by decide : 1 ≤ 1)
    have hprod := rationalHeightLE_matrix_mul (LinearMap.toMatrix e f φ.toLinearMap)
      (LinearMap.toMatrix f e σ)
      (fun i j => by rw [LinearMap.toMatrix_apply]; exact hentries i j)
      (fun i j => by rw [LinearMap.toMatrix_apply]; exact hσH i j) i j
    rw [hQ]
    simpa only [Matrix.sub_apply, mul_one] using hI.sub hprod
  · intro g
    have hσR := linearMap_baseChange_image_section φ.toLinearMap σ hσ
    have hker := ker_id_sub_comp_eq_range (φ.toLinearMap.baseChange ℝ) (σ.baseChange ℝ) hσR
    have hPR : P.baseChange ℝ = LinearMap.id - (φ.toLinearMap.baseChange ℝ).comp (σ.baseChange ℝ) := by
      simp only [P, LinearMap.baseChange_sub, LinearMap.baseChange_id, LinearMap.baseChange_comp]
    rw [realificationMap_mem_range_iff, ← hker, ← hPR]
    change P.baseChange ℝ g.coord = 0 ↔ _
    rw [show (fun i j => (Q i j : ℝ)) *ᵥ (f.baseChange ℝ).equivFun g.coord =
      (f.baseChange ℝ).equivFun (P.baseChange ℝ g.coord) from baseChange_matrix_apply f f P g.coord]
    constructor
    · intro h
      rw [h, map_zero]
    · intro h
      apply (f.baseChange ℝ).equivFun.injective
      simpa only [map_zero] using h

end Erdos3

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

theorem bch_comap_inner_grid {ι κ L M : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s : ℕ} {hL : LieModule.lowerCentralSeries ℚ L L s = ⊥}
    {hM : LieModule.lowerCentralSeries ℚ M M s = ⊥}
    (e : Basis ι ℚ L) (f : Basis κ ℚ M) (φ : L →ₗ⁅ℚ⁆ M)
    (Λ : Subgroup (NilpotentLieBCHGroup M s hM)) (l : ℕ)
    (hΛ : scaledIntegerGrid l ⊆ bchSubgroupCoordinates f Λ) :
    scaledIntegerGrid (l * matrixDenominator (LinearMap.toMatrix e f φ.toLinearMap)) ⊆
      bchSubgroupCoordinates e (Λ.comap (map (hnil := hL) φ)) := by
  rw [bchSubgroupCoordinates_comap e f φ Λ]
  intro x hx
  exact hΛ (matrix_mulVec_fine_grid (LinearMap.toMatrix e f φ.toLinearMap) l hx)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.NativeHorizontalLiftBudget
namespace OAI

section

namespace Erdos3

open scoped NNReal

theorem exists_bchLogMetricConstant_exp_bound (s : ℕ) :
    ∃ Z : ℕ, 2 ≤ Z ∧ ∀ (n H : ℕ) (p : ℝ), 0 ≤ p → (n : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p →
      (bchLogMetricConstant s n H 1 : ℝ) ≤ Real.exp ((p + Z) ^ Z + 1) := by
  obtain ⟨Z, hZ, hbox⟩ := exists_bchBoxMetricConstant_exp_bound s 0
  refine ⟨Z, hZ, ?_⟩
  intro n H p hp hn hH
  have h := (bchBoxCoordinateBound_le_bchBoxMetricConstant s n H 1).trans
    (hbox n H 1 p hp hn hH (by simp only [NNReal.coe_one, pow_zero]; exact Real.one_le_exp (by norm_num)))
  change bchBoxCoordinateBound s n H 1 ≤ Real.exp ((p + Z) ^ Z) at h
  change bchBoxCoordinateBound s n H 1 + 1 ≤ _
  have h1 : 1 ≤ Real.exp ((p + Z) ^ Z) := Real.one_le_exp (by positivity)
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  rw [Real.exp_add]
  nlinarith [Real.exp_pos ((p + Z) ^ Z)]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RealSymbolRepresentativeSplitting
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (w : σ → ℕ)

theorem realSymbolRepresentative_rational_coefficients (l : ℕ)
    (g : F.RealPolynomialSymbolGroup w) (hg : F.SymbolRationalGrid b ω hlayers w l g) :
    (fun z : (σ →₀ ℕ) × ι => (b.baseChange ℝ).repr
      (coefficients (F.realSymbolRepresentative b ω hlayers w g.coord) z.1) z.2)
        ∈ realDenominatorGrid l := by
  classical
  obtain ⟨a, ha⟩ := hg
  refine ⟨fun z => if h : Finsupp.weight w z.1 = ω z.2 then a ⟨z, h⟩ else 0, ?_⟩
  funext z
  change ((if h : Finsupp.weight w z.1 = ω z.2 then a ⟨z, h⟩ else 0 : ℤ) : ℝ) =
    (l : ℝ) * (b.baseChange ℝ).repr
      (coefficients (F.realSymbolRepresentative b ω hlayers w g.coord) z.1) z.2
  by_cases h : Finsupp.weight w z.1 = ω z.2
  · rw [dif_pos h]
    have hc := F.realSymbolRepresentative_coefficient b ω hlayers w g.coord ⟨z, h⟩
    change (b.baseChange ℝ).repr
      (coefficients (F.realSymbolRepresentative b ω hlayers w g.coord) z.1) z.2 = _ at hc
    rw [hc]
    exact congrFun ha ⟨z, h⟩
  · rw [dif_neg h, Int.cast_zero,
      F.realSymbolRepresentative_coefficient_of_ne b ω hlayers w g.coord z.1 z.2 h, mul_zero]

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.TotalDegreeSplitDownsets
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open scoped BigOperators

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

noncomputable def totalDegreeMultifiltration (σ : Type*) [Fintype σ] [Nonempty σ] :
    MultidegreeLieFiltration σ L s (fun _ => s) := by
  classical
  exact {
    ordinary := F
    layer := fun a => F.layer (∑ i, a i)
    antitone := fun _ _ h => F.antitone (Finset.sum_le_sum fun i _ => h i)
    zero_eq_top := by simpa only [Pi.zero_apply, Finset.sum_const_zero] using F.totalDegree_zero_layer
    lie_mem := by
      intro a b x y hx hy
      simpa only [Pi.add_apply, Finset.sum_add_distrib] using F.lie_mem hx hy
    terminal := by
      intro a ha
      change ¬∀ i, a i ≤ s at ha
      push Not at ha
      obtain ⟨i, hi⟩ := ha
      have hsum : a i ≤ ∑ j, a j :=
        Finset.single_le_sum (fun j _ => Nat.zero_le (a j)) (Finset.mem_univ i)
      exact F.layer_eq_bot_above_step (hi.trans_le hsum)
    degree_eq := by
      intro n
      apply le_antisymm
      · let i : σ := Classical.choice (inferInstance : Nonempty σ)
        let a : σ → ℕ := Pi.single i n
        have hsum : ∑ j, a j = n := by simp [a]
        apply le_iSup_of_le a
        apply le_iSup_of_le (show n ≤ ∑ j, a j by omega)
        rw [hsum]
      · apply iSup_le
        intro a
        apply iSup_le
        intro ha
        exact F.antitone ha }

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial
open scoped BigOperators TensorProduct

variable {σ L : Type*} [Fintype σ] [Nonempty σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} (F : NilpotentLieFiltration L s)

theorem real_totalDegree_adapted (g : F.realification.PolynomialOrbit (fun _ : σ => 1)) :
    (F.totalDegreeMultifiltration σ).realification.Adapted g.log := by
  intro a
  change coefficients g.log a ∈ F.realification.layer (∑ i, a i)
  simpa only [Finsupp.weight_eq_sum, smul_eq_mul, mul_one] using
    (F.realification.adapted_iff_coefficients (fun _ : σ => 1) g.log).mp g.adapted a

noncomputable def realTotalDegreeOrbit (g : F.realification.PolynomialOrbit (fun _ : σ => 1)) :
    (F.totalDegreeMultifiltration σ).realification.PolynomialOrbit :=
  (F.totalDegreeMultifiltration σ).realification.polynomialOrbitOfLog g.log
    (F.real_totalDegree_adapted g)

theorem realTotalDegreeOrbit_eval (g : F.realification.PolynomialOrbit (fun _ : σ => 1))
    (x : σ → ℤ) :
    (F.totalDegreeMultifiltration σ).realification.polynomialOrbitEval x (F.realTotalDegreeOrbit g) =
      F.realification.polynomialOrbitEval (fun _ : σ => 1) x g := by
  apply NilpotentLieBCHGroup.ext
  simp only [MultidegreeLieFiltration.polynomialOrbitEval_coord, NilpotentLieFiltration.polynomialOrbitEval_coord]
  rfl

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3

open scoped BigOperators

theorem totalDegreeSplitDownset_terminal {L : Type*} [LieRing L] [LieAlgebra ℚ L]
    {s : ℕ} (F : NilpotentLieFiltration L s) (a : Fin 2 →₀ ℕ)
    (ha : a ∉ totalDegreeSplitDownset s false ∪ totalDegreeSplitDownset s true) :
    (F.totalDegreeMultifiltration (Fin 2)).layer (fun i => a i) = ⊥ := by
  apply F.layer_eq_bot_above_step
  exact Nat.lt_of_not_ge (fun h => ha (totalDegreeSplitDownset_covers s a h))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.DescendedLinearMapBounds
namespace OAI

section

namespace Erdos3

open Module

variable {L M Z ι κ ν : Type*} [LieRing L] [LieAlgebra ℚ L]
  [LieRing M] [LieAlgebra ℚ M] [AddCommGroup Z] [Module ℚ Z]
  [Fintype ι] [Fintype κ]

theorem descended_linear_map_coordinate_height
    (e : Basis ι ℚ L) (f : Basis κ ℚ M) (b : Basis ν ℚ Z)
    (π : L →ₗ[ℚ] M) (hπ : Function.Surjective π) (φ : M →ₗ[ℚ] Z)
    {Q H : ℕ} (hQ : 1 ≤ Q)
    (hproj : ∀ i j, RationalHeightLE (f.repr (π (e j)) i) Q)
    (hcomp : ∀ i j, RationalHeightLE (b.repr (φ (π (e j))) i) H) (i : ν) (j : κ) :
    RationalHeightLE (b.repr (φ (f j)) i)
      ((Fintype.card ι + 1) * (rationalSolveHeight (Fintype.card κ) Q * H) ^ Fintype.card ι) := by
  obtain ⟨σ, hσ, hσH⟩ := exists_bounded_linear_section e f π hπ hQ hproj
  have h := linearMap_coordinate_height e b (φ.comp π) (fun j i => hcomp i j)
    (σ (f j)) (fun k => hσH k j) i
  simpa only [LinearMap.comp_apply, hσ (f j)] using h

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RealSubspaceIntersectionCorrections
namespace OAI

section

namespace Erdos3

open scoped Matrix NNReal

theorem exists_image_intersection_corrections
    {ι κ ν σ : Type*} [Fintype ι] [Fintype κ] [Fintype ν]
    (A : Matrix ι κ ℚ) (B : Matrix ι ν ℚ) {H l : ℕ} (hH : 1 ≤ H) (hl : 0 < l)
    (hA : ∀ i j, RationalHeightLE (A i j) H) (hB : ∀ i j, RationalHeightLE (B i j) H)
    {p : ℝ} (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p)
    (hcols : (Fintype.card (κ ⊕ ν) : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p) (hlp : (l : ℝ) ≤ Real.exp p)
    (T : σ → ℝ) (hT : ∀ i, Real.exp (separationBudget p) ≤ T i) :
    ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + 2) ^ 3 + (p + 2) ^ 36) ∧
      ∀ (α : σ →₀ ℕ), α ≠ 0 → ∀ (a b u v : ι → ℝ),
        u ∈ LinearMap.range (Matrix.mulVecLin (fun i j => (A i j : ℝ))) →
        v ∈ LinearMap.range (Matrix.mulVecLin (fun i j => (B i j : ℝ))) →
        ‖a‖ ≤ Real.exp p / monomialScale T α → b ∈ realDenominatorGrid l →
        u - v = a + b → ∃ e q : ι → ℝ,
          e ∈ LinearMap.range (Matrix.mulVecLin (fun i j => (A i j : ℝ))) ∧
          q ∈ LinearMap.range (Matrix.mulVecLin (fun i j => (A i j : ℝ))) ∧
          ‖e‖ ≤ Real.exp ((p + 2) ^ 3 + (p + 2) ^ 18 + p) / monomialScale T α ∧
          q ∈ realDenominatorGrid m ∧
          u - e - q ∈ LinearMap.range (Matrix.mulVecLin (fun i j => (A i j : ℝ))) ⊓
            LinearMap.range (Matrix.mulVecLin (fun i j => (B i j : ℝ))) := by
  let C := Matrix.fromCols A B
  have hC : ∀ i j, RationalHeightLE (C i j) H := by
    intro i j
    cases j with
    | inl j => exact hA i j
    | inr j => exact hB i j
  obtain ⟨S, m, hm, hmp, hsolve⟩ :=
    exists_controlled_linear_splitting C hH hl hC hp hι hcols hHp hlp T hT
  have hκ : (Fintype.card κ : ℝ) ≤ p := by
    rw [Fintype.card_sum, Nat.cast_add] at hcols
    linarith [Nat.cast_nonneg (α := ℝ) (Fintype.card ν)]
  have hHp' : (H : ℝ) ≤ Real.exp ((p + 2) ^ 1) :=
    hHp.trans (Real.exp_le_exp.mpr (by simp))
  have hden : (matrixDenominator A : ℝ) ≤ Real.exp ((p + 2) ^ 3) :=
    matrixDenominator_le_exp_power A hp 1 hι hκ
      (fun i j => (Nat.cast_le.mpr (hA i j).2).trans hHp')
  have hfac : ((Fintype.card κ : ℝ) + 1) * (H + 1) ≤ Real.exp ((p + 2) ^ 3) := by
    apply le_trans _ (matrix_weighted_factor_le_exp_power (Fintype.card κ) hp hκ 1 (by decide))
    exact mul_le_mul_of_nonneg_left (add_le_add hHp' le_rfl) (by positivity)
  have hnorm (y : κ → ℝ) :
      ‖(fun i j => (A i j : ℝ)) *ᵥ y‖ ≤ Real.exp ((p + 2) ^ 3) * ‖y‖ :=
    (norm_matrix_mulVec_le _ (H : ℝ≥0) (fun i j => (hA i j).abs_real_le) y).trans
      (mul_le_mul_of_nonneg_right hfac (norm_nonneg y))
  refine ⟨matrixDenominator A * m, Nat.mul_pos (matrixDenominator_pos A) hm, ?_, ?_⟩
  · rw [Nat.cast_mul]
    exact (mul_le_mul hden hmp (Nat.cast_nonneg _) (Real.exp_pos _).le).trans_eq
      (Real.exp_add _ _).symm
  · intro α hα a b u v hu hv ha hb hdiff
    have hspan : Submodule.span ℝ (Set.range (fun j i => (C i j : ℝ))) =
        Submodule.span ℝ (Set.range (fun j i => (A i j : ℝ))) ⊔
          Submodule.span ℝ (Set.range (fun j i => (B i j : ℝ))) :=
      real_column_span_fromCols A B
    have hdiffmem : u - v ∈ LinearMap.range (Matrix.mulVecLin (fun i j => (C i j : ℝ))) := by
      apply (real_column_span_mem_iff C _).mp
      rw [hspan]
      exact Submodule.sub_mem _ (Submodule.mem_sup_left ((real_column_span_mem_iff A _).mpr hu))
        (Submodule.mem_sup_right ((real_column_span_mem_iff B _).mpr hv))
    obtain ⟨z, hz⟩ := hdiffmem
    obtain ⟨hSa, hSb, hslow, hgrid, _⟩ := hsolve α hα a b z ha hb (hz.trans hdiff)
    let ca := (fun i j => (S i j : ℝ)) *ᵥ a
    let cb := (fun i j => (S i j : ℝ)) *ᵥ b
    let e := (fun i j => (A i j : ℝ)) *ᵥ (ca ∘ Sum.inl)
    let q := (fun i j => (A i j : ℝ)) *ᵥ (cb ∘ Sum.inl)
    let eB := (fun i j => (B i j : ℝ)) *ᵥ (ca ∘ Sum.inr)
    let qB := (fun i j => (B i j : ℝ)) *ᵥ (cb ∘ Sum.inr)
    have he : e ∈ LinearMap.range (Matrix.mulVecLin (fun i j => (A i j : ℝ))) := ⟨_, rfl⟩
    have hq : q ∈ LinearMap.range (Matrix.mulVecLin (fun i j => (A i j : ℝ))) := ⟨_, rfl⟩
    have heB : eB ∈ LinearMap.range (Matrix.mulVecLin (fun i j => (B i j : ℝ))) := ⟨_, rfl⟩
    have hqB : qB ∈ LinearMap.range (Matrix.mulVecLin (fun i j => (B i j : ℝ))) := ⟨_, rfl⟩
    have hea : e + eB = a := by
      change (C.map (Rat.castHom ℝ)) *ᵥ ca = a at hSa
      dsimp only [C] at hSa
      rw [Matrix.fromCols_map, Matrix.fromCols_mulVec] at hSa
      exact hSa
    have hqb : q + qB = b := by
      change (C.map (Rat.castHom ℝ)) *ᵥ cb = b at hSb
      dsimp only [C] at hSb
      rw [Matrix.fromCols_map, Matrix.fromCols_mulVec] at hSb
      exact hSb
    refine ⟨e, q, he, hq, ?_,
      real_matrix_denominator_grid A m _ (realDenominatorGrid_comp m _ hgrid Sum.inl),
      Submodule.sub_mem _ (Submodule.sub_mem _ hu he) hq, ?_⟩
    · calc
        ‖e‖ ≤ Real.exp ((p + 2) ^ 3) * ‖ca ∘ Sum.inl‖ := hnorm _
        _ ≤ Real.exp ((p + 2) ^ 3) *
            (Real.exp ((p + 2) ^ 18 + p) / monomialScale T α) :=
          mul_le_mul_of_nonneg_left ((pi_norm_restriction_le ca Sum.inl).trans hslow)
            (Real.exp_pos _).le
        _ = _ := by
          rw [← mul_div_assoc, ← Real.exp_add]
          congr 2
          ring
    · have heq : u - e - q = v + eB + qB := by
        rw [← hea, ← hqb] at hdiff
        have hu' : u = (e + eB) + (q + qB) + v := (sub_eq_iff_eq_add).mp hdiff
        rw [hu']
        abel
      rw [heq]
      exact Submodule.add_mem _ (Submodule.add_mem _ hv heB) hqB

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
open scoped TensorProduct NNReal

theorem linearMap_coordinate_norm_le {ι κ V W : Type*} [Fintype ι] [Fintype κ]
    [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    (e : Basis ι ℝ V) (f : Basis κ ℝ W) (q : V →ₗ[ℝ] W) (A : ℝ≥0)
    (hentries : ∀ i j, |f.repr (q (e j)) i| ≤ A) (x : V) :
    ‖f.equivFun (q x)‖ ≤ (Fintype.card ι : ℝ) * A * ‖e.equivFun x‖ := by
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  have h := abs_linearMap_le_basis_bound e ((f.coord i).comp q) A (hentries i) x
  simpa only [LinearMap.comp_apply, Basis.coord_apply, Basis.equivFun_apply, Real.norm_eq_abs] using h

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CoefficientSliceEmbedding
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators NNReal

namespace ScalarCubeLocalizationData

variable {I : Type*} [Fintype I] [DecidableEq I] (d : ScalarCubeLocalizationData I)

noncomputable def cellCount : ℕ := residueCellCount d.length d.cellLength

end ScalarCubeLocalizationData

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CommonDependentIntegralModel
namespace OAI

section

namespace Erdos3

open Module

variable {I L : Type*} [Fintype I] [LieRing L] [LieAlgebra ℚ L]

theorem finiteMarkedLieValues_coordinate_height {ι : Type*} [Fintype ι]
    (b : Basis ι ℚ L) (v : I → L) (w : I → ℕ) (marked : I → Bool) {H : ℕ}
    (hc : ∀ i j k, RationalHeightLE (lieStructureConstants b i j k) H)
    (hv : ∀ i j, RationalHeightLE (b.repr (v i) j) H) (s d k l : ℕ)
    {x : L} (hx : x ∈ finiteMarkedLieValues v w marked s d k l) (j : ι) :
    RationalHeightLE (b.repr x j) (lieTreeHeight (Fintype.card ι) H s) := by
  classical
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
  exact finiteLieTrees_coordinate_height b v hc hv s a (Finset.mem_filter.mp ha).1 j

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.MarkedEvaluationHeightBudget
namespace OAI

section

namespace Erdos3

noncomputable def markedShiftModelBudget (s : ℕ) (p : ℝ) : ℝ :=
  markedShiftHeightBudget s p +
    (markedShiftHeightBudget s p + (bchIntegralDenominatorBound (s + 1) + 5 : ℕ)) ^
      (bchIntegralDenominatorBound (s + 1) + 5)

theorem markedShiftHeightBudget_le_model (s : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    markedShiftHeightBudget s p ≤ markedShiftModelBudget s p :=
  le_add_of_nonneg_right (pow_nonneg
    (add_nonneg (markedShiftHeightBudget_nonneg s hp) (Nat.cast_nonneg _)) _)

theorem exists_markedShiftModel_budget (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p → markedShiftModelBudget s p ≤ (p + C) ^ C := by
  let Q : Polynomial ℕ := Polynomial.X * Polynomial.C (s + 1) * (Polynomial.X + 1) ^ s +
    Polynomial.X + Polynomial.C (s + 1)
  let U : Polynomial ℕ := (Q + 2) ^ (5082 * s + 3564)
  let K := bchIntegralDenominatorBound (s + 1) + 5
  obtain ⟨C, hC, h⟩ := exists_natPolynomial_eval_budget (U + (U + Polynomial.C K) ^ K)
  refine ⟨C, hC, ?_⟩
  intro p hp
  simpa only [markedShiftModelBudget, markedShiftHeightBudget, markedShiftInputBudget,
    Q, U, K, Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_pow,
    Polynomial.eval₂_X, Polynomial.eval₂_C, Polynomial.eval₂_one, Polynomial.eval₂_ofNat,
    Nat.coe_castRingHom] using h p hp

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.MarkedLocalObservableMetric
namespace OAI

section

namespace Erdos3

open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal

noncomputable def markedLocalBoxConstant (s d H u e Ht : ℕ) (p : ℝ) (B ℓ : ℝ≥0) : ℝ≥0 :=
  ℓ * bchBoxMetricConstant u e Ht (markedEvaluationBoxRadius s d H p B) *
    ⟨Real.exp (2 * p), Real.exp_nonneg _⟩ * markedRetractionBoxConstant s d H p B

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CommonInducedCorrelation
namespace OAI

section

namespace Erdos3

open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal

noncomputable def inducedMarkedLipschitzBound (s d u e : ℕ) (p : ℝ) (R : ℝ≥0) : ℝ≥0 :=
  2 * phaseBandQuotientConstant (s + 1) d ⌈Real.exp p⌉₊ R
    ⟨Real.exp ((p + 3) ^ 2), Real.exp_nonneg _⟩
    (markedLocalBoxConstant s d ⌈Real.exp p⌉₊ u e ⌈Real.exp p⌉₊ p (R + 1)
      ⟨Real.exp p, Real.exp_nonneg _⟩)

end Erdos3

end

end OAI
end


