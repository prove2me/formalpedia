-- Prove2me | Definitions.Def_OAIE3v2B024
-- name    : OAIE3v2B024
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T09:59:17.566991+00:00
-- url     : https://prove2.me/theorems/f96ebe05-cd47-4c37-a846-91f578806e0e
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 25 of 311
-- statement:
--   Definitions bundle 25 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports no other bundle of this split.
--
--   Modules: `Dynamics/ImageReconstructionLogBudget.lean`, `Dynamics/InducedMarkedBudget.lean`, `Dynamics/MarkedEvaluationHeightBudget.lean`, `Dynamics/ReconstructionConstantBudget.lean`, `Estimates/BoundedNativeDependentApproximations.lean`, `Estimates/FiniteFourPointAnchors.lean`, `Estimates/FixedObservableCorrelation.lean`, `Estimates/LipschitzExtensionAlongMap.lean`, `Estimates/MarkedPureEvaluation.lean`, `Estimates/NativeBoundedVariablePatchExpansion.lean`, `Estimates/NativeCoveredCommonFactorization.lean`, `Estimates/NativeLocalPivotVerticalPartners.lean`, `Estimates/NativeMeanRowCorrelation.lean`, `Estimates/NativeWeightPairRemoval.lean`, `Estimates/RealifiedReconstruction.lean`, `Estimates/UnitVerticalCyclicDifference.lean`, `Estimates/VectorApproximationPrecomposition.lean`, `Fourier/JoinedFrequencyQuotientInjectivity.lean`, `Fourier/RealQuarterTorusExtension.lean`, `Fourier/RectangularGridCharacter.lean`, `Geometry/BoxCornerMean.lean`, `Geometry/CoordinatewiseLipschitz.lean`, `Lattices/MarkedDirectionLatticeScale.lean`, `Lattices/NativeIntegerDivision.lean`, `Lattices/NativeIntegerHalving.lean`, `Lattices/PartitionedAffineLogEnvelope.lean`, `Linear/FurstenbergWeissProjection.lean`, `Linear/ImageDefiningMatrix.lean`, `Linear/RankDependentInputBudget.lean`, `Linear/RankIntervalFactorization.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.ImageReconstructionLogBudget
namespace OAI

section

namespace Erdos3

def imageRepresentativeLogBudget (C : ℕ) (p : ℝ) : ℝ :=
  ((p + 2) ^ 4 + C) ^ C + (p + 2) ^ 2

def generalReconstructionLogBudget (C D E F Z : ℕ) (p : ℝ) : ℝ :=
  let q := p + imageRepresentativeLogBudget C p + 1
  p + (p + 2) ^ 18 + (p + 2) ^ 48 + (p + 2) ^ 24 +
    ((p + Z) ^ Z + 1) + (q + D + E) ^ E + (q + F) ^ F + 1

theorem generalReconstructionLogBudget_bounds (C D E F Z : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    let q := p + imageRepresentativeLogBudget C p + 1
    let r := generalReconstructionLogBudget C D E F Z p
    1 ≤ r ∧ p ≤ r ∧ (p + 2) ^ 18 ≤ r ∧ (p + 2) ^ 48 ≤ r ∧ (p + 2) ^ 24 ≤ r ∧
      (p + Z) ^ Z + 1 ≤ r ∧ (q + D + E) ^ E ≤ r ∧ (q + F) ^ F ≤ r := by
  have hq : 0 ≤ p + imageRepresentativeLogBudget C p + 1 := by
    dsimp [imageRepresentativeLogBudget]
    positivity
  have h18 : 0 ≤ (p + 2) ^ 18 := by positivity
  have h48 : 0 ≤ (p + 2) ^ 48 := by positivity
  have h24 : 0 ≤ (p + 2) ^ 24 := by positivity
  have hZ : 0 ≤ (p + Z) ^ Z + 1 := by positivity
  have hE : 0 ≤ (p + imageRepresentativeLogBudget C p + 1 + D + E) ^ E := by positivity
  have hF : 0 ≤ (p + imageRepresentativeLogBudget C p + 1 + F) ^ F := by positivity
  dsimp only [generalReconstructionLogBudget]
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.LipschitzExtensionAlongMap
namespace OAI

section

namespace Erdos3

open scoped NNReal

variable {X : Type*} [PseudoMetricSpace X]

theorem exists_real_lipschitz_extension_interval (f : X → ℝ) (S : Set X) (L : ℝ≥0)
    (hf : LipschitzOnWith L f S) (a b : ℝ) (hab : a ≤ b)
    (hbound : ∀ x ∈ S, a ≤ f x ∧ f x ≤ b) :
    ∃ g : X → ℝ, LipschitzWith L g ∧ Set.EqOn f g S ∧ ∀ x, a ≤ g x ∧ g x ≤ b := by
  obtain ⟨g, hg, heq⟩ := hf.extend_real
  refine ⟨fun x => max a (min b (g x)), (hg.const_min b).const_max a, ?_, ?_⟩
  · intro x hx
    change f x = max a (min b (g x))
    rw [← heq hx, min_eq_right (hbound x hx).2, max_eq_right (hbound x hx).1]
  · intro x
    exact ⟨le_max_left _ _, max_le hab (min_le_left _ _)⟩

theorem exists_complex_bounded_lipschitz_extension (f : X → ℂ) (S : Set X) (L B : ℝ≥0)
    (hf : LipschitzOnWith L f S) (hbound : ∀ x ∈ S, ‖f x‖ ≤ B) :
    ∃ g : X → ℂ, LipschitzWith (2 * L) g ∧ Set.EqOn f g S ∧ ∀ x, ‖g x‖ ≤ 2 * B := by
  have hre : LipschitzOnWith L (fun x => (f x).re) S := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    change |(f x - f y).re| ≤ L * dist x y
    exact (Complex.abs_re_le_norm _).trans (by simpa only [dist_eq_norm] using hf.dist_le_mul x hx y hy)
  have him : LipschitzOnWith L (fun x => (f x).im) S := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    change |(f x - f y).im| ≤ L * dist x y
    exact (Complex.abs_im_le_norm _).trans (by simpa only [dist_eq_norm] using hf.dist_le_mul x hx y hy)
  obtain ⟨u, hu, heu, hub⟩ := exists_real_lipschitz_extension_interval (fun x => (f x).re) S L hre
    (-B) B (neg_le_self B.coe_nonneg) (fun x hx => abs_le.mp ((Complex.abs_re_le_norm _).trans (hbound x hx)))
  obtain ⟨v, hv, hev, hvb⟩ := exists_real_lipschitz_extension_interval (fun x => (f x).im) S L him
    (-B) B (neg_le_self B.coe_nonneg) (fun x hx => abs_le.mp ((Complex.abs_im_le_norm _).trans (hbound x hx)))
  let g : X → ℂ := fun x => ⟨u x, v x⟩
  refine ⟨g, ?_, ?_, ?_⟩
  · apply LipschitzWith.of_dist_le_mul
    intro x y
    have hu' := hu.dist_le_mul x y
    have hv' := hv.dist_le_mul x y
    rw [Real.dist_eq] at hu' hv'
    calc
      dist (g x) (g y) = ‖g x - g y‖ := dist_eq_norm _ _
      _ ≤ |(g x - g y).re| + |(g x - g y).im| := Complex.norm_le_abs_re_add_abs_im _
      _ ≤ (L : ℝ) * dist x y + L * dist x y := add_le_add hu' hv'
      _ = ((2 * L : ℝ≥0) : ℝ) * dist x y := by simp only [NNReal.coe_mul, NNReal.coe_ofNat]; ring
  · intro x hx
    exact Complex.ext (heu hx) (hev hx)
  · intro x
    exact (Complex.norm_le_abs_re_add_abs_im (g x)).trans
      (by have h1 := abs_le.mpr (hub x); have h2 := abs_le.mpr (hvb x); change |u x| + |v x| ≤ _; linarith)

theorem exists_complex_extension_from_subset (S : Set X) (f : S → ℂ) (L B : ℝ≥0)
    (hf : LipschitzWith L f) (hbound : ∀ x, ‖f x‖ ≤ B) :
    ∃ g : X → ℂ, LipschitzWith (2 * L) g ∧ (∀ x : S, g x = f x) ∧ ∀ x, ‖g x‖ ≤ 2 * B := by
  classical
  let F : X → ℂ := fun x => if hx : x ∈ S then f ⟨x, hx⟩ else 0
  have hF (x : S) : F x = f x := by simp only [F, dif_pos x.property]
  have hLip : LipschitzOnWith L F S := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    simpa only [F, dif_pos hx, dif_pos hy, Subtype.dist_eq] using hf.dist_le_mul ⟨x, hx⟩ ⟨y, hy⟩
  obtain ⟨g, hg, heq, hb⟩ := exists_complex_bounded_lipschitz_extension F S L B hLip
    (fun x hx => (congrArg norm (hF ⟨x, hx⟩)).le.trans (hbound ⟨x, hx⟩))
  exact ⟨g, hg, fun x => (heq x.property).symm.trans (hF x), hb⟩

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

theorem exists_complex_extension_along_map {X Y : Type*} [PseudoMetricSpace Y]
    (f : X → Y) (u : X → ℂ) (K B : ℝ≥0)
    (hdist : ∀ x y, dist (u x) (u y) ≤ K * dist (f x) (f y))
    (hbound : ∀ x, ‖u x‖ ≤ B) :
    ∃ g : Y → ℂ, LipschitzWith (2 * K) g ∧ (∀ x, g (f x) = u x) ∧
      ∀ y, ‖g y‖ ≤ 2 * B := by
  classical
  let S := Set.range f
  let pre (y : S) : X := Classical.choose y.property
  have hpre (y : S) : f (pre y) = y.val := Classical.choose_spec y.property
  let v (y : S) : ℂ := u (pre y)
  have hv : LipschitzWith K v := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [v, hpre, Subtype.dist_eq] using hdist (pre x) (pre y)
  have hvx (x : X) : v ⟨f x, ⟨x, rfl⟩⟩ = u x := by
    apply dist_le_zero.mp
    have h := hdist (pre ⟨f x, ⟨x, rfl⟩⟩) x
    simpa only [hpre, dist_self, mul_zero] using h
  obtain ⟨g, hg, hge, hgb⟩ := exists_complex_extension_from_subset S v K B hv (fun y => hbound (pre y))
  exact ⟨g, hg, fun x => (hge ⟨f x, ⟨x, rfl⟩⟩).trans (hvx x), hgb⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.RectangularGridCharacter
namespace OAI

section

namespace Erdos3

open Module
open scoped BigOperators NNReal

theorem abs_linearMap_le_basis_bound {ι V : Type*} [Fintype ι]
    [AddCommGroup V] [Module ℝ V] (e : Basis ι ℝ V) (η : V →ₗ[ℝ] ℝ)
    (A : ℝ≥0) (hη : ∀ i, |η (e i)| ≤ A) (x : V) :
    |η x| ≤ (Fintype.card ι : ℝ) * A * ‖e.equivFun x‖ := by
  have hx : η x = ∑ i, e.repr x i * η (e i) := by
    conv_lhs => rw [← e.sum_repr x]
    simp only [map_sum, map_smul, smul_eq_mul]
  rw [hx]
  calc
    _ ≤ ∑ i, |e.repr x i * η (e i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : ι, ‖e.equivFun x‖ * A := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul]
      have he : |e.repr x i| ≤ ‖e.equivFun x‖ := by
        simpa only [Real.norm_eq_abs, Basis.equivFun_apply] using (norm_le_pi_norm (e.equivFun x) i)
      exact mul_le_mul he (hη i) (abs_nonneg _) (norm_nonneg _)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.BoxCornerMean
namespace OAI

section

namespace Erdos3

open scoped BigOperators

def boxCorner {n : ℕ} {X : Type*} (u v : Fin n → X) (ω : Fin n → Bool) : Fin n → X :=
  fun i => if ω i then v i else u i

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RealifiedReconstruction
namespace OAI

section

namespace Erdos3

open Module
open scoped Matrix TensorProduct

variable {ι κ L M : Type*} [Fintype ι] [Fintype κ]
  [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]

theorem linearMap_baseChange_image_section (φ : L →ₗ[ℚ] M) (σ : M →ₗ[ℚ] L)
    (hσ : (φ.comp σ).comp φ = φ) :
    ((φ.baseChange ℝ).comp (σ.baseChange ℝ)).comp (φ.baseChange ℝ) = φ.baseChange ℝ := by
  simpa only [LinearMap.baseChange_comp] using
    congrArg (fun T : L →ₗ[ℚ] M => T.baseChange ℝ) hσ

end Erdos3

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

theorem ker_id_sub_comp_eq_range {R V W : Type*} [Ring R]
    [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
    (φ : V →ₗ[R] W) (σ : W →ₗ[R] V) (hσ : (φ.comp σ).comp φ = φ) :
    LinearMap.ker (LinearMap.id - φ.comp σ) = LinearMap.range φ := by
  ext y
  change y - φ (σ y) = 0 ↔ ∃ x, φ x = y
  constructor
  · intro h
    exact ⟨σ y, (sub_eq_zero.mp h).symm⟩
  · rintro ⟨x, rfl⟩
    exact sub_eq_zero.mpr (DFunLike.congr_fun hσ x).symm

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.FurstenbergWeissProjection
namespace OAI

section

namespace Erdos3

variable {V W : Type*} [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℚ W]

def fourLinearMap (f : V →ₗ[ℚ] W) : (Fin 4 → V) →ₗ[ℚ] (Fin 4 → W) :=
  LinearMap.pi (fun k => f.comp (LinearMap.proj k))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.ReconstructionConstantBudget
namespace OAI

section

namespace Erdos3

open scoped NNReal

theorem ambientReconstructionConstant_le_exp (L K B T ε : ℝ≥0) (r : ℝ) (hr : 1 ≤ r)
    (hL : (L : ℝ) ≤ Real.exp r) (hK : (K : ℝ) ≤ Real.exp r)
    (hB : (B : ℝ) ≤ Real.exp r) (hT : (T : ℝ) ≤ Real.exp r)
    (hε : (ε : ℝ)⁻¹ ≤ Real.exp r) :
    ((2 * max (L * (2 * K)) (2 * B / (min T⁻¹ ε / 2)) : ℝ≥0) : ℝ) ≤ Real.exp (5 * r) := by
  have h2 : (2 : ℝ) ≤ Real.exp r := by linarith [Real.add_one_le_exp r]
  let m := min T⁻¹ ε
  have hm : (m : ℝ)⁻¹ ≤ Real.exp r := by
    by_cases h : T⁻¹ ≤ ε
    · simp only [m, min_eq_left h, NNReal.coe_inv, inv_inv]
      exact hT
    · simp only [m, min_eq_right (le_of_not_ge h)]
      exact hε
  have hfirst : (L : ℝ) * (2 * K) ≤ Real.exp (4 * r) := by
    calc
      _ ≤ Real.exp r * (Real.exp r * Real.exp r) := by gcongr
      _ = Real.exp (3 * r) := by simp only [← Real.exp_add]; congr 1; ring
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  have hsecond : 2 * (B : ℝ) / ((m : ℝ) / 2) ≤ Real.exp (4 * r) := by
    calc
      _ = 2 * 2 * (B : ℝ) * (m : ℝ)⁻¹ := by simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]; ring
      _ ≤ Real.exp r * Real.exp r * Real.exp r * Real.exp r := by gcongr
      _ = _ := by simp only [← Real.exp_add]; congr 1; ring
  change 2 * max ((L : ℝ) * (2 * K)) (2 * (B : ℝ) / ((m : ℝ) / 2)) ≤ _
  calc
    _ ≤ Real.exp r * Real.exp (4 * r) := mul_le_mul h2 (max_le hfirst hsecond) (by positivity) (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem generalReconstructionConstant_le_exp (L B A N T D Q X Y ε : ℝ≥0) (r : ℝ) (hr : 1 ≤ r)
    (hL : (L : ℝ) ≤ Real.exp r) (hB : (B : ℝ) ≤ Real.exp r)
    (hA : (A : ℝ) ≤ Real.exp r) (hN : (N : ℝ) ≤ Real.exp r)
    (hT : (T : ℝ) ≤ Real.exp r) (hD : (D : ℝ) ≤ Real.exp r)
    (hQ : (Q : ℝ) ≤ Real.exp r) (hX : (X : ℝ) ≤ Real.exp r)
    (hY : (Y : ℝ) ≤ Real.exp r)
    (hε : (ε : ℝ)⁻¹ = (T : ℝ) * Y + D * Q * X * T * Y + 1) :
    ((2 * max (L * (2 * (A * N * T))) (2 * B / (min T⁻¹ ε / 2)) : ℝ≥0) : ℝ) ≤
      Real.exp (40 * r) := by
  have h15 : 1 ≤ Real.exp (5 * r) := Real.one_le_exp (by linarith)
  have hTY : (T : ℝ) * Y ≤ Real.exp (5 * r) := by
    calc
      _ ≤ Real.exp r * Real.exp r := by gcongr
      _ = Real.exp (2 * r) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  have hprod : (D : ℝ) * Q * X * T * Y ≤ Real.exp (5 * r) := by
    calc
      _ ≤ Real.exp r * Real.exp r * Real.exp r * Real.exp r * Real.exp r := by gcongr
      _ = _ := by simp only [← Real.exp_add]; congr 1; ring
  have heps : (ε : ℝ)⁻¹ ≤ Real.exp (8 * r) := by
    rw [hε]
    calc
      _ ≤ 3 * Real.exp (5 * r) := by linarith
      _ ≤ Real.exp (3 * r) * Real.exp (5 * r) := by
        apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
        linarith [Real.add_one_le_exp (3 * r)]
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hK : ((A * N * T : ℝ≥0) : ℝ) ≤ Real.exp (8 * r) := by
    calc
      _ ≤ Real.exp r * Real.exp r * Real.exp r := by simp only [NNReal.coe_mul]; gcongr
      _ = Real.exp (3 * r) := by simp only [← Real.exp_add]; congr 1; ring
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  have hshift : Real.exp r ≤ Real.exp (8 * r) := Real.exp_le_exp.mpr (by linarith)
  have h := ambientReconstructionConstant_le_exp L (A * N * T) B T ε (8 * r)
    (by linarith) (hL.trans hshift) hK (hB.trans hshift) (hT.trans hshift) heps
  convert h using 1
  congr 1
  ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FiniteFourPointAnchors
namespace OAI

section

namespace Erdos3

variable (G : Type*) [AddCommGroup G]

def fourSparse12Equiv : (G × G × G) ≃ (G × G) × G where
  toFun t := ((t.2.2, t.2.1), t.2.1 - t.1)
  invFun u := (u.1.2 - u.2, u.1.2, u.1.1)
  left_inv := by rintro ⟨a, b, c⟩; simp
  right_inv := by rintro ⟨⟨a, b⟩, h⟩; simp

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.VectorApproximationPrecomposition
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem vector_approximation_precision {I : Type*} [Fintype I] {q epsilon : ℝ}
    (a : ℕ) (hq : 0 ≤ q) (hI : (Fintype.card I : ℝ) ≤ Real.exp q)
    (hepsilon : 0 < epsilon) (hscale : 1 / epsilon ≤ Real.exp ((q + 2) ^ a)) :
    0 < epsilon / (Fintype.card I + 1 : ℝ) ∧
      1 / (epsilon / (Fintype.card I + 1 : ℝ)) ≤ Real.exp ((q + 2) ^ (a + 1)) := by
  have hcard : (0 : ℝ) < Fintype.card I + 1 := by positivity
  refine ⟨div_pos hepsilon hcard, ?_⟩
  have hcount : (Fintype.card I + 1 : ℝ) ≤ Real.exp (q + 1) := by
    rw [Real.exp_add]
    nlinarith [Real.one_le_exp hq, Real.add_one_le_exp (1 : ℝ)]
  have hpow : 1 ≤ (q + 2) ^ a := one_le_pow₀ (by linarith)
  have hexponent : q + 1 + (q + 2) ^ a ≤ (q + 2) ^ (a + 1) := by
    rw [pow_succ]
    nlinarith
  calc
    _ = (Fintype.card I + 1 : ℝ) * (1 / epsilon) := by field_simp
    _ ≤ Real.exp (q + 1) * Real.exp ((q + 2) ^ a) :=
      mul_le_mul hcount hscale (by positivity) (Real.exp_nonneg _)
    _ = Real.exp (q + 1 + (q + 2) ^ a) := (Real.exp_add _ _).symm
    _ ≤ _ := Real.exp_le_exp.mpr hexponent

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem scalar_error_le_of_vector_error {I J S : Type*} [Fintype I] [Fintype J]
    (u : I → S → ℂ) (w : J → S → ℂ) (c : J → EuclideanSpace ℂ I)
    {epsilon : ℝ}
    (herror : ∀ x, ‖(WithLp.toLp 2 (fun k => u k x) : EuclideanSpace ℂ I) -
      ∑ j, w j x • c j‖ ≤ epsilon) (k : I) :
    ∀ x, ‖u k x - ∑ j, w j x * c j k‖ ≤ epsilon := by
  intro x
  have h := (PiLp.norm_apply_le
    ((WithLp.toLp 2 (fun k => u k x) : EuclideanSpace ℂ I) - ∑ j, w j x • c j) k).trans (herror x)
  simpa only [PiLp.sub_apply, PiLp.toLp_apply, WithLp.ofLp_sum, Finset.sum_apply,
    WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul] using h

theorem norm_complex_half_le_one {c : ℂ} (hc : ‖c‖ ≤ 2) : ‖c / 2‖ ≤ 1 := by
  have htwo : ‖(2 : ℂ)‖ = (2 : ℝ) := by norm_num
  rw [norm_div, htwo]
  linarith only [hc]

theorem sum_double_half_products {J : Type*} [Fintype J] (a b c : J → ℂ) :
    (∑ j : Bool × J, (c j.2 / 2 * a j.2) * b j.2) = ∑ j, (a j * b j) * c j := by
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_bool]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

theorem vector_approximation_precompose {I J S X : Type*} [Fintype I] [Fintype J]
    [PseudoMetricSpace X] (f : X → X) (y z : S → X) (w : J → S → ℂ)
    {A : ℝ≥0} (hf : LipschitzWith A f) (heval : ∀ x, f (y x) = z x)
    {p q B B' epsilon : ℝ} (hscale : Real.exp p * (A : ℝ) ≤ Real.exp q) (hB : B ≤ B')
    (happrox : ∀ (u : I → X → ℂ) (ell : ℝ≥0), (ell : ℝ) ≤ Real.exp q →
      (∀ k, LipschitzWith ell (u k)) → (∀ k x, ‖u k x‖ ≤ 1) →
      ∃ c : J → EuclideanSpace ℂ I, (∀ j k, ‖c j k‖ ≤ 2) ∧ (∀ j, ‖c j‖ ≤ B) ∧
        ∀ x, ‖(WithLp.toLp 2 (fun k => u k (y x)) : EuclideanSpace ℂ I) -
          ∑ j, w j x • c j‖ ≤ epsilon) :
    ∀ (u : I → X → ℂ) (ell : ℝ≥0), (ell : ℝ) ≤ Real.exp p →
      (∀ k, LipschitzWith ell (u k)) → (∀ k x, ‖u k x‖ ≤ 1) →
      ∃ c : J → EuclideanSpace ℂ I, (∀ j k, ‖c j k‖ ≤ 2) ∧ (∀ j, ‖c j‖ ≤ B') ∧
        ∀ x, ‖(WithLp.toLp 2 (fun k => u k (z x)) : EuclideanSpace ℂ I) -
          ∑ j, w j x • c j‖ ≤ epsilon := by
  intro u ell hell hu hub
  have hbound : ((ell * A : ℝ≥0) : ℝ) ≤ Real.exp q :=
    (mul_le_mul_of_nonneg_right hell A.coe_nonneg).trans hscale
  obtain ⟨c, hc, hcB, herr⟩ := happrox (fun k x => u k (f x)) (ell * A) hbound
    (fun k => (hu k).comp hf) (fun k x => hub k (f x))
  refine ⟨c, hc, fun j => (hcB j).trans hB, ?_⟩
  intro x
  simpa only [heval x] using herr x

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.JoinedFrequencyQuotientInjectivity
namespace OAI

section

namespace Erdos3

variable {L : Type*} [AddCommGroup L] [Module ℚ L]

noncomputable def dividedFrequency (n : ℕ) (η : L →ₗ[ℚ] ℚ) : L →ₗ[ℚ] ℚ := (n : ℚ)⁻¹ • η

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.RealQuarterTorusExtension
namespace OAI

section

namespace Erdos3

open Module

noncomputable def centeredCircleLift (z : AddCircle (1 : ℝ)) : ℝ :=
  (AddCircle.equivIco (1 : ℝ) (-(1 / 2)) z).val

theorem centeredCircleLift_coe {y : ℝ} (hy : |y| ≤ 1 / 4) :
    centeredCircleLift (y : AddCircle (1 : ℝ)) = y := by
  apply AddCircle.equivIco_coe_of_mem
  constructor <;> linarith [(abs_le.mp hy).1, (abs_le.mp hy).2]

noncomputable def affineCyclicTorusLocalLift {r N : ℕ}
    (t c : Fin r → ℝ) (h₀ h : ZMod N) : Fin r → ℝ :=
  fun i => centeredCircleLift
    (((((h.val : ℝ) - h₀.val) * t i - c i) : ℝ) : AddCircle (1 : ℝ))

end Erdos3

end

section

namespace Erdos3

theorem centeredCircleLift_eq_sub_floor (x : ℝ) :
    centeredCircleLift (x : AddCircle (1 : ℝ)) = x - (⌊x + 1 / 2⌋ : ℤ) := by
  have hmem : x - (⌊x + 1 / 2⌋ : ℤ) ∈ Set.Ico (-(1 / 2 : ℝ)) (-(1 / 2 : ℝ) + 1) := by
    constructor
    · linarith [Int.floor_le (x + 1 / 2)]
    · linarith [Int.lt_floor_add_one (x + 1 / 2)]
  have hint : (((⌊x + 1 / 2⌋ : ℤ) : ℝ) : AddCircle (1 : ℝ)) = 0 := by
    apply (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr
    exact ⟨⌊x + 1 / 2⌋, by simp⟩
  have he : ((x - (⌊x + 1 / 2⌋ : ℤ) : ℝ) : AddCircle (1 : ℝ)) = x := by
    rw [AddCircle.coe_sub, hint, sub_zero]
  rw [← he]
  exact AddCircle.equivIco_coe_of_mem hmem

noncomputable def affineCyclicTorusCarry {r N : ℕ}
    (t c : Fin r → ℝ) (h₀ h : ZMod N) (i : Fin r) : ℤ :=
  ⌊((h.val : ℝ) - h₀.val) * t i - c i + 1 / 2⌋

theorem affineCyclicTorusLocalLift_eq_sub_carry {r N : ℕ}
    (t c : Fin r → ℝ) (h₀ h : ZMod N) (i : Fin r) :
    affineCyclicTorusLocalLift t c h₀ h i =
      ((h.val : ℝ) - h₀.val) * t i - c i - affineCyclicTorusCarry t c h₀ h i :=
  centeredCircleLift_eq_sub_floor _

end Erdos3

end

section

namespace Erdos3

noncomputable def centeredTorusLift {ι : Type*} (x : ι → AddCircle (1 : ℝ)) : ι → ℝ :=
  fun i => centeredCircleLift (x i)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeLocalPivotVerticalPartners
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem finite_double_normalization {X : Type*} (S : Finset X) (f g : X → ℂ) (b : ℝ)
    (hcorr : Real.exp (-b) ≤ ‖𝔼 x ∈ S, f x * g x‖) :
    Real.exp (-(3 * b)) ≤ ‖𝔼 x ∈ S,
      ((Real.exp (-b) : ℂ) * f x) * ((Real.exp (-b) : ℂ) * g x)‖ := by
  have hmean : (𝔼 x ∈ S, ((Real.exp (-b) : ℂ) * f x) * ((Real.exp (-b) : ℂ) * g x)) =
      ((Real.exp (-b) : ℂ) * (Real.exp (-b) : ℂ)) * (𝔼 x ∈ S, f x * g x) := by
    rw [Finset.mul_expect]
    apply Finset.expect_congr rfl
    intro x _
    ring
  rw [hmean, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  calc
    Real.exp (-(3 * b)) = (Real.exp (-b) * Real.exp (-b)) * Real.exp (-b) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hcorr (by positivity)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FixedObservableCorrelation
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem pi_fin_card_le_exp {α : Type*} [Fintype α] [DecidableEq α]
    (n : α → ℕ) {p q : ℝ} (hq : 0 ≤ q) (hα : (Fintype.card α : ℝ) ≤ p)
    (hn : ∀ a, (n a : ℝ) ≤ Real.exp q) :
    (Fintype.card (∀ a, Fin (n a)) : ℝ) ≤ Real.exp (p * q) := by
  rw [Fintype.card_pi, Nat.cast_prod]
  simp only [Fintype.card_fin]
  calc
    (∏ a, (n a : ℝ)) ≤ ∏ _a : α, Real.exp q :=
      Finset.prod_le_prod (fun _ _ => Nat.cast_nonneg _) (fun a _ => hn a)
    _ = Real.exp ((Fintype.card α : ℝ) * q) := by
      rw [Finset.prod_const, Finset.card_univ, Real.exp_nat_mul]
    _ ≤ _ := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hα hq)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.CoordinatewiseLipschitz
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal

theorem lipschitzWith_of_coordinatewise {ι : Type*} [Fintype ι] [DecidableEq ι]
    {X : ι → Type*} [∀ i, PseudoMetricSpace (X i)] {Y : Type*} [PseudoMetricSpace Y]
    (f : (∀ i, X i) → Y) (C : ι → ℝ≥0)
    (h : ∀ i x, LipschitzWith (C i) (fun a => f (Function.update x i a))) :
    LipschitzWith (∑ i, C i) f := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  let z (S : Finset ι) : ∀ i, X i := fun i => if i ∈ S then x i else y i
  have hbound (S : Finset ι) : dist (f (z S)) (f y) ≤ ∑ i ∈ S, (C i : ℝ) * dist (x i) (y i) := by
    induction S using Finset.induction_on with
    | empty => simp only [z, Finset.notMem_empty, ite_false, Finset.sum_empty, dist_self, le_refl]
    | @insert i S hi ih =>
      have heq : z (insert i S) = Function.update (z S) i (x i) := by
        funext j
        by_cases hji : j = i
        · subst j
          simp only [z, Finset.mem_insert_self, ite_true, Function.update_self]
        · simp only [z, Finset.mem_insert, hji, false_or, Function.update_of_ne hji]
      have hold : z S = Function.update (z S) i (y i) := by
        funext j
        by_cases hji : j = i
        · subst j
          simp only [z, hi, ite_false, Function.update_self]
        · rw [Function.update_of_ne hji]
      have hstep : dist (f (z (insert i S))) (f (z S)) ≤ (C i : ℝ) * dist (x i) (y i) := by
        calc
          _ = dist (f (Function.update (z S) i (x i))) (f (Function.update (z S) i (y i))) := by
            rw [heq]
            exact congrArg (fun v => dist (f (Function.update (z S) i (x i))) (f v)) hold
          _ ≤ _ := (h i (z S)).dist_le_mul _ _
      have htri : dist (f (z (insert i S))) (f y) ≤
          (C i : ℝ) * dist (x i) (y i) + ∑ j ∈ S, (C j : ℝ) * dist (x j) (y j) :=
        (dist_triangle _ _ _).trans (add_le_add hstep ih)
      simpa only [Finset.sum_insert hi] using htri
  have htotal : dist (f x) (f y) ≤ ∑ i, (C i : ℝ) * dist (x i) (y i) := by
    simpa only [z, Finset.mem_univ, ite_true] using hbound Finset.univ
  calc
    _ ≤ ∑ i, (C i : ℝ) * dist (x i) (y i) := htotal
    _ ≤ ∑ i, (C i : ℝ) * dist x y := Finset.sum_le_sum
      (fun i _ => mul_le_mul_of_nonneg_left (dist_le_pi_dist x y i) (C i).coe_nonneg)
    _ = ((∑ i, C i : ℝ≥0) : ℝ) * dist x y := by rw [NNReal.coe_sum, Finset.sum_mul]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.NativeIntegerHalving
namespace OAI

section

namespace Erdos3

open scoped TensorProduct BigOperators

noncomputable def pairParityIndicator (r : Fin 2 → ZMod 2) (x : Fin 2 → ℤ) : ℂ :=
  if (fun i => (x i : ZMod 2)) = r then 1 else 0

theorem pairParityIndicator_product (r : Fin 2 → ZMod 2) (x : Fin 2 → ℤ) :
    pairParityIndicator r x =
      (if (x 0 : ZMod 2) = r 0 then 1 else 0) *
        (if (x 1 : ZMod 2) = r 1 then 1 else 0) := by
  classical
  have heq : (fun i => (x i : ZMod 2)) = r ↔ (x 0 : ZMod 2) = r 0 ∧ (x 1 : ZMod 2) = r 1 := by
    constructor
    · intro h
      exact ⟨congrFun h 0, congrFun h 1⟩
    · rintro ⟨h0, h1⟩
      funext i
      fin_cases i <;> assumption
  unfold pairParityIndicator
  simp only [heq]
  split_ifs <;> simp_all

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeBoundedVariablePatchExpansion
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {α : Type*} [Fintype α] {κ X : α → Type*}
  (ψ : ∀ a, κ a → X a → ℝ)

noncomputable def productPartitionWeight (j : ∀ a, κ a) (x : ∀ a, X a) : ℝ :=
  ∏ a, ψ a (j a) (x a)

theorem productPartitionWeight_nonneg (hψ : ∀ a j x, 0 ≤ ψ a j x)
    (j : ∀ a, κ a) (x : ∀ a, X a) : 0 ≤ productPartitionWeight ψ j x :=
  Finset.prod_nonneg (fun a _ => hψ a (j a) (x a))

theorem productPartitionWeight_pos_coordinate (hψ : ∀ a j x, 0 ≤ ψ a j x)
    (j : ∀ a, κ a) (x : ∀ a, X a) (hx : 0 < productPartitionWeight ψ j x) (a : α) :
    0 < ψ a (j a) (x a) := by
  classical
  apply lt_of_le_of_ne (hψ a (j a) (x a))
  intro hz
  have hw : productPartitionWeight ψ j x = 0 :=
    Finset.prod_eq_zero (Finset.mem_univ a) hz.symm
  linarith

variable [DecidableEq α] [∀ a, Fintype (κ a)]

theorem sum_productPartitionWeight (hsum : ∀ a x, ∑ j, ψ a j x = 1) (x : ∀ a, X a) :
    ∑ j, productPartitionWeight ψ j x = 1 := by
  unfold productPartitionWeight
  rw [← Fintype.prod_sum (fun a j => ψ a j (x a))]
  simp only [hsum, Finset.prod_const_one]

variable [∀ a, PseudoMetricSpace (X a)]

omit [DecidableEq α] [∀ a, Fintype (κ a)] in
theorem productPartitionWeight_diameter {rho : ℝ} (hrho : 0 ≤ rho)
    (hψ : ∀ a j x, 0 ≤ ψ a j x)
    (hdiam : ∀ a j x y, 0 < ψ a j x → 0 < ψ a j y → dist x y ≤ rho)
    (j : ∀ a, κ a) (x y : ∀ a, X a)
    (hx : 0 < productPartitionWeight ψ j x) (hy : 0 < productPartitionWeight ψ j y) :
    dist x y ≤ rho := by
  apply (dist_pi_le_iff hrho).mpr
  intro a
  exact hdiam a (j a) (x a) (y a)
    (productPartitionWeight_pos_coordinate ψ hψ j x hx a)
    (productPartitionWeight_pos_coordinate ψ hψ j y hy a)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeWeightPairRemoval
namespace OAI

section

namespace Erdos3.NativeMixedReductionData

variable {s : ℕ}
  {p P : ℝ}

def secondInput (i : Fin 3) : ((Fin 5 → ℤ) →+ ℤ) where
  toFun x := (![x 1, x 3, x 4] : Fin 3 → ℤ) i
  map_zero' := by fin_cases i <;> rfl
  map_add' x y := by fin_cases i <;> rfl

def fourthInput (i : Fin 3) : ((Fin 5 → ℤ) →+ ℤ) where
  toFun x := (![x 1 + x 2 - x 0, x 3, x 4] : Fin 3 → ℤ) i
  map_zero' := by fin_cases i <;> rfl
  map_add' x y := by
    fin_cases i
    · change (x 1 + y 1) + (x 2 + y 2) - (x 0 + y 0) =
        (x 1 + x 2 - x 0) + (y 1 + y 2 - y 0)
      ring
    · rfl
    · rfl

def parallelogramInput (i : Fin 4) : ((Fin 5 → ℤ) →+ ℤ) where
  toFun x := (![x 0, x 1, x 2, x 3] : Fin 4 → ℤ) i
  map_zero' := by fin_cases i <;> rfl
  map_add' x y := by fin_cases i <;> rfl

end Erdos3.NativeMixedReductionData

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeMeanRowCorrelation
namespace OAI

section

namespace Erdos3

open scoped BigOperators TensorProduct

theorem mean_row_weighted_sum_norm_le {H X I : Type*} [Fintype H] [Fintype X] [Fintype I]
    (c : I → ℂ) (F : I → H → X → ℂ) :
    (𝔼 h, ‖𝔼 x, ∑ i, c i * F i h x‖) ≤ ∑ i, ‖c i‖ * (𝔼 h, ‖𝔼 x, F i h x‖) := by
  have hp (h : H) : ‖𝔼 x, ∑ i, c i * F i h x‖ ≤ ∑ i, ‖c i‖ * ‖𝔼 x, F i h x‖ := by
    simp_rw [Finset.expect_sum_comm, ← Finset.mul_expect]
    exact (norm_sum_le _ _).trans_eq (by simp only [norm_mul])
  have hm := Finset.expect_le_expect (s := Finset.univ) (fun h _ => hp h)
  simpa only [Finset.expect_sum_comm, ← Finset.mul_expect] using hm

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RankIntervalFactorization
namespace OAI

section

namespace Erdos3

theorem card_selected_four_le {ι : Type*} [Fintype ι] (K : Finset (Fin 4)) :
    Fintype.card (Σ _ : K, ι) ≤ Fintype.card (Σ _ : Fin 4, ι) := by
  let f : (Σ _ : K, ι) → (Σ _ : Fin 4, ι) := fun j => ⟨j.1, j.2⟩
  apply Fintype.card_le_of_injective f
  intro x y h
  exact Sigma.ext (Subtype.ext (congrArg Sigma.fst h))
    (heq_of_eq (congrArg (fun z : Σ _ : Fin 4, ι => z.2) h))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RankDependentInputBudget
namespace OAI

section

namespace Erdos3

def rankDependentInputBudget (z : ℝ) : ℝ :=
  2 * z + 2 * (z + ((z + 2) ^ 3 + (z + 2) ^ 36)) +
    ((z + 2) ^ 3 + (z + 2) ^ 18 + z) + 2

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.BoundedNativeDependentApproximations
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [Fintype G]

def fourSparseAnchorChange (h : G) : (G × G) ≃ (G × G) where
  toFun u := (u.1, u.1 - u.2 + h)
  invFun u := (u.1, u.1 - u.2 + h)
  left_inv := by
    rintro ⟨a, b⟩
    apply Prod.ext
    · rfl
    · dsimp
      abel_nf
  right_inv := by
    rintro ⟨a, b⟩
    apply Prod.ext
    · rfl
    · dsimp
      abel_nf

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeCoveredCommonFactorization
namespace OAI

section

namespace Erdos3

open Module
open scoped TensorProduct

theorem toAdd_hom_corrected_factor {G V : Type*} [Group G] [AddCommGroup V]
    (f : G →* Multiplicative V) (g₀ ε g γ : G) :
    Multiplicative.toAdd (f (g₀⁻¹ * ε⁻¹ * g * γ⁻¹)) =
      Multiplicative.toAdd (f g) - Multiplicative.toAdd (f g₀) -
        Multiplicative.toAdd (f ε) - Multiplicative.toAdd (f γ) := by
  simp only [map_mul, map_inv, toAdd_mul, toAdd_inv]
  abel

end Erdos3

end

section

namespace Erdos3

open Module

theorem toAdd_hom_corrected_reference {G V : Type*} [Group G] [AddCommGroup V]
    (f : G →* Multiplicative V) (ε g γ : G) :
    Multiplicative.toAdd (f (ε⁻¹ * g * γ⁻¹)) =
      Multiplicative.toAdd (f g) - Multiplicative.toAdd (f ε) - Multiplicative.toAdd (f γ) := by
  simp only [map_mul, map_inv, toAdd_mul, toAdd_inv]
  abel

theorem sub_corrected_reference_add_errors {V : Type*} [AddCommGroup V]
    (x y a b a₀ b₀ : V) :
    x - (y - a₀ - b₀) - (a + a₀) - (b + b₀) = x - y - a - b := by
  abel

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MarkedPureEvaluation
namespace OAI

section

namespace Erdos3

open scoped TensorProduct

def monoidHomOfSurjectiveComposition {A B C : Type*} [Monoid A] [Monoid B] [Monoid C]
    (f : A →* B) (hf : Function.Surjective f) (g : A →* C) (k : B → C)
    (hcomp : ∀ a, k (f a) = g a) : B →* C where
  toFun := k
  map_one' := by
    calc
      k 1 = k (f 1) := congrArg k f.map_one.symm
      _ = g 1 := hcomp 1
      _ = 1 := g.map_one
  map_mul' x y := by
    obtain ⟨a, rfl⟩ := hf x
    obtain ⟨b, rfl⟩ := hf y
    rw [← f.map_mul, hcomp, hcomp, hcomp, g.map_mul]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.MarkedEvaluationHeightBudget
namespace OAI

section

namespace Erdos3

noncomputable def markedShiftInputBudget (s : ℕ) (p : ℝ) : ℝ :=
  p * (s + 1 : ℕ) * (p + 1) ^ s + p + (s + 1 : ℕ)

noncomputable def markedShiftHeightBudget (s : ℕ) (p : ℝ) : ℝ :=
  (markedShiftInputBudget s p + 2) ^ (5082 * s + 3564)

theorem markedShiftInputBudget_nonneg (s : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ markedShiftInputBudget s p := by
  unfold markedShiftInputBudget
  positivity

theorem le_markedShiftInputBudget (s : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    p ≤ markedShiftInputBudget s p := by
  unfold markedShiftInputBudget
  exact (le_add_of_nonneg_left (by positivity)).trans
    (le_add_of_nonneg_right (Nat.cast_nonneg _))

theorem step_le_markedShiftInputBudget (s : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    (s + 1 : ℕ) ≤ markedShiftInputBudget s p := by
  unfold markedShiftInputBudget
  exact le_add_of_nonneg_left (by positivity)

theorem markedShift_dimension_budget (s n t : ℕ) {p : ℝ} (hp : 0 ≤ p)
    (hn : (n : ℝ) ≤ p) (ht : (t : ℝ) ≤ p) :
    ((n * (s + 1) * (t + 1) ^ s + t : ℕ) : ℝ) ≤ markedShiftInputBudget s p := by
  calc
    _ ≤ p * (s + 1 : ℕ) * (p + 1) ^ s + p := by
      push_cast
      gcongr
    _ ≤ _ := le_add_of_nonneg_right (Nat.cast_nonneg (s + 1))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.MarkedDirectionLatticeScale
namespace OAI

section

namespace Erdos3

open Module
open scoped Matrix

theorem direction_lattice_scale_bound (d t B H : ℕ) {p : ℝ} (hp : 0 ≤ p)
    (hd : (d : ℝ) ≤ p) (ht : (t : ℝ) ≤ p)
    (hB : (B : ℝ) ≤ Real.exp p) (hH : (H : ℝ) ≤ Real.exp p) :
    ((B * H ^ (d * t) : ℕ) : ℝ) ≤ Real.exp ((p + 2) ^ 3) := by
  rw [Nat.cast_mul, Nat.cast_pow]
  calc
    _ ≤ Real.exp p * (Real.exp p) ^ (d * t) :=
      mul_le_mul hB (pow_le_pow_left₀ (Nat.cast_nonneg _) hH _) (by positivity) (Real.exp_nonneg _)
    _ = Real.exp (p + (d * t : ℕ) * p) := by rw [← Real.exp_nat_mul, ← Real.exp_add]
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      have hdt : (d : ℝ) * t ≤ p * p :=
        mul_le_mul hd ht (Nat.cast_nonneg _) hp
      have hmul := mul_le_mul_of_nonneg_right hdt hp
      push_cast
      nlinarith only [hp, hmul, sq_nonneg p]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.InducedMarkedBudget
namespace OAI

section

namespace Erdos3

open scoped NNReal

def inducedMarkedLogBudget (C A B : ℕ) (p : ℝ) : ℝ :=
  let q := 6 * p + (p + C) ^ C + 2
  let a := (q + A) ^ A
  let t := a + q + 8 * p + 3
  let b := (t + B) ^ B
  2 * (b + 2 * a + 8 * p + (p + 3) ^ 2 + q + 10) + 132

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.UnitVerticalCyclicDifference
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal

noncomputable def cyclicSecondDifference {N : ℕ} (u v : (Fin 2 → ℤ) → ℂ)
    (k : ZMod N) (h : ℤ) (n : ZMod N) : ℂ :=
  u ![h, (n.val : ℤ)] * star (v ![h, ((n + k).val : ℤ)])

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.NativeIntegerDivision
namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def pairResidueIndicator {d : ℕ} (r : Fin 2 → ZMod d) (x : Fin 2 → ℤ) : ℂ :=
  if (fun i => (x i : ZMod d)) = r then 1 else 0

theorem pairResidueIndicator_product {d : ℕ} (r : Fin 2 → ZMod d) (x : Fin 2 → ℤ) :
    pairResidueIndicator r x =
      (if (x 0 : ZMod d) = r 0 then 1 else 0) *
        (if (x 1 : ZMod d) = r 1 then 1 else 0) := by
  classical
  have heq : (fun i => (x i : ZMod d)) = r ↔ (x 0 : ZMod d) = r 0 ∧ (x 1 : ZMod d) = r 1 := by
    constructor
    · intro h
      exact ⟨congrFun h 0, congrFun h 1⟩
    · rintro ⟨h0, h1⟩
      funext i
      fin_cases i <;> assumption
  unfold pairResidueIndicator
  simp only [heq]
  split_ifs <;> simp_all

theorem card_pairResidue_le_exp (d : ℕ) [NeZero d] :
    (Fintype.card (Fin 2 → ZMod d) : ℝ) ≤ Real.exp ((d : ℝ) ^ 2) := by
  simp only [Fintype.card_fun, ZMod.card, Fintype.card_fin, Nat.cast_pow]
  linarith [Real.add_one_le_exp ((d : ℝ) ^ 2)]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.PartitionedAffineLogEnvelope
namespace OAI

section

namespace Erdos3

section Definitions
variable {A : Type*} [Semiring A]
def affineMinorDegreeEnvelope (D : A) : A := 1 + D * D
end Definitions

end Erdos3

end

end OAI
end


