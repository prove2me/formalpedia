-- Prove2me | Definitions.Def_OAIE3v2B095
-- name    : OAIE3v2B095
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T10:28:05.564759+00:00
-- url     : https://prove2.me/theorems/07713c73-564d-4e62-84ed-7a87641477ec
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 97 of 311
-- statement:
--   Definitions bundle 97 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B068`, `OAIE3v2B069`, `OAIE3v2B070`, `OAIE3v2B071`, `OAIE3v2B072`, `OAIE3v2B073`, `OAIE3v2B074`, `OAIE3v2B075`, `OAIE3v2B076`, `OAIE3v2B077`, `OAIE3v2B078` of this split.
--
--   Modules: `Dynamics/GlobalErrorSplittingBudget.lean`, `Dynamics/PreparedFiniteStageNativeBudget.lean`, `Estimates/AnchoredReflectedFamily.lean`, `Estimates/CubeSignalAlgebra.lean`, `Estimates/DilationPairFiltration.lean`, `Estimates/EuclideanDerivativeCovolume.lean`, `Estimates/LieTreeMultidegree.lean`, `Estimates/MixedRootLosses.lean`, `Estimates/PositiveCyclicCorrelation.lean`, `Estimates/RationalLieSubalgebra.lean`, `Estimates/RealificationFixedSubmodule.lean`, `Estimates/RealifiedMultidegree.lean`, `Estimates/RealifiedReconstruction.lean`, `Estimates/TailReflectionInduction.lean`, `Estimates/UnitVerticalMeanRowCorrelation.lean`, `Estimates/WeightedSummandCorrelation.lean`, `Fourier/LogCharacterBudget.lean`, `Fourier/RealQuarterTorusExtension.lean`, `Geometry/AllocatedExternalCandidateSpatialNativeBudget.lean`, `Geometry/BoxCornerMean.lean`, `Geometry/FiniteChoiceLeafCoordinates.lean`, `Geometry/FiniteNormalizedChartCorrection.lean`, `Geometry/FullChartHomogeneousCorrection.lean`, `Geometry/RealCoordinateFunctionals.lean`, `Geometry/SubmoduleQuotientCoordinates.lean`, `Lattices/LatticeCoordinateLifts.lean`, `Lattices/LatticeMinorNormBound.lean`, `Lattices/NativeRetainedIntegerMultilinearQuadruples.lean`, `Linear/DerivativeVerticalBasis.lean`, `Linear/RationalTaggedSpanProjection.lean`, `Nilpotent/BCHChartCutoffSmooth.lean`, `Nilpotent/BCHQuotientLocalIsometry.lean`, `Nilpotent/BCHSubgroupGridExistence.lean`, `Nilpotent/FactorwiseBCHCovers.lean`, `Nilpotent/FilteredAdjointFirstBracket.lean`, `Nilpotent/SquarefreeBracketHeight.lean`, `Polynomial/AdaptedPolynomialSubstitution.lean`, `Polynomial/ControlledPositivePolynomialDownsets.lean`, `Polynomial/ExtendedPolynomialValues.lean`, `Polynomial/MajorWeightedDegreeTools.lean`, `Polynomial/PolynomialCoefficientGridDenominator.lean`, `Polynomial/TranslationPhaseQuotient.lean`, `Probability/EuclideanDerivativeDensityCovolume.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B068
import Definitions.Def_OAIE3v2B069
import Definitions.Def_OAIE3v2B070
import Definitions.Def_OAIE3v2B071
import Definitions.Def_OAIE3v2B072
import Definitions.Def_OAIE3v2B073
import Definitions.Def_OAIE3v2B074
import Definitions.Def_OAIE3v2B075
import Definitions.Def_OAIE3v2B076
import Definitions.Def_OAIE3v2B077
import Definitions.Def_OAIE3v2B078

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.WeightedSummandCorrelation
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem exists_correlating_weighted_summand {Ω J : Type*} [Fintype J]
    {Q : Finset Ω} (hQ : Q.Nonempty) (f u : Ω → ℂ) (v : J → Ω → ℂ) (c : J → ℂ)
    {ρ M B : ℝ} (hρ : 0 < ρ) (hM : 0 < M) (hB : 0 < B)
    (hcard : (Fintype.card J : ℝ) ≤ M) (hc : ∀ j, ‖c j‖ ≤ B)
    (hf : ∀ x ∈ Q, ‖f x‖ ≤ 1)
    (happrox : ∀ x ∈ Q, ‖(∑ j, c j * v j x) - u x‖ ≤ ρ / 2)
    (hcorr : ρ ≤ ‖finiteCorrelation Q f u‖) :
    ∃ j, ρ / (2 * M * B) ≤ ‖finiteCorrelation Q f (v j)‖ := by
  obtain ⟨j, hj⟩ := exists_correlating_summand hQ f u (fun j x => c j * v j x)
    hρ hM hcard hf happrox hcorr
  have heq : finiteCorrelation Q f (fun x => c j * v j x) =
      star (c j) * finiteCorrelation Q f (v j) := by
    unfold finiteCorrelation
    rw [Finset.mul_expect]
    apply Finset.expect_congr rfl
    intro x _
    simp only [star_mul]
    ring
  rw [heq, norm_mul, norm_star] at hj
  refine ⟨j, ?_⟩
  rw [← div_div]
  apply (div_le_iff₀ hB).mpr
  simpa only [mul_comm] using hj.trans
    (mul_le_mul_of_nonneg_right (hc j) (norm_nonneg _))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RationalLieSubalgebra
namespace OAI

section

namespace Erdos3

open Module
open scoped Matrix

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

variable {L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
  [DecidableEq ι] [DecidableEq κ]

theorem exists_bounded_lie_quotient_section (e : Basis ι ℚ L) (b : Basis κ ℚ M)
    (φ : L →ₗ⁅ℚ⁆ M) (hφ : Function.Surjective φ) {H : ℕ} (hH : 1 ≤ H)
    (hc : ∀ i j k, RationalHeightLE (lieStructureConstants e i j k) H)
    (hD : ∀ i j, RationalHeightLE (LinearMap.toMatrix e b φ.toLinearMap i j) H) :
    ∃ S : Matrix ι κ ℚ, LinearMap.toMatrix e b φ.toLinearMap * S = 1 ∧
      (∀ i j, RationalHeightLE (S i j) (rationalSolveHeight (Fintype.card κ) H)) ∧
      ∀ i j k, RationalHeightLE (lieStructureConstants b i j k)
        (rationalLieStructureHeight (Fintype.card ι) (max H (rationalSolveHeight (Fintype.card κ) H))) := by
  obtain ⟨S, hS, hSH⟩ := exists_bounded_rational_section (LinearMap.toMatrix e b φ.toLinearMap)
    (basisMatrix_surjective e b φ.toLinearMap hφ) hH hD
  refine ⟨S, hS, hSH, ?_⟩
  intro i j k
  rw [lieStructureConstants_quotient_matrix e b φ S hS]
  exact transportedLieConstants_height_uniform _ _ _
    (fun u v w => (hc u v w).mono (le_max_left _ _))
    (fun u v => (hD u v).mono (le_max_left _ _))
    (fun u v => (hSH u v).mono (le_max_right _ _)) i j k

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.BCHSubgroupGridExistence
namespace OAI

section

namespace Erdos3.NilpotentLieBCHGroup

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem conjugationCoord_nsmul (g : NilpotentLieBCHGroup L s hnil) (n : ℕ) (x : L) :
    conjugationCoord g (n • x) = n • conjugationCoord g x := by
  have he : (⟨n • x⟩ : NilpotentLieBCHGroup L s hnil) =
      (⟨x⟩ : NilpotentLieBCHGroup L s hnil) ^ n := by
    apply ext
    exact (coord_pow _ _).symm
  change ((MulAut.conj g) (⟨n • x⟩ : NilpotentLieBCHGroup L s hnil)).coord = _
  rw [he, map_pow, coord_pow]
  rfl

end Erdos3.NilpotentLieBCHGroup

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.ExtendedPolynomialValues
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module
open scoped TensorProduct

variable {σ R S V W : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup V] [Module R V] [Module S V] [IsScalarTower R S V]
  [AddCommGroup W] [Module R W] [Module S W] [IsScalarTower R S W]

theorem eval₂_map (f : V →ₗ[S] W) (x : σ → S) (p : VectorPolynomial σ R V) :
    eval₂ x (map (f.restrictScalars R) p) = f (eval₂ x p) := by
  induction p using TensorProduct.induction_on with
  | zero => simp
  | tmul q v =>
    change eval₂ x (q ⊗ₜ[R] f v) = f (eval₂ x (q ⊗ₜ[R] v))
    rw [eval₂_tmul, eval₂_tmul, map_smul]
  | add p q hp hq => simp only [map_add, hp, hq]

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.AdaptedPolynomialSubstitution
namespace OAI


namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial

variable {σ L M : Type*} [LieRing L] [LieAlgebra ℚ L]
  [LieRing M] [LieAlgebra ℚ M] {s t : ℕ}
  (F : NilpotentLieFiltration L s)

variable {F}

variable (F)

theorem polynomialOrbitEval_step_zero (F : NilpotentLieFiltration L 0)
    (w : σ → ℕ) (p : F.PolynomialOrbit w) (x : σ → ℤ) :
    F.polynomialOrbitEval w x p = 1 := by
  apply NilpotentLieBCHGroup.ext
  change (F.polynomialOrbitEval w x p).coord = 0
  have h : (F.polynomialOrbitEval w x p).coord ∈ F.layer 1 := by simp [F.one_eq_top]
  simpa only [F.terminal, Submodule.mem_bot] using h

end Erdos3.NilpotentLieFiltration


end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.DilationPairFiltration
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

def dilationPairFiltrationLayerEquiv (q : ℚ) (n : ℕ) (hn : 1 ≤ n) :
    (F.dilationPairFiltration q).layer n ≃ₗ[ℚ] F.dilationPairLayer q n where
  toFun x := ⟨x.val.val, x.property⟩
  invFun x := ⟨⟨x.val, F.dilationPairLayer_antitone q hn x.property⟩, x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RealifiedMultidegree
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

theorem rational_inclusion_mem_realLayer {i : ℕ} {a : L} (ha : a ∈ F.layer i) :
    rationalLieInclusion a ∈ F.realLayer i :=
  LieSubmodule.tmul_mem_baseChange_of_mem 1 ha

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.BCHChartCutoffSmooth
namespace OAI

section

namespace Erdos3.NilpotentLieBCHGroup

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥} [TopologicalSpace L]

instance instT2Space [T2Space L] : T2Space (NilpotentLieBCHGroup L s hnil) :=
  (coordHomeomorph (hnil := hnil)).isEmbedding.t2Space

end Erdos3.NilpotentLieBCHGroup

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.BCHQuotientLocalIsometry
namespace OAI

section

namespace Erdos3.NilpotentLieBCHGroup

open Module _root_.Set

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [IsScalarTower ℚ ℝ L] [TopologicalSpace L] [IsTopologicalAddGroup L]
  [ContinuousSMul ℝ L] [T2Space L]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem quotientMetricSpace_edist_mk (e : Basis ι ℝ L)
    (Γ : Subgroup (NilpotentLieBCHGroup L s hnil))
    (hΓ : IsClosed (Γ : Set (NilpotentLieBCHGroup L s hnil)))
    (x y : NilpotentLieBCHGroup L s hnil) :
    letI := rightMetricSpace (hnil := hnil) e
    letI := quotientMetricSpace e Γ hΓ
    edist (QuotientGroup.mk x : _ ⧸ Γ) (QuotientGroup.mk y) = ⨅ γ : Γ, edist x (y * γ) := rfl

end Erdos3.NilpotentLieBCHGroup

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.LieTreeMultidegree
namespace OAI

section

namespace Erdos3

variable {R I J L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]

theorem lieTreeOccurrenceMultilinear_apply (a : FreeMagma I) :
    ∀ v : LieTreeOccurrences a → L,
      lieTreeOccurrenceMultilinear (R := R) a v = lieTreeEval v (lieTreeOccurrenceTree a) := by
  induction a using FreeMagma.rec with
  | of i => intro v; rfl
  | mul a b ha hb =>
    intro v
    change ⁅lieTreeOccurrenceMultilinear a (v ∘ Sum.inl),
      lieTreeOccurrenceMultilinear b (v ∘ Sum.inr)⁆ = _
    rw [ha, hb]
    change _ = ⁅lieTreeEval v (FreeMagma.map Sum.inl (lieTreeOccurrenceTree a)),
      lieTreeEval v (FreeMagma.map Sum.inr (lieTreeOccurrenceTree b))⁆
    rw [lieTreeEval_relabel, lieTreeEval_relabel]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.SquarefreeBracketHeight
namespace OAI

section

namespace Erdos3

open Module
open scoped Matrix TensorProduct

variable {L ι κ ν : Type*} [LieRing L] [LieAlgebra ℚ L]
  {E V : Submodule ℚ L}

theorem bracketSystemMatrix_height {α : Type*} [Fintype α]
    (b : Basis α ℚ L) (e : Basis ν ℚ E) (f : Basis ι ℚ (L ⧸ V)) (k : κ → L)
    {H A B C : ℕ}
    (hbr : ∀ i j n, RationalHeightLE (lieStructureConstants b i j n) H)
    (he : ∀ n i, RationalHeightLE (b.repr (e n : L) i) A)
    (hk : ∀ t i, RationalHeightLE (b.repr (k t) i) B)
    (hq : ∀ i n, RationalHeightLE (f.repr (V.mkQ (b i)) n) C) (bi : κ × ι) (n : ν) :
    RationalHeightLE (bracketSystemMatrix e f k bi n)
      ((Fintype.card α + 1) *
        (((Fintype.card α ^ 2 + 1) * (H * A * B) ^ (Fintype.card α ^ 2)) * C) ^
          Fintype.card α) :=
  linearMap_coordinate_height b f V.mkQ hq _
    (lie_bracket_coordinate_height b hbr (e n : L) (k bi.1) (he n) (hk bi.1)) bi.2

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

theorem boxCornerProduct_succ {n : ℕ} {X : Type*} (F : (Fin (n + 1) → X) → ℂ)
    (u v : Fin (n + 1) → X) :
    boxCornerProduct F u v =
      boxCornerProduct (fun x => F (Fin.cons (u 0) x)) (Fin.tail u) (Fin.tail v) *
        star (boxCornerProduct (fun x => F (Fin.cons (v 0) x)) (Fin.tail u) (Fin.tail v)) := by
  simp only [boxCornerProduct]
  rw [prod_bool_tuple_succ]
  simp only [booleanWeight_cons_false, booleanWeight_cons_true, boxCorner_cons_false,
    boxCorner_cons_true, conjugationPower, RingHom.comp_apply, starRingEnd_apply, star_prod]

theorem iteratedBoxDifference_eq_cornerProduct {X Z : Type*} (n : ℕ)
    (F : (Fin n → X) → Z → ℂ) (u v : Fin n → X) (z : Z) :
    iteratedBoxDifference n F u v z = boxCornerProduct (fun x => F x z) u v := by
  induction n with
  | zero =>
    rw [boxCornerProduct, Fintype.prod_subsingleton _ (default : Fin 0 → Bool)]
    simp only [booleanWeight, Fin.sum_univ_zero, conjugationPower, RingHom.id_apply, iteratedBoxDifference]
    congr 1
    funext i
    exact Fin.elim0 i
  | succ n ih =>
    rw [iteratedBoxDifference, ih, boxCornerProduct_mul, boxCornerProduct_star, boxCornerProduct_succ]

theorem boxPhaseMoment_eq_expect_cornerProduct {n : ℕ} {X : Type*} [Fintype X]
    (F : (Fin n → X) → ℂ) :
    boxPhaseMoment n F = 𝔼 u, 𝔼 v, boxCornerProduct F u v := by
  simp only [boxPhaseMoment, iteratedBoxDifference_eq_cornerProduct]

theorem boxCornerProduct_map {n : ℕ} {X Y : Type*} (φ : X → Y)
    (F : (Fin n → Y) → ℂ) (u v : Fin n → X) :
    boxCornerProduct (fun x => F (fun i => φ (x i))) u v =
      boxCornerProduct F (fun i => φ (u i)) (fun i => φ (v i)) := by
  unfold boxCornerProduct
  apply Finset.prod_congr rfl
  intro ω _
  apply congrArg (conjugationPower (booleanWeight ω))
  change F (fun i => φ (boxCorner u v ω i)) =
    F (boxCorner (fun i => φ (u i)) (fun i => φ (v i)) ω)
  apply congrArg F
  funext i
  cases h : ω i <;> simp [boxCorner, h]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem boxCornerAnchor_norm_le_one {n : ℕ} {X : Type*}
    (F : (Fin n → X) → ℂ) (hF : ∀ z, ‖F z‖ ≤ 1) (a z : Fin n → X) :
    ‖boxCornerAnchor F a z‖ ≤ 1 := by
  classical
  unfold boxCornerAnchor
  rw [norm_prod]
  apply Finset.prod_le_one (fun _ _ => norm_nonneg _)
  intro ω _
  rw [conjugationPower_eq_if_mod]
  split_ifs <;> simpa only [norm_star] using hF (boxCorner z a ω)

theorem boxCornerAnchor_map {n : ℕ} {X Y : Type*} (φ : X → Y)
    (F : (Fin n → Y) → ℂ) (a z : Fin n → X) :
    boxCornerAnchor (fun x => F (fun i => φ (x i))) a z =
      boxCornerAnchor F (fun i => φ (a i)) (fun i => φ (z i)) := by
  classical
  unfold boxCornerAnchor
  apply Finset.prod_congr rfl
  intro ω _
  apply congrArg (conjugationPower (booleanWeight ω))
  apply congrArg F
  funext i
  cases h : ω i <;> simp [boxCorner, h]

theorem exists_box_corner_anchor_correlation {n : ℕ} {X : Type*}
    [Fintype X] [Nonempty X] (F : (Fin n → X) → ℂ) :
    ∃ a : Fin n → X, (boxPhaseMoment n F).re ≤
      ‖𝔼 z : Fin n → X, F z * boxCornerAnchor F a z‖ := by
  have hm : boxPhaseMoment n F =
      𝔼 a : Fin n → X, 𝔼 z : Fin n → X, F z * boxCornerAnchor F a z := by
    rw [boxPhaseMoment_eq_expect_cornerProduct, Finset.expect_comm]
    simp_rw [boxCornerProduct_eq_mul_anchor]
  have hmean : (boxPhaseMoment n F).re =
      𝔼 a : Fin n → X, (𝔼 z : Fin n → X, F z * boxCornerAnchor F a z).re := by
    rw [hm, expect_re]
  obtain ⟨a, _, ha⟩ := Finset.exists_le_of_le_expect Finset.univ_nonempty hmean.le
  exact ⟨a, ha.trans (Complex.re_le_norm _)⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialCoefficientGridDenominator
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial

variable {σ : Type*}

theorem mem_integralRealPolynomialSubring_iff (P : MvPolynomial σ ℝ) :
    P ∈ integralRealPolynomialSubring σ ↔
      ∀ m, ∃ z : ℤ, (z : ℝ) = P.coeff m := by
  constructor
  · rintro ⟨Q, rfl⟩ m
    exact ⟨Q.coeff m, by simp [coeff_map]⟩
  · intro h
    apply MvPolynomial.mem_range_map_iff_coeffs_subset.mpr
    intro c hc
    obtain ⟨m, _, rfl⟩ := MvPolynomial.mem_coeffs_iff.mp hc
    exact h m

theorem X_mem_integralRealPolynomialSubring (i : σ) :
    (X i : MvPolynomial σ ℝ) ∈ integralRealPolynomialSubring σ :=
  ⟨X i, by simp⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.FilteredAdjointFirstBracket
namespace OAI

section

namespace Erdos3

namespace NilpotentAlgebraFiltration

variable {A : Type*} [Ring A] [Algebra ℚ A] (F : NilpotentAlgebraFiltration A 2)

theorem mul_eq_zero_of_degrees {i j : ℕ} {a b : A}
    (ha : a ∈ F.layer i) (hb : b ∈ F.layer j) (hij : 3 ≤ i + j) : a * b = 0 := by
  have h := F.antitone hij (F.mul_mem ha hb)
  simpa only [F.terminal, Submodule.mem_bot] using h

theorem exp_eq_quadratic {a : A} (ha : a ∈ F.layer 1) :
    IsNilpotent.exp a = 1 + a + (1 / 2 : ℚ) • a ^ 2 := by
  rw [IsNilpotent.exp_eq_sum (F.pow_eq_zero le_rfl ha)]
  norm_num [Finset.sum_range_succ]

theorem nilpotentBCH_eq_quadratic {a b : A} (ha : a ∈ F.layer 1)
    (hb : b ∈ F.layer 1) :
    nilpotentBCH a b = a + b + (1 / 2 : ℚ) • (a * b - b * a) := by
  have ha2 : a ^ 2 ∈ F.layer 2 := by simpa using F.pow_mem ha 2
  have hb2 : b ^ 2 ∈ F.layer 2 := by simpa using F.pow_mem hb 2
  have hab2 := F.mul_eq_zero_of_degrees ha hb2 (by decide)
  have ha2b := F.mul_eq_zero_of_degrees ha2 hb (by decide)
  have ha2b2 := F.mul_eq_zero_of_degrees ha2 hb2 (by decide)
  let q := (1 / 2 : ℚ) • a ^ 2 + a * b + (1 / 2 : ℚ) • b ^ 2
  have hq : q ∈ F.layer 2 :=
    (F.layer 2).add_mem ((F.layer 2).add_mem ((F.layer 2).smul_mem _ ha2)
      (F.mul_mem ha hb)) ((F.layer 2).smul_mem _ hb2)
  have hab : a + b ∈ F.layer 1 := (F.layer 1).add_mem ha hb
  have hp : IsNilpotent.exp a * IsNilpotent.exp b - 1 = a + b + q := by
    rw [F.exp_eq_quadratic ha, F.exp_eq_quadratic hb]
    simp only [add_mul, mul_add, one_mul, mul_one, smul_mul_assoc, mul_smul_comm,
      hab2, ha2b, ha2b2, smul_zero]
    dsimp [q]
    module
  have hq1 : q ∈ F.layer 1 := F.antitone (by decide) hq
  have hp2 : (a + b + q) ^ 2 = (a + b) ^ 2 := by
    rw [pow_two, add_mul (a + b) q (a + b + q),
      mul_add (a + b) (a + b) q, mul_add q (a + b) q,
      F.mul_eq_zero_of_degrees hab hq (by decide),
      F.mul_eq_zero_of_degrees hq hab (by decide),
      F.mul_eq_zero_of_degrees hq hq (by decide)]
    simp only [add_zero, pow_two]
  rw [nilpotentBCH, hp,
    nilpotentLog_eq_sum (F.pow_eq_zero le_rfl ((F.layer 1).add_mem hab hq1))]
  norm_num [Finset.sum_range_succ, hp2]
  dsimp [q]
  simp only [pow_two, add_mul, mul_add, smul_add, smul_sub]
  module

end NilpotentAlgebraFiltration

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L]
attribute [local instance] LieRing.ofAssociativeRing

theorem lieBCH_eq_quadratic_of_step_two {s : ℕ} (hs : 2 ≤ s)
    (hnil : LieModule.lowerCentralSeries ℚ L L 2 = ⊥) (a b : L) :
    lieBCH s a b = a + b + (1 / 2 : ℚ) • ⁅a, b⁆ := by
  let x : Fin 2 → FreeLieAlgebra ℚ (Fin 2) := FreeLieAlgebra.of ℚ
  let F := truncatedSeriesFiltration (A := FreeAlgebra ℚ (Fin 2)) 2
  have hx (i : Fin 2) : scaledFreeGenerator 2 i ∈ F.layer 1 :=
    scaledFreeGenerator_mem_layer 2 i
  have h : scaledFreeLieEval 2 (lieBCH s (x 0) (x 1)) =
      scaledFreeLieEval 2 (x 0 + x 1 + (1 / 2 : ℚ) • ⁅x 0, x 1⁆) := by
    simp only [map_lieBCH, map_add, map_smul, LieHom.map_lie, x, scaledFreeLieEval_of]
    rw [(F.extend hs).lieBCH_eq (hx 0) (hx 1)]
    exact F.nilpotentBCH_eq_quadratic (hx 0) (hx 1)
  have he := lie_lift_eq_of_scaledFreeLieEval_eq ![a, b] hnil h
  simpa only [map_lieBCH, map_add, map_smul, LieHom.map_lie, x,
    FreeLieAlgebra.lift_of_apply, Matrix.cons_val_zero, Matrix.cons_val_one] using he

end Erdos3

end

section

namespace Erdos3

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L]

theorem lieBCH_eq_quadratic_of_central_commutator {s : ℕ} (hs : 2 ≤ s)
    (a b : L) (ha : ⁅a, ⁅a, b⁆⁆ = 0) (hb : ⁅b, ⁅a, b⁆⁆ = 0) :
    lieBCH s a b = a + b + (1 / 2 : ℚ) • ⁅a, b⁆ := by
  let K := centralPairSubalgebra a b ha hb
  have haK : a ∈ K := Submodule.subset_span (by simp)
  have hbK : b ∈ K := Submodule.subset_span (by simp)
  have h := congrArg K.incl (lieBCH_eq_quadratic_of_step_two hs
    (centralPairSubalgebra_step_two a b ha hb) (⟨a, haK⟩ : K) (⟨b, hbK⟩ : K))
  simp only [map_lieBCH, map_add, map_smul, LieHom.map_lie] at h
  exact h

theorem lieBCH_conjugation_of_central_commutator {s : ℕ} (hs : 2 ≤ s)
    (a b : L) (ha : ⁅a, ⁅a, b⁆⁆ = 0) (hb : ⁅b, ⁅a, b⁆⁆ = 0) :
    lieBCH s (lieBCH s a b) (-a) = b + ⁅a, b⁆ := by
  have hba : ⁅b, a⁆ = -⁅a, b⁆ := (lie_skew b a).symm
  have hca : ⁅⁅a, b⁆, a⁆ = 0 := by rw [← lie_skew ⁅a, b⁆ a, ha, neg_zero]
  have hc : ⁅a + b + (1 / 2 : ℚ) • ⁅a, b⁆, -a⁆ = ⁅a, b⁆ := by
    simp only [add_lie, lie_neg, lie_self, smul_lie, hca,
      smul_zero, hba, neg_neg, zero_add, add_zero]
  have hu : ⁅a + b + (1 / 2 : ℚ) • ⁅a, b⁆, ⁅a, b⁆⁆ = 0 := by
    simp only [add_lie, ha, hb, smul_lie, lie_self, smul_zero, add_zero]
  rw [lieBCH_eq_quadratic_of_central_commutator hs a b ha hb,
    lieBCH_eq_quadratic_of_central_commutator hs _ _
      (by rw [hc, hu]) (by rw [hc, neg_lie, ha, neg_zero]), hc]
  module

end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration

open NilpotentLieBCHGroup

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)
  (U : LieSubalgebra ℚ L) (V : Submodule ℚ L)
  (hUV : ∀ u ∈ U, ∀ v ∈ V, ⁅u, v⁆ ∈ V)

include hUV

theorem invariant_sup_layer (j : ℕ) :
    ∀ u ∈ U, ∀ v ∈ V ⊔ F.layer j, ⁅u, v⁆ ∈ V ⊔ F.layer j := by
  intro u hu v hv
  obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.mp hv
  rw [lie_add]
  exact (V ⊔ F.layer j).add_mem (Submodule.mem_sup_left (hUV _ hu _ hx))
    (Submodule.mem_sup_right ((F.layerIdeal j).lie_mem hy))

theorem lie_mem_invariant_sup_next_layer (j : ℕ) {u v : L} (hu : u ∈ U)
    (hv : v ∈ V ⊔ F.layer j) : ⁅u, v⁆ ∈ V ⊔ F.layer (j + 1) := by
  obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.mp hv
  rw [lie_add]
  apply (V ⊔ F.layer (j + 1)).add_mem (Submodule.mem_sup_left (hUV _ hu _ hx))
  apply Submodule.mem_sup_right
  have hu1 : u ∈ F.layer 1 := by rw [F.one_eq_top]; trivial
  simpa only [Nat.add_comm 1 j] using F.lie_mem hu1 hy

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.MajorWeightedDegreeTools
namespace OAI


namespace Erdos3

open _root_.MvPolynomial

variable {σ τ R : Type*} [CommRing R]

theorem weightedSupportLE_lt_succ {w : σ → ℕ} {d : ℕ} {p : MvPolynomial σ R}
    (hp : p ∈ weightedSupportLE w d) : p ∈ weightedSupportLT w (d + 1) :=
  fun _ ha => Nat.lt_succ_iff.mpr (hp ha)

theorem weightedComparison_mul (w : τ → ℕ)
    (F G : MvPolynomial σ R →ₐ[R] MvPolynomial τ R)
    (p q : MvPolynomial σ R) (d e : ℕ)
    (hGp : G p ∈ weightedSupportLE w d) (hFq : F q ∈ weightedSupportLE w e)
    (hdp : F p - G p ∈ weightedSupportLT w d)
    (hdq : F q - G q ∈ weightedSupportLT w e) :
    F (p * q) - G (p * q) ∈ weightedSupportLT w (d + e) := by
  rw [map_mul, map_mul,
    show F p * F q - G p * G q = (F p - G p) * F q + G p * (F q - G q) by ring]
  exact (weightedSupportLT w (d + e)).add_mem (weightedSupportLT_mul_LE hdp hFq)
    (weightedSupportLE_mul_LT hGp hdq)

end Erdos3


end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.TranslationPhaseQuotient
namespace OAI


namespace Erdos3

open _root_.MvPolynomial Module

variable {σ R : Type*} [CommRing R]

theorem exponentSum_le_positive_weight (w : σ → ℕ) (hw : ∀ i, 0 < w i) (a : σ →₀ ℕ) :
    a.sum (fun _ n => n) ≤ Finsupp.weight w a := by
  simp only [Finsupp.weight_apply, Finsupp.sum, nsmul_eq_mul]
  exact Finset.sum_le_sum (fun i _ => Nat.le_mul_of_pos_right (a i) (hw i))

end Erdos3


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

theorem exists_bounded_linear_image_section (e : Basis ι ℚ L) (f : Basis κ ℚ M)
    (φ : L →ₗ[ℚ] M) {H : ℕ} (hH : 1 ≤ H)
    (hentries : ∀ i j, RationalHeightLE (f.repr (φ (e j)) i) H) :
    ∃ σ : M →ₗ[ℚ] L, (φ.comp σ).comp φ = φ ∧
      ∀ i j, RationalHeightLE (e.repr (σ (f j)) i) (rationalKernelHeight (Fintype.card κ) H) := by
  classical
  obtain ⟨S, hS, hSH⟩ := exists_bounded_rational_image_section (LinearMap.toMatrix e f φ) hH
    (by intro i j; rw [LinearMap.toMatrix_apply]; exact hentries i j)
  refine ⟨Matrix.toLin f e S, ?_, ?_⟩
  · apply (LinearMap.toMatrix e f).injective
    rw [LinearMap.toMatrix_comp e f f, LinearMap.toMatrix_comp f e f, LinearMap.toMatrix_toLin]
    exact hS
  · intro i j
    have heq := LinearMap.toMatrix_apply f e (Matrix.toLin f e S) i j
    rw [LinearMap.toMatrix_toLin] at heq
    rw [← heq]
    exact hSH i j

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.FactorwiseBCHCovers
namespace OAI

section

namespace Erdos3

open NilpotentLieBCHGroup

variable {α : Type*} {M : α → Type*} [∀ a, LieRing (M a)] [∀ a, LieAlgebra ℚ (M a)]
  [DecidableEq α] {s : ℕ}

def liePiSingle (a : α) : M a →ₗ⁅ℚ⁆ (∀ a, M a) where
  toLinearMap := LinearMap.single ℚ M a
  map_lie' {x y} := by
    ext i
    change Pi.single a ⁅x, y⁆ i = ⁅Pi.single a x i, Pi.single a y i⁆
    by_cases hi : i = a
    · subst i
      simp only [Pi.single_eq_same]
    · simp only [Pi.single_eq_of_ne hi, lie_zero]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.LogCharacterBudget
namespace OAI

section

namespace Erdos3.NilpotentLieBCHGroup

open CircleFourier

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

noncomputable def logCharacter (η : L →ₗ[ℝ] ℝ) (g : NilpotentLieBCHGroup L s hnil) : ℂ :=
  character (η g.coord : CircleFourier.Circle)

theorem logCharacter_norm (η : L →ₗ[ℝ] ℝ) (g : NilpotentLieBCHGroup L s hnil) :
    ‖logCharacter η g‖ = 1 := norm_character _

theorem logCharacter_mul (η : L →ₗ[ℝ] ℝ) (g h : NilpotentLieBCHGroup L s hnil)
    (hgh : ⁅g.coord, h.coord⁆ = 0) :
    logCharacter η (g * h) = logCharacter η g * logCharacter η h := by
  simp only [logCharacter, coord_mul, lieBCH_eq_add_of_lie_eq_zero hnil hgh,
    map_add, AddCircle.coe_add, character_add]

theorem logCharacter_inv_mul (η : L →ₗ[ℝ] ℝ) (g : NilpotentLieBCHGroup L s hnil) :
    logCharacter η g⁻¹ * logCharacter η g = 1 := by
  simp only [logCharacter, coord_inv, map_neg, AddCircle.coe_neg, ← character_add,
    neg_add_cancel, character_zero]

theorem logCharacter_of_integral (η : L →ₗ[ℝ] ℝ) (g : NilpotentLieBCHGroup L s hnil)
    (hg : ∃ n : ℤ, η g.coord = n) : logCharacter η g = 1 := by
  obtain ⟨n, hn⟩ := hg
  apply (character_eq_one_iff _).mpr
  apply (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr
  exact ⟨n, by simpa only [zsmul_eq_mul, mul_one] using hn.symm⟩

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3.NilpotentLieBCHGroup

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem logCharacter_norm_sub_eq_relative (η : L →ₗ[ℝ] ℝ)
    (x y γ : NilpotentLieBCHGroup L s hnil)
    (hx : ∀ v : L, ⁅x.coord, v⁆ = 0) (hy : ∀ v : L, ⁅y.coord, v⁆ = 0)
    (hγ : logCharacter η γ = 1) :
    ‖logCharacter η x - logCharacter η y‖ =
      ‖logCharacter η (y * γ * x⁻¹) - 1‖ := by
  have hzero : ⁅(y * γ).coord, x.coord⁆ = 0 := by rw [← lie_skew, hx, neg_zero]
  have hright : ⁅(y * γ).coord, x⁻¹.coord⁆ = 0 := by
    simp only [coord_inv, lie_neg, hzero, neg_zero]
  have hprod : logCharacter η (y * γ * x⁻¹) * logCharacter η x = logCharacter η y := by
    rw [logCharacter_mul η (y * γ) x⁻¹ hright,
      logCharacter_mul η y γ (hy γ.coord), hγ, mul_one, mul_assoc, logCharacter_inv_mul, mul_one]
  calc
    _ = ‖logCharacter η y - logCharacter η x‖ := norm_sub_rev _ _
    _ = ‖(logCharacter η (y * γ * x⁻¹) - 1) * logCharacter η x‖ := by
      rw [sub_mul, one_mul, hprod]
    _ = _ := by rw [norm_mul, logCharacter_norm, mul_one]

end Erdos3.NilpotentLieBCHGroup

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.GlobalErrorSplittingBudget
namespace OAI

section

namespace Erdos3

theorem exists_global_error_budget (a c : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ b : ℝ, 0 ≤ b →
      let B := (b + a) ^ a
      let F := (B + c) ^ c
      let Q := 3 * b + B + F + 3
      B ≤ (b + C) ^ C ∧ productNiltestBudget (3 * Q + 4) ≤ (b + C) ^ C := by
  obtain ⟨e, _, hproduct⟩ := exists_productNiltestBudget_bound
  let X : Polynomial ℕ := Polynomial.X
  let B₀ := (X + Polynomial.C a) ^ a
  let F₀ := (B₀ + Polynomial.C c) ^ c
  let Q₀ := 3 * X + B₀ + F₀ + 3
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (B₀ + (3 * Q₀ + 4 + Polynomial.C e) ^ e)
  refine ⟨C, hC, ?_⟩
  intro b hb B F Q
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hpoly : B + (3 * Q + 4 + e) ^ e ≤ (b + C) ^ C := by
    simpa [X, B₀, F₀, Q₀, B, F, Q, Polynomial.eval₂_pow] using hbudget b hb
  have hnon : 0 ≤ (3 * Q + 4 + e) ^ e := by positivity
  exact ⟨by linarith, (hproduct _ (by positivity)).trans (by linarith)⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.LatticeCoordinateLifts
namespace OAI

section

namespace Erdos3

open Module BohrLattice.MinkowskiDiagonalNormalization
open scoped BigOperators Matrix

theorem lattice_basis_coordinates_bound
    {r : ℕ} (Λ : Submodule ℤ (Fin r → ℝ)) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (b : Basis (Fin r) ℤ Λ) (ρ : Fin r → ℝ) (hρ : ∀ j, 0 < ρ j)
    {H : ℝ} (hH : 0 ≤ H) (hb : ∀ i j, |(b i : Fin r → ℝ) j| ≤ H * ρ j)
    (hcov : (∏ j, ρ j) ≤ ZLattice.covolume Λ)
    (x : Fin r → ℝ) (hx : ∀ j, |x j| ≤ ρ j) (i : Fin r) :
    |(b.ofZLatticeBasis ℝ Λ).equivFun x i| ≤
      (r : ℝ) * r.factorial * H ^ (r - 1) := by
  classical
  let B := b.ofZLatticeBasis ℝ Λ
  let M : Matrix (Fin r) (Fin r) ℝ := fun i j => B j i / ρ i
  have hM : M = (Matrix.of (normalizedBasis B ρ hρ))ᵀ := by
    ext i j
    simp [M]
  have hB : |(Matrix.of B).det| = ZLattice.covolume Λ := by
    have he : (B : Fin r → Fin r → ℝ) = fun j => (b j : Fin r → ℝ) :=
      funext (fun j => Basis.ofZLatticeBasis_apply ℝ Λ b j)
    rw [he]
    exact (ZLattice.covolume_eq_det Λ b).symm
  have hprod : 0 < ∏ j, ρ j := Finset.prod_pos (fun j _ => hρ j)
  have hdet : 1 ≤ |M.det| := by
    rw [hM, Matrix.det_transpose, abs_det_normalizedBasis, hB, ← div_eq_mul_inv]
    exact (le_div_iff₀ hprod).mpr (by simpa using hcov)
  have hentry : ∀ j k, |M j k| ≤ H := by
    intro j k
    change |B k j / ρ j| ≤ H
    rw [abs_div, abs_of_pos (hρ j)]
    apply (div_le_iff₀ (hρ j)).mpr
    simpa only [B, Basis.ofZLatticeBasis_apply] using hb k j
  have hinv : ∀ j k, |M⁻¹ j k| ≤ (r.factorial : ℝ) * H ^ (r - 1) := by
    intro j k
    simpa only [Fintype.card_fin, div_one] using
      matrix_inverse_entry_abs_le M hentry (by norm_num : (0 : ℝ) < 1) hdet j k
  have hMx : M.mulVec (B.equivFun x) = fun j => x j / ρ j := by
    exact basis_coordinate_matrix_mulVec B (divideCoordinates ρ hρ).toLinearMap x
  have hback : M⁻¹.mulVec (fun j => x j / ρ j) = B.equivFun x := by
    rw [← hMx, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _
      (isUnit_iff_ne_zero.mpr (abs_pos.mp (lt_of_lt_of_le zero_lt_one hdet))), Matrix.one_mulVec]
  have hsmall (j) : |x j / ρ j| ≤ 1 := by
    rw [abs_div, abs_of_pos (hρ j)]
    exact (div_le_one (hρ j)).mpr (hx j)
  change |B.equivFun x i| ≤ _
  rw [← hback]
  change |∑ j, M⁻¹ i j * (x j / ρ j)| ≤ _
  calc
    _ ≤ ∑ j, |M⁻¹ i j * (x j / ρ j)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin r, (r.factorial : ℝ) * H ^ (r - 1) := by
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul]
      have h := mul_le_mul (hinv i j) (hsmall j) (abs_nonneg _) (by positivity)
      simpa only [mul_one] using h
    _ = _ := by simp [mul_assoc]

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

theorem properCyclicCoordinateBound_nonneg (r : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    0 ≤ properCyclicCoordinateBound r δ := by
  have h := properCyclicKernelBasisBound_nonneg r hδ
  unfold properCyclicCoordinateBound
  positivity

theorem exists_controlled_cyclic_torus_model
    {r N : ℕ} [NeZero N] (η : (Fin r → ℤ) →+ ZMod N) (R : Fin r → ℕ)
    (hinj : Set.InjOn η {x | ∀ i, |x i| ≤ (R i : ℤ)})
    (h₀ : ZMod N) (J : Finset (ZMod N))
    (δ : ℝ) (hδ : 0 < δ) (hdense : δ * N ≤ (J.card : ℝ))
    (hrep : ∀ h ∈ J, ∃ x : Fin r → ℤ, (∀ i, |x i| ≤ (R i : ℤ)) ∧ h = h₀ + η x) :
    ∃ b : Basis (Fin r) ℤ (cyclicIntegerKernel η),
      (∀ i j, |(b i : Fin r → ℝ) j| ≤ properCyclicKernelBasisBound r δ * ((R j : ℝ) + 1)) ∧
      (∀ x : Fin r → ℝ, (∀ j, |x j| ≤ (R j : ℝ) + 1) → ∀ i,
        |cyclicKernelRealCoordinates η b x i| ≤ properCyclicCoordinateBound r δ) ∧
      Set.InjOn (fun x i => cyclicKernelCoordinateCharacter η b i x)
        {x | ∀ i, |x i| ≤ (R i : ℤ)} ∧
      ∃ t : Fin r → ℝ, (∀ i, t i ∈ Set.Ico (0 : ℝ) 1) ∧
        (∀ i, ∃ k : ℤ, (N : ℝ) * t i = (k : ℝ)) ∧
        ∀ (h : ZMod N) (x : Fin r → ℤ), h = h₀ + η x → ∀ i,
          ((cyclicKernelRealCoordinates η b (integerVectorRealMap x) i : ℝ) :
            AddCircle (1 : ℝ)) =
              ((((h.val : ℝ) - h₀.val) * t i : ℝ) : AddCircle (1 : ℝ)) := by
  obtain ⟨b, hb, t, ht, hperiod, hformula⟩ :=
    exists_proper_affine_torus_basis η R hinj h₀ J δ hδ hdense hrep
  refine ⟨b, hb, ?_, cyclicKernelCoordinateCharacters_injOn η b _ hinj,
    t, ht, hperiod, hformula⟩
  intro x hx i
  exact lattice_basis_coordinates_bound (cyclicIntegerKernel η) b
    (fun j => (R j : ℝ) + 1) (by intro j; positivity)
    (properCyclicKernelBasisBound_nonneg r hδ) hb
    (proper_cyclic_kernel_covolume_lower_bound η R hinj) x hx i

end Erdos3

end

section

namespace Erdos3

theorem properCyclicCoordinateBound_le_exp {r : ℕ} {p : ℝ}
    (hp : 0 ≤ p) (hr : (r : ℝ) ≤ p) :
    properCyclicCoordinateBound r (Real.exp (-p)) ≤ Real.exp ((p + 4) ^ 5) := by
  have hB := properCyclicKernelBasisBound_le_exp hp hr
  have hB0 := properCyclicKernelBasisBound_nonneg r (Real.exp_pos (-p))
  have hrp : (r : ℝ) ≤ Real.exp p := hr.trans
    ((le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp p))
  have hfac : (r.factorial : ℝ) ≤ Real.exp (p ^ 2) :=
    (factorial_le_exp_sq r).trans (Real.exp_le_exp.mpr
      (by nlinarith [Nat.cast_nonneg (α := ℝ) r]))
  have hsub : ((r - 1 : ℕ) : ℝ) ≤ p :=
    (Nat.cast_le.mpr (Nat.sub_le r 1)).trans hr
  have hpower : properCyclicKernelBasisBound r (Real.exp (-p)) ^ (r - 1) ≤
      Real.exp (p * (p + 4) ^ 3) := by
    calc
      _ ≤ (Real.exp ((p + 4) ^ 3)) ^ (r - 1) := pow_le_pow_left₀ hB0 hB _
      _ = Real.exp (((r - 1 : ℕ) : ℝ) * (p + 4) ^ 3) := by rw [Real.exp_nat_mul]
      _ ≤ _ := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hsub (by positivity))
  have hmain : properCyclicCoordinateBound r (Real.exp (-p)) ≤
      Real.exp (p + p ^ 2 + p * (p + 4) ^ 3) := by
    unfold properCyclicCoordinateBound
    calc
      _ ≤ Real.exp p * Real.exp (p ^ 2) * Real.exp (p * (p + 4) ^ 3) := by gcongr
      _ = _ := by rw [← Real.exp_add, ← Real.exp_add]
  apply hmain.trans
  apply Real.exp_le_exp.mpr
  have h : 0 ≤ p ^ 5 + 19 * p ^ 4 + 148 * p ^ 3 + 591 * p ^ 2 + 1215 * p + 1024 := by
    positivity
  nlinarith

end Erdos3

end

section

namespace Erdos3

open Module

theorem exists_localized_cyclic_torus_chart
    {r N : ℕ} [NeZero N] (η : (Fin r → ℤ) →+ ZMod N) (R : Fin r → ℕ)
    (hinj : Set.InjOn η {x | ∀ i, |x i| ≤ (R i : ℤ)})
    (h₀ : ZMod N) (J : Finset (ZMod N)) (hJ : J.Nonempty)
    (δ : ℝ) (hδ : 0 < δ) (hdense : δ * N ≤ (J.card : ℝ))
    (x : ZMod N → Fin r → ℤ)
    (hx : ∀ h ∈ J, ∀ i, |x h i| ≤ (R i : ℤ))
    (hrep : ∀ h ∈ J, h = h₀ + η (x h)) (q : ℕ) (hq : 2 ≤ q) :
    ∃ b : Basis (Fin r) ℤ (cyclicIntegerKernel η),
      (∀ i j, |(b i : Fin r → ℝ) j| ≤ properCyclicKernelBasisBound r δ * ((R j : ℝ) + 1)) ∧
      ∃ t : Fin r → ℝ, (∀ i, t i ∈ Set.Ico (0 : ℝ) 1) ∧
        (∀ i, ∃ k : ℤ, (N : ℝ) * t i = (k : ℝ)) ∧
        ∃ K ⊆ J, K.Nonempty ∧
          J.card ≤ realBoxCellCount (properCyclicCoordinateBound r δ) q ^ r * K.card ∧
          ∃ c : Fin r → ℝ,
            (∀ i, |c i| ≤ properCyclicCoordinateBound r δ + (1 / 2 : ℝ) / q) ∧
            ∀ h ∈ K,
              cyclicKernelRealCoordinates η b (integerVectorRealMap (x h)) =
                c + affineCyclicTorusLocalLift t c h₀ h ∧
              (∀ i, |affineCyclicTorusLocalLift t c h₀ h i| ≤ (1 / 2 : ℝ) / q) ∧
              integerVectorRealMap (x h) = (cyclicKernelRealCoordinates η b).symm
                (c + affineCyclicTorusLocalLift t c h₀ h) := by
  classical
  obtain ⟨b, hb, hcoordinates, _, t, ht, hperiod, hphase⟩ :=
    exists_controlled_cyclic_torus_model η R hinj h₀ J δ hδ hdense
      (fun h hh => ⟨x h, hx h hh, hrep h hh⟩)
  let y (h : ZMod N) := cyclicKernelRealCoordinates η b (integerVectorRealMap (x h))
  have hy : ∀ h ∈ J, ∀ i, |y h i| ≤ properCyclicCoordinateBound r δ := by
    intro h hh i
    apply hcoordinates _ _ i
    intro j
    have hj : |(x h j : ℝ)| ≤ (R j : ℝ) := by exact_mod_cast hx h hh j
    change |(x h j : ℝ)| ≤ (R j : ℝ) + 1
    linarith
  obtain ⟨K, hKJ, hK, hcard, c, hc, hclose⟩ := exists_dense_real_box_cell J hJ y hy q (by omega)
  have hquarter : (1 / 2 : ℝ) / q ≤ 1 / 4 := by
    have hqR : (2 : ℝ) ≤ q := by exact_mod_cast hq
    apply (div_le_iff₀ (by linarith : (0 : ℝ) < q)).mpr
    linarith
  refine ⟨b, hb, t, ht, hperiod, K, hKJ, hK, ?_, c, hc, ?_⟩
  · simpa only [Fintype.card_fin] using hcard
  · intro h hh
    have hlocal (i) : affineCyclicTorusLocalLift t c h₀ h i = y h i - c i := by
      have he : ((y h i - c i : ℝ) : AddCircle (1 : ℝ)) =
          (((((h.val : ℝ) - h₀.val) * t i - c i) : ℝ) : AddCircle (1 : ℝ)) := by
        rw [AddCircle.coe_sub, AddCircle.coe_sub]
        exact congrArg (fun z : AddCircle (1 : ℝ) => z - (c i : AddCircle (1 : ℝ)))
          (hphase h (x h) (hrep h (hKJ hh)) i)
      change centeredCircleLift _ = _
      rw [← he]
      exact centeredCircleLift_coe ((hclose h hh i).trans hquarter)
    have he : y h = c + affineCyclicTorusLocalLift t c h₀ h := by
      funext i
      rw [Pi.add_apply, hlocal]
      ring
    refine ⟨he, ?_, ?_⟩
    · intro i
      rw [hlocal]
      exact hclose h hh i
    · exact (LinearEquiv.eq_symm_apply (cyclicKernelRealCoordinates η b)).mpr he

end Erdos3

end

section

namespace Erdos3

theorem local_cyclic_torus_cell_count_le_exp {r : ℕ} {p : ℝ}
    (hp : 0 ≤ p) (hr : (r : ℝ) ≤ p) :
    ((realBoxCellCount (properCyclicCoordinateBound r (Real.exp (-p))) 8 : ℕ) : ℝ) ^ r ≤
      Real.exp ((r : ℝ) * ((p + 4) ^ 5 + 17)) := by
  have hC := properCyclicCoordinateBound_le_exp hp hr
  have hC0 := properCyclicCoordinateBound_nonneg r (Real.exp_pos (-p))
  have hm := realBoxCellCount_le hC0 8
  have hE : 1 ≤ Real.exp ((p + 4) ^ 5) := Real.one_le_exp (by positivity)
  have h17 : (17 : ℝ) ≤ Real.exp 17 := by linarith [Real.add_one_le_exp (17 : ℝ)]
  have hcount : (realBoxCellCount (properCyclicCoordinateBound r (Real.exp (-p))) 8 : ℝ) ≤
      Real.exp ((p + 4) ^ 5 + 17) := by
    calc
      _ ≤ 17 * Real.exp ((p + 4) ^ 5) := by norm_num at hm; linarith
      _ ≤ Real.exp 17 * Real.exp ((p + 4) ^ 5) :=
        mul_le_mul_of_nonneg_right h17 (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  calc
    _ ≤ (Real.exp ((p + 4) ^ 5 + 17)) ^ r := pow_le_pow_left₀ (Nat.cast_nonneg _) hcount r
    _ = _ := (Real.exp_nat_mul _ _).symm

theorem local_cyclic_torus_density {r N : ℕ} {p : ℝ}
    (hp : 0 ≤ p) (hr : (r : ℝ) ≤ p) (J K : Finset (ZMod N))
    (hJ : Real.exp (-p) * N ≤ (J.card : ℝ))
    (hK : J.card ≤ realBoxCellCount (properCyclicCoordinateBound r (Real.exp (-p))) 8 ^ r * K.card) :
    Real.exp (-((p + 4) ^ 7)) * N ≤ (K.card : ℝ) := by
  let L := (r : ℝ) * ((p + 4) ^ 5 + 17)
  have hcount := local_cyclic_torus_cell_count_le_exp hp hr
  have hretain : Real.exp (-(p + L)) * N ≤ (K.card : ℝ) := by
    apply (mul_le_mul_iff_right₀ (Real.exp_pos L)).mp
    calc
      _ = Real.exp (-p) * N := by
        rw [← mul_assoc, ← Real.exp_add]
        congr 2
        ring
      _ ≤ (J.card : ℝ) := hJ
      _ ≤ ((realBoxCellCount (properCyclicCoordinateBound r (Real.exp (-p))) 8 : ℕ) : ℝ) ^ r * K.card := by
        exact_mod_cast hK
      _ ≤ Real.exp L * K.card := mul_le_mul_of_nonneg_right hcount (Nat.cast_nonneg _)
  exact (mul_le_mul_of_nonneg_right
    (Real.exp_le_exp.mpr (neg_le_neg (local_cyclic_torus_total_loss_le hp hr)))
    (Nat.cast_nonneg N)).trans hretain

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RealificationFixedSubmodule
namespace OAI

section

namespace Erdos3

open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L]

theorem realificationLieHom_eq_self_on (φ : L →ₗ⁅ℚ⁆ L) (U : Submodule ℚ L)
    (hφ : ∀ x ∈ U, φ x = x) (x : ℝ ⊗[ℚ] L) (hx : x ∈ U.baseChange ℝ) :
    realificationLieHom φ x = x := by
  obtain ⟨y, rfl⟩ := hx
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul r y =>
    simp only [LinearMap.baseChange_tmul, realificationLieHom_tmul]
    change r ⊗ₜ[ℚ] φ y.val = r ⊗ₜ[ℚ] y.val
    rw [hφ y.val y.property]
  | add y z hy hz => simp only [map_add, hy, hz]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RationalTaggedSpanProjection
namespace OAI

section

namespace Erdos3

open scoped Matrix

theorem matrix_pair_denominator_le_exp_power {ι κ : Type*} [Fintype ι] [Fintype κ]
    (D : Matrix κ ι ℚ) (S : Matrix ι κ ℚ) (l : ℕ) {p : ℝ} (hp : 0 ≤ p)
    (a : ℕ) (ha : 1 ≤ a) (hι : (Fintype.card ι : ℝ) ≤ p)
    (hκ : (Fintype.card κ : ℝ) ≤ p)
    (hD : ∀ i j, ((D i j).den : ℝ) ≤ Real.exp ((p + 2) ^ a))
    (hS : ∀ i j, ((S i j).den : ℝ) ≤ Real.exp ((p + 2) ^ a))
    (hl : (l : ℝ) ≤ Real.exp p) :
    ((matrixDenominator D * matrixDenominator S * l : ℕ) : ℝ) ≤
      Real.exp ((p + 2) ^ (a + 4)) := by
  have hDb := matrixDenominator_le_exp_power D hp a hκ hι hD
  have hSb := matrixDenominator_le_exp_power S hp a hι hκ hS
  have hlb := hl.trans (Real.exp_le_exp.mpr (le_power_budget hp (by omega : 1 ≤ a + 2)))
  rw [Nat.cast_mul, Nat.cast_mul]
  calc
    _ ≤ Real.exp ((p + 2) ^ (a + 2)) * Real.exp ((p + 2) ^ (a + 2)) *
        Real.exp ((p + 2) ^ (a + 2)) :=
      mul_le_mul (mul_le_mul hDb hSb (Nat.cast_nonneg _) (Real.exp_nonneg _)) hlb
        (Nat.cast_nonneg _) (by positivity)
    _ = Real.exp (3 * (p + 2) ^ (a + 2)) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp ((p + 2) ^ (a + 4)) := by
      apply Real.exp_le_exp.mpr
      calc
        _ ≤ (p + 2) ^ 2 * (p + 2) ^ (a + 2) :=
          mul_le_mul_of_nonneg_right (by nlinarith) (by positivity)
        _ = _ := by rw [← pow_add]; congr 1; omega

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PositiveCyclicCorrelation
namespace OAI

section

open scoped BigOperators

namespace Erdos3

theorem exists_correlating_commonCyclicCut {ι : Type*} [Fintype ι] {N : ℕ} [NeZero N]
    (h : ι → ZMod N) (f u : ZMod N → ℂ) {ρ B : ℝ}
    (hρ : 0 < ρ) (hB : 0 < B) (hf : ∀ x, ‖f x‖ ≤ 1) (hu : ∀ x, ‖u x‖ ≤ B)
    (hc : ρ ≤ ‖finiteCorrelation Finset.univ f u‖) :
    ∃ a : commonCyclicCuts h, (cyclicCutCell (commonCyclicCuts h) N a).Nonempty ∧
      ρ / (2 * ((Fintype.card ι : ℝ) + 8)) ≤
        ‖finiteCorrelation (cyclicCutCell (commonCyclicCuts h) N a) f u‖ ∧
      ρ / (2 * ((Fintype.card ι : ℝ) + 8) * B) ≤
        ((cyclicCutCell (commonCyclicCuts h) N a).card : ℝ) / N := by
  have hsum (x : ZMod N) :
      (∑ a : commonCyclicCuts h, u x * finiteIndicator (cyclicCutCell (commonCyclicCuts h) N a) x) = u x := by
    rw [← Finset.mul_sum, sum_commonCyclicCut_indicator, mul_one]
  have hcard : (Fintype.card (commonCyclicCuts h) : ℝ) ≤ (Fintype.card ι : ℝ) + 8 := by
    rw [Fintype.card_coe]
    exact_mod_cast commonCyclicCuts_card_le h
  obtain ⟨a, ha⟩ := exists_correlating_summand Finset.univ_nonempty f u
    (fun a : commonCyclicCuts h => fun x => u x * finiteIndicator (cyclicCutCell (commonCyclicCuts h) N a) x)
    hρ (by positivity : (0 : ℝ) < (Fintype.card ι : ℝ) + 8) hcard (fun x _ => hf x)
    (fun x _ => by rw [hsum, sub_self, norm_zero]; positivity) hc
  have hh := retained_restricted_correlation (cyclicCutCell (commonCyclicCuts h) N a) f u
    (ρ := ρ / (2 * ((Fintype.card ι : ℝ) + 8))) (by positivity) hB
    (fun x _ => hf x) (fun x _ => hu x) ha
  refine ⟨a, hh.1, hh.2.1, ?_⟩
  simpa only [div_div, ZMod.card] using hh.2.2

end Erdos3

end

section

open scoped BigOperators

namespace Erdos3

variable {ι : Type*} [Fintype ι] {N : ℕ} [NeZero N]

theorem exists_correlating_integer_product_interval (h : ι → ZMod N) (u : ι → ℤ → ℂ)
    (f : ZMod N → ℂ) {ρ B : ℝ} (hρ : 0 < ρ) (hB : 0 < B)
    (hf : ∀ x, ‖f x‖ ≤ 1) (hu : ∀ x, ‖translatedCyclicProduct h u x‖ ≤ B)
    (hc : ρ ≤ ‖finiteCorrelation Finset.univ f (translatedCyclicProduct h u)‖) :
    ∃ a : commonCyclicCuts h,
      let len := intervalCutUpper (commonCyclicCuts h) N a - a
      0 < len ∧ a.val + len ≤ N ∧ 2 * ((len : ℤ) - 1) < N ∧
      ρ / (2 * ((Fintype.card ι : ℝ) + 8)) ≤
        ‖finiteCorrelation (Finset.Ico (a.val : ℤ) (a.val + len)) (fun x => f (x : ZMod N))
          (fun x => ∏ i, u i (x + cyclicTranslationOffset (h i) a))‖ ∧
      ρ / (2 * ((Fintype.card ι : ℝ) + 8) * B) ≤ (len : ℝ) / N := by
  obtain ⟨a, ha, hcorr, hvol⟩ := exists_correlating_commonCyclicCut h f
    (translatedCyclicProduct h u) hρ hB hf hu hc
  have huN := intervalCutUpper_le_end (commonCyclicCuts h) N a
  have hlen : intervalCutUpper (commonCyclicCuts h) N a - a.val ≤ N := by omega
  have hcard : (cyclicCutCell (commonCyclicCuts h) N a).card =
      intervalCutUpper (commonCyclicCuts h) N a - a.val := cyclicInterval_card _ hlen
  refine ⟨a, ?_, ?_, (commonCyclicCut_short h a.property).1, ?_, ?_⟩
  · rw [← hcard]
    exact ha.card_pos
  · have haN := commonCyclicCuts_le h a.property
    have hal := le_intervalCutUpper (commonCyclicCuts h) N haN
    omega
  · rwa [translatedCyclicProduct_cut_correlation h u f a.property] at hcorr
  · rwa [hcard] at hvol

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_cyclic_cube_product_interval {d N : ℕ} [NeZero N]
    (f : ZMod N → ℂ) (R : ℤ → ℂ) (k : Fin d → ZMod N)
    {ρ : ℝ} (hρ : 0 < ρ) (hf : ∀ x, ‖f x‖ ≤ 1) (hR : ∀ n, ‖R n‖ ≤ 1)
    (hcorr : ρ ≤ ‖finiteCorrelation Finset.univ f (cubeProduct (fun n : ZMod N => R n.val) (List.ofFn k))‖) :
    ∃ (b : (Fin d → Bool) → Fin (d + 1)) (a len : ℕ),
      0 < len ∧ a + len ≤ N ∧ 2 * ((len : ℤ) - 1) < N ∧
      ρ / (2 * ((2 : ℝ) ^ d + 8)) ≤
        ‖finiteCorrelation (Finset.Ico (a : ℤ) (a + len)) (fun n => f (n : ZMod N))
          (integerCubeProductWithShift R (fun i => ((k i).val : ℤ)) (cubeCarryShift d N b))‖ ∧
      ρ / (2 * ((2 : ℝ) ^ d + 8)) ≤ (len : ℝ) / N := by
  classical
  let shifts (ω : Fin d → Bool) := cubeShift k ω
  let u (ω : Fin d → Bool) (n : ℤ) := conjugationPower (booleanWeight ω) (R n)
  have heval (n : ZMod N) : translatedCyclicProduct shifts u n =
      cubeProduct (fun n : ZMod N => R n.val) (List.ofFn k) n := by
    rw [cubeProduct_eq_boolean_product]
    unfold translatedCyclicProduct
    apply Finset.prod_congr rfl
    intro ω _
    simp only [shifts, u, add_comm]
  have hcap (n : ZMod N) : ‖translatedCyclicProduct shifts u n‖ ≤ 1 := by
    rw [heval]
    exact cubeProduct_norm_le_one _ (fun x => hR x.val) _ n
  have hc : ρ ≤ ‖finiteCorrelation Finset.univ f (translatedCyclicProduct shifts u)‖ := by
    simpa only [finiteCorrelation, heval] using hcorr
  obtain ⟨a, hlen, hend, hshort, hcor, hvol⟩ := exists_correlating_integer_product_interval
    shifts u f hρ (by norm_num : (0 : ℝ) < 1) hf hcap hc
  simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, Nat.cast_pow,
    Nat.cast_ofNat, mul_one] at hcor hvol
  let len := intervalCutUpper (commonCyclicCuts shifts) N a.val - a.val
  have haN : a.val < N := by omega
  obtain ⟨b, hb⟩ := exists_cube_carry_code k haN
  have hprod (n : ℤ) : (∏ ω, u ω (n + cyclicTranslationOffset (shifts ω) a.val)) =
      integerCubeProductWithShift R (fun i => ((k i).val : ℤ)) (cubeCarryShift d N b) n := by
    unfold integerCubeProductWithShift
    apply Finset.prod_congr rfl
    intro ω _
    simp only [u, shifts, hb, add_assoc]
  refine ⟨b, a.val, len, hlen, hend, hshort, ?_, hvol⟩
  simpa only [finiteCorrelation, hprod] using hcor

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.SubmoduleQuotientCoordinates
namespace OAI

section

namespace Erdos3

open Module
open scoped Matrix

variable {ι κ V : Type*} [AddCommGroup V] [Module ℚ V] [Fintype ι] [Fintype κ]
  (b : Basis ι ℚ V) (U : Submodule ℚ V) (D : Matrix κ ι ℚ)
  (hker : LinearMap.ker D.mulVecLin = U.map b.equivFun.toLinearMap)
  (hsurj : Function.Surjective D.mulVec)

theorem submoduleQuotientCoordinateEquiv_symm [DecidableEq κ]
    (S : Matrix ι κ ℚ) (hS : D * S = 1) (y : κ → ℚ) :
    (submoduleQuotientCoordinateEquiv b U D hker hsurj).symm y = U.mkQ (b.equivFun.symm (S *ᵥ y)) := by
  apply (submoduleQuotientCoordinateEquiv b U D hker hsurj).injective
  rw [LinearEquiv.apply_symm_apply, submoduleQuotientCoordinateEquiv_mk,
    LinearEquiv.apply_symm_apply, Matrix.mulVec_mulVec, hS, Matrix.one_mulVec]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.RealCoordinateFunctionals
namespace OAI

section

namespace Erdos3

open Module
open scoped Matrix TensorProduct NNReal

variable {V I J : Type*} [AddCommGroup V] [Module ℚ V]

theorem realifyCoordinateMap_eq_matrix [Fintype I] (b : Basis I ℚ V)
    (ℓ : V →ₗ[ℚ] (J → ℚ)) (x : ℝ ⊗[ℚ] V) :
    realifyCoordinateMap ℓ x =
      (fun j i => (coordinateFunctionalMatrix b ℓ j i : ℝ)) *ᵥ
        (b.baseChange ℝ).equivFun x := by
  classical
  have h : (realifyCoordinateMap ℓ).comp (b.baseChange ℝ).equivFun.symm.toLinearMap =
      Matrix.mulVecLin (fun j i => (coordinateFunctionalMatrix b ℓ j i : ℝ)) := by
    apply (Pi.basisFun ℝ I).ext
    intro i
    change realifyCoordinateMap ℓ ((b.baseChange ℝ).equivFun.symm (Pi.single i 1)) =
      Matrix.of (fun j k => (coordinateFunctionalMatrix b ℓ j k : ℝ)) *ᵥ Pi.single i 1
    rw [Basis.equivFun_symm_single, Matrix.mulVec_single_one, Basis.baseChange_apply]
    funext j
    rw [realifyCoordinateMap_tmul, one_mul]
    rfl
  have hx := DFunLike.congr_fun h ((b.baseChange ℝ).equivFun x)
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply] at hx
  exact hx.trans (Matrix.mulVecLin_apply _ _)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.DerivativeVerticalBasis
namespace OAI

section

namespace Erdos3

theorem exists_vertical_derivative_grid_matrix
    {σ κ : Type*} [Fintype σ] [Fintype κ] [DecidableEq κ] {k : ℕ}
    (T : σ → ℝ) (hT : ∀ i, T i ≠ 0) (scale : κ → ℝ) (hscale : ∀ j, scale j ≠ 0)
    (Y : (σ → ℝ) →ₗ[ℝ] (κ → ℝ)) (A : (κ → ℝ) ≃ₗ[ℝ] (κ → ℝ))
    (l : ℕ) (hl : 0 < l) (v : Fin k → EuclideanSpace ℝ (σ ⊕ κ))
    (hli : LinearIndependent ℝ v)
    (hv : ∀ j, v j ∈ euclideanDerivativeLattice T hT scale hscale Y A l hl)
    (hzero : ∀ j, euclideanDerivativeShiftMap T hT (v j) = 0) :
    ∃ B : Matrix κ (Fin k) ℝ, LinearIndependent ℝ B.col ∧
      (∀ j, B.col j ∈ realDenominatorGrid l) ∧
      ∀ j, v j = euclideanVerticalMap scale hscale A (B.col j) := by
  choose r hr he using fun j =>
    euclideanDerivative_vertical_grid_coordinates T hT scale hscale Y A l hl (v j) (hv j) (hzero j)
  let B : Matrix κ (Fin k) ℝ := fun i j => r j i
  refine ⟨B, ?_, hr, he⟩
  apply LinearIndependent.of_comp (euclideanVerticalMap scale hscale A)
  have hf : euclideanVerticalMap scale hscale A ∘ B.col = v :=
    funext (fun j => (he j).symm)
  rw [hf]
  exact hli

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.EuclideanDerivativeCovolume
namespace OAI

section

namespace Erdos3

open Module

theorem euclideanDerivativeLattice_covolume_le
    {σ κ : Type*} [Fintype σ] [Fintype κ] [DecidableEq κ]
    (T : σ → ℝ) (hT : ∀ i, T i ≠ 0) (scale : κ → ℝ) (hscale : ∀ j, scale j ≠ 0)
    (Y : (σ → ℝ) →ₗ[ℝ] (κ → ℝ)) (A : (κ → ℝ) ≃ₗ[ℝ] (κ → ℝ))
    (l : ℕ) (hl : 0 < l) (R N : ℝ) (hR : 0 ≤ R) (hN : 0 < N)
    (P : Finset ((σ → ℝ) × (κ → ℝ)))
    (hP : ∀ v ∈ P,
      v ∈ derivativeGridPoints T scale Y (LinearMap.toMatrix' A.toLinearMap) l ∧ ‖v‖ ≤ R)
    (hcard : N ≤ (P.card : ℝ)) :
    let ρ := ((Fintype.card σ + Fintype.card κ : ℕ) : ℝ) * R
    let Λ := euclideanDerivativeLattice T hT scale hscale Y A l hl
    ZLattice.covolume (shortVectorLattice Λ ρ) ≤
      (((finrank ℝ (shortVectorSpan Λ ρ) : ℝ) + 2) * ρ) ^
        finrank ℝ (shortVectorSpan Λ ρ) / N := by
  obtain ⟨Q, hQcard, hQ⟩ := exists_bounded_euclideanDerivativeLattice_family
    T hT scale hscale Y A l hl R P hP
  apply shortVectorLattice_covolume_le_of_points _ _ N
    (mul_nonneg (Nat.cast_nonneg _) hR) hN Q hQ
  simpa only [hQcard] using hcard

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.EuclideanDerivativeDensityCovolume
namespace OAI

section

namespace Erdos3

open Module

theorem euclideanDerivative_covolume_density_bound
    {σ κ : Type*} [Fintype σ] [Fintype κ] [DecidableEq κ]
    (T : σ → ℝ) (hT : ∀ i, 0 < T i)
    (scale : κ → ℝ) (hscale : ∀ j, scale j ≠ 0)
    (Y : (σ → ℝ) →ₗ[ℝ] (κ → ℝ)) (A : (κ → ℝ) ≃ₗ[ℝ] (κ → ℝ))
    (l : ℕ) (hl : 0 < l) (R δ : ℝ) (hR : 0 ≤ R) (hδ : 0 < δ)
    (H : Finset (σ → ℤ)) (r : (σ → ℤ) → κ → ℝ)
    (hr : ∀ h ∈ H, r h ∈ realDenominatorGrid l)
    (hnorm : ∀ h ∈ H,
      ‖derivativeGridPoint T scale Y (LinearMap.toMatrix' A.toLinearMap) h (r h)‖ ≤ R)
    (hdense : δ * ∏ i, T i ≤ (H.card : ℝ)) :
    let ρ := ((Fintype.card σ + Fintype.card κ : ℕ) : ℝ) * R
    let Λ := euclideanDerivativeLattice T (fun i => (hT i).ne') scale hscale Y A l hl
    let d := finrank ℝ (shortVectorSpan Λ ρ)
    ZLattice.covolume (shortVectorLattice Λ ρ) ≤
      (((d : ℝ) + 2) * ρ) ^ d / (δ * ∏ i, T i) := by
  obtain ⟨P, hcard, hP⟩ := exists_bounded_derivativeGridPoint_family T
    (fun i => (hT i).ne') scale Y (LinearMap.toMatrix' A.toLinearMap) l H 0 R
    (fun h hh => ⟨r h, hr h hh, by simpa only [sub_zero] using hnorm h hh⟩)
  apply euclideanDerivativeLattice_covolume_le T (fun i => (hT i).ne') scale hscale
    Y A l hl R (δ * ∏ i, T i) hR (mul_pos hδ (Finset.prod_pos (fun i _ => hT i))) P hP
  simpa only [hcard] using hdense

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.LatticeMinorNormBound
namespace OAI

section

namespace Erdos3

open scoped Matrix

theorem lattice_norm_le_selected_coordinates {ι E : Type*} [Fintype ι] {k : ℕ}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (Λ : Submodule ℤ E) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (b : Module.Basis (Fin k) ℤ Λ) (f : E →ₗᵢ[ℝ] EuclideanSpace ℝ ι)
    (p : Fin k → ι)
    (hp : (Matrix.of (fun i j => f (b j).val (p i))).det ≠ 0)
    (C D : ℝ) (hD : 0 < D) (hC : ZLattice.covolume Λ ≤ C)
    (hlower : 1 / D ≤ |(Matrix.of (fun i j => f (b j).val (p i))).det|)
    (x : E) :
    ‖x‖ ≤ (Fintype.card ι : ℝ) * k * (C * D) * ‖fun j => f x (p j)‖ := by
  let bR := b.ofZLatticeBasis ℝ Λ
  let g := (EuclideanSpace.equiv ι ℝ).toLinearMap.comp f.toLinearMap
  let F := Matrix.of (fun i j => g (bR j) i)
  have hF (i j) : F i j = f (b j).val i := by
    simp only [F, Matrix.of_apply, bR, Module.Basis.ofZLatticeBasis_apply]
    rfl
  have hminor : ∀ q : Fin k → ι, |(F.submatrix q id).det| ≤ C := by
    intro q
    exact (lattice_projection_all_minors_bound Λ b f id Function.injective_id F hF q).trans hC
  have hp' : (F.submatrix p id).det ≠ 0 := by
    have he : F.submatrix p id = Matrix.of (fun i j => f (b j).val (p i)) := by
      ext i j
      exact hF (p i) j
    rwa [he]
  have hlower' : 1 / D ≤ |(F.submatrix p id).det| := by
    have he : F.submatrix p id = Matrix.of (fun i j => f (b j).val (p i)) := by
      ext i j
      exact hF (p i) j
    rwa [he]
  have hC0 : 0 ≤ C := (ZLattice.covolume_pos Λ MeasureTheory.volume).le.trans hC
  have hbound := euclidean_matrix_mulVec_norm_le (F * (F.submatrix p id)⁻¹)
    (C * D) (mul_nonneg hC0 hD.le)
    (row_normalization_abs_le F p hp' C D hD hminor hlower') (fun j => f x (p j))
  have hreconstruct :
      (F * (F.submatrix p id)⁻¹) *ᵥ (fun j => f x (p j)) = g x :=
    basis_image_reconstruct_from_minor bR g p hp' x
  have he : (EuclideanSpace.equiv ι ℝ).symm
      ((F * (F.submatrix p id)⁻¹) *ᵥ (fun j => f x (p j))) = f x := by
    rw [hreconstruct]
    exact (EuclideanSpace.equiv ι ℝ).symm_apply_apply (f x)
  rw [he, f.norm_map] at hbound
  exact hbound

theorem lattice_norm_le_projection_of_grid_minor
    {ι κ E : Type*} [Fintype ι] [Fintype κ] {k : ℕ}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (Λ : Submodule ℤ E) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (b : Module.Basis (Fin k) ℤ Λ) (f : E →ₗᵢ[ℝ] EuclideanSpace ℝ ι)
    (e : κ → ι) (l : ℕ) (hl : 0 < l) (B : Matrix κ (Fin k) ℝ)
    (hB : ∀ i j, B i j = f (b j).val (e i))
    (hgrid : ∀ j, B.col j ∈ realDenominatorGrid l)
    (p : Fin k → κ) (hp : (B.submatrix p id).det ≠ 0)
    (C : ℝ) (hC : ZLattice.covolume Λ ≤ C) (x : E) :
    ‖x‖ ≤ (Fintype.card ι : ℝ) * k * (C * (l : ℝ) ^ k) *
      ‖fun i => f x (e i)‖ := by
  let M := B.submatrix p id
  have hm : Matrix.of (fun i j => f (b j).val ((e ∘ p) i)) = M := by
    ext i j
    exact (hB (p i) j).symm
  have hMgrid (j) : (fun i => M i j) ∈ realDenominatorGrid l := by
    obtain ⟨z, hz⟩ := hgrid j
    refine ⟨fun i => z (p i), ?_⟩
    funext i
    exact congrFun hz (p i)
  have hMlower : 1 / (l : ℝ) ^ k ≤ |M.det| := by
    simpa only [Fintype.card_fin] using one_div_pow_le_abs_grid_det M l hl hMgrid hp
  have hp' : (Matrix.of (fun i j => f (b j).val ((e ∘ p) i))).det ≠ 0 := by rwa [hm]
  have hlower : 1 / (l : ℝ) ^ k ≤
      |(Matrix.of (fun i j => f (b j).val ((e ∘ p) i))).det| := by rwa [hm]
  have hn := lattice_norm_le_selected_coordinates Λ b f (e ∘ p) hp' C ((l : ℝ) ^ k)
    (pow_pos (by exact_mod_cast hl) _) hC hlower x
  have hr : ‖fun j => f x ((e ∘ p) j)‖ ≤ ‖fun i => f x (e i)‖ := by
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro j
    exact norm_le_pi_norm (fun i => f x (e i)) (p j)
  have hC0 : 0 ≤ C := (ZLattice.covolume_pos Λ MeasureTheory.volume).le.trans hC
  exact hn.trans (mul_le_mul_of_nonneg_left hr (by positivity))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.ControlledPositivePolynomialDownsets
namespace OAI

section

namespace Erdos3

theorem positivePolynomialInputBudget_le_denominator (t : ℕ) (p : ℝ) :
    positivePolynomialInputBudget t p ≤ positivePolynomialDenominatorBudget t p :=
  le_add_of_nonneg_right (by positivity)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.UnitVerticalMeanRowCorrelation
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem expect_pair_cyclicHalf_le {N : ℕ} [NeZero N] (f : (Fin 2 → ZMod N) → ℝ)
    (hf : ∀ x, 0 ≤ f x) :
    (𝔼 x : Fin 2 → ZMod N, f (fun i => cyclicHalf (x i))) ≤
      4 * (𝔼 x : Fin 2 → ZMod N, f x) := by
  rw [expect_fin_two, expect_fin_two]
  have heq (h n : ZMod N) : (fun i => cyclicHalf (![h, n] i)) = ![cyclicHalf h, cyclicHalf n] := by
    funext i
    fin_cases i <;> rfl
  simp only [heq]
  calc
    _ ≤ 𝔼 h : ZMod N, 2 * (𝔼 n : ZMod N, f ![cyclicHalf h, n]) := by
      apply Finset.expect_le_expect
      intro h _
      exact expect_cyclicHalf_le (fun n => f ![cyclicHalf h, n]) (fun n => hf _)
    _ = 2 * (𝔼 h : ZMod N, 𝔼 n : ZMod N, f ![cyclicHalf h, n]) := by
      rw [← Finset.mul_expect]
    _ ≤ 2 * (2 * (𝔼 h : ZMod N, 𝔼 n : ZMod N, f ![h, n])) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact expect_cyclicHalf_le (fun h => 𝔼 n : ZMod N, f ![h, n])
        (fun h => Finset.expect_nonneg (fun n _ => hf _))
    _ = _ := by ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.NativeRetainedIntegerMultilinearQuadruples
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem exists_fourPoint_integer_interval {N : ℕ} [NeZero N]
    (f₁ f₂ f₃ f₄ : ℤ → ℂ) (a : ZMod N) {ρ B : ℝ}
    (hρ : 0 < ρ) (hB : 0 < B)
    (hbound : ∀ x : ZMod N,
      ‖fourPointProduct (fun x : ZMod N => f₁ x.val) (fun x : ZMod N => f₂ x.val)
        (fun x : ZMod N => f₃ x.val) (fun x : ZMod N => f₄ x.val) a x‖ ≤ B)
    (hcorr : ρ ≤ ‖𝔼 x : ZMod N,
      fourPointProduct (fun x : ZMod N => f₁ x.val) (fun x : ZMod N => f₂ x.val)
        (fun x : ZMod N => f₃ x.val) (fun x : ZMod N => f₄ x.val) a x‖) :
    ∃ (branch : Bool) (c len : ℕ), 0 < len ∧ c + len ≤ N ∧
      2 * ((len : ℤ) - 1) < N ∧
      ρ / 20 ≤ ‖𝔼 n ∈ Finset.Ico (c : ℤ) (c + len),
        fourPointProduct f₁ f₂ f₃ f₄ (cyclicBranchOffset a branch) n‖ ∧
      ρ / (20 * B) ≤ (len : ℝ) / N := by
  let shifts : Fin 2 → ZMod N := ![0, a]
  let u : Fin 2 → ℤ → ℂ := ![(fun n => f₁ n * star (f₃ n)), (fun n => star (f₂ n) * f₄ n)]
  have heval (x : ZMod N) : star (translatedCyclicProduct shifts u x) =
      fourPointProduct (fun x : ZMod N => f₁ x.val) (fun x : ZMod N => f₂ x.val)
        (fun x : ZMod N => f₃ x.val) (fun x : ZMod N => f₄ x.val) a x := by
    simp only [translatedCyclicProduct, shifts, u, Fin.prod_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one, zero_add, star_mul, star_star,
      fourPointProduct, add_comm a x]
    ring
  have hu (x : ZMod N) : ‖translatedCyclicProduct shifts u x‖ ≤ B := by
    rw [← norm_star, heval]
    exact hbound x
  have hc : ρ ≤ ‖finiteCorrelation Finset.univ (fun _ : ZMod N => (1 : ℂ))
      (translatedCyclicProduct shifts u)‖ := by
    simpa only [finiteCorrelation, one_mul, heval] using hcorr
  obtain ⟨c, hlen, hN, hshort, hcor, hvol⟩ := exists_correlating_integer_product_interval
    shifts u (fun _ : ZMod N => (1 : ℂ)) hρ hB (fun _ => by norm_num) hu hc
  norm_num only [Fintype.card_fin, Nat.cast_ofNat] at hcor hvol
  let len := intervalCutUpper (commonCyclicCuts shifts) N c.val - c.val
  have hcN : c.val < N := by omega
  have hoff : cyclicTranslationOffset (shifts 0) c.val = 0 := by
    simp [shifts, cyclicTranslationOffset, Nat.not_le.mpr hcN]
  let branch := decide (N - a.val ≤ c.val)
  have hprod (n : ℤ) : star (∏ i, u i (n + cyclicTranslationOffset (shifts i) c.val)) =
      fourPointProduct f₁ f₂ f₃ f₄ (cyclicBranchOffset a branch) n := by
    rw [Fin.prod_univ_two, hoff]
    simp only [u, shifts, Matrix.cons_val_zero, Matrix.cons_val_one, add_zero,
      cyclicTranslationOffset_eq_branch, star_mul, star_star, fourPointProduct, branch]
    ring
  refine ⟨branch, c.val, len, hlen, hN, hshort, ?_, ?_⟩
  · simpa only [finiteCorrelation, one_mul, hprod] using hcor
  · exact hvol

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.FiniteChoiceLeafCoordinates
namespace OAI

section

namespace Erdos3

variable {σ : Type*} [DecidableEq σ] {n : ℕ}

theorem finiteChoiceLeafInput_get (l : List σ) :
    l.Nodup → ∀ (v : Fin l.length → Fin (n + 1)) (x : (Fin (n + 1) × σ) → ℤ)
      (j : Fin l.length), finiteChoiceLeafInput l v x (l.get j) = x (v j, l.get j) := by
  induction l with
  | nil => intro _ v x j; exact Fin.elim0 j
  | cons i l ih =>
      intro hl v x j
      obtain ⟨hi, hl⟩ := List.nodup_cons.mp hl
      refine Fin.cases ?_ (fun k => ?_) j
      · change finiteChoiceLeafInput l (Fin.tail v) (finiteChoiceReplaceInput i (v 0) x) i =
          x (v 0, i)
        rw [finiteChoiceLeafInput_of_not_mem l (Fin.tail v) (finiteChoiceReplaceInput i (v 0) x) i hi]
        simp [finiteChoiceReplaceInput, finiteChoiceReplaceIndex]
      · change finiteChoiceLeafInput l (Fin.tail v) (finiteChoiceReplaceInput i (v 0) x) (l.get k) =
          x (v k.succ, l.get k)
        rw [ih hl (Fin.tail v) (finiteChoiceReplaceInput i (v 0) x) k]
        have hki : l.get k ≠ i := by
          intro heq
          apply hi
          rw [← heq]
          exact List.get_mem l k
        change x (if (v k.succ, l.get k) = (0, i) then (v 0, i) else (v k.succ, l.get k)) = _
        rw [if_neg (fun h => hki (congrArg Prod.snd h))]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.TailReflectionInduction
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem exists_family_reflected_correlation
    {T G : Type*} [Fintype T] [Nonempty T] [AddCommGroup G] [Fintype G]
    (F : T → G → G → ℂ) (b₁ b₂ b₃ : T → G → ℂ)
    (hb₁ : ∀ t x, ‖b₁ t x‖ ≤ 1) (hb₂ : ∀ t y, ‖b₂ t y‖ ≤ 1)
    (hb₃ : ∀ t z, ‖b₃ t z‖ ≤ 1) :
    ∃ (z : G) (b : T → G → ℂ), (∀ t y, ‖b t y‖ ≤ 1) ∧
      ‖𝔼 t, 𝔼 x, 𝔼 y, F t y x * b₁ t x * b₂ t y * b₃ t (x + y)‖ ^ 2 ≤
        (𝔼 t, 𝔼 y, 𝔼 y', F t y (z - y - y') * star (F t y' (z - y - y')) *
          b t y * star (b t y')).re := by
  let B (z : G) (t : T) (y : G) := b₂ t y * star (b₃ t (z - y))
  let v (y : G) (u : T × G) := F u.1 y u.2 * b₂ u.1 y * b₃ u.1 (u.2 + y)
  have hleft : (𝔼 u : T × G, b₁ u.1 u.2 * (𝔼 y, v y u)) =
      𝔼 t, 𝔼 x, 𝔼 y, F t y x * b₁ t x * b₂ t y * b₃ t (x + y) := by
    simp_rw [expect_prod_split, Finset.mul_expect]
    apply Finset.expect_congr rfl
    intro t _
    apply Finset.expect_congr rfl
    intro x _
    apply Finset.expect_congr rfl
    intro y _
    dsimp only [v]
    ring
  have hchange (t : T) : (𝔼 y, 𝔼 y', 𝔼 x,
      v y (t, x) * star (v y' (t, x))) =
      𝔼 z, 𝔼 y, 𝔼 y', F t y (z - y - y') * star (F t y' (z - y - y')) *
        B z t y * star (B z t y') := by
    calc
      _ = 𝔼 y, 𝔼 y', 𝔼 z, F t y (z - y - y') * star (F t y' (z - y - y')) *
          B z t y * star (B z t y') := by
        apply Finset.expect_congr rfl
        intro y _
        apply Finset.expect_congr rfl
        intro y' _
        apply Fintype.expect_equiv (Equiv.addRight (y + y'))
        intro x
        have h₁ : x + (y + y') - y = x + y' := by abel
        have h₂ : x + (y + y') - y' = x + y := by abel
        simp only [Equiv.coe_addRight, v, B, h₁, h₂, add_sub_cancel_right,
          star_mul, star_star]
        ring
      _ = 𝔼 y, 𝔼 z, 𝔼 y', F t y (z - y - y') * star (F t y' (z - y - y')) *
          B z t y * star (B z t y') := by
        apply Finset.expect_congr rfl
        intro y _
        exact Finset.expect_comm _ _ _
      _ = _ := Finset.expect_comm _ _ _
  have hright : (𝔼 y, 𝔼 y', 𝔼 u : T × G, v y u * star (v y' u)) =
      𝔼 z, 𝔼 t, 𝔼 y, 𝔼 y', F t y (z - y - y') * star (F t y' (z - y - y')) *
        B z t y * star (B z t y') := by
    simp_rw [expect_prod_split]
    calc
      _ = 𝔼 y, 𝔼 t, 𝔼 y', 𝔼 x, v y (t, x) * star (v y' (t, x)) := by
        apply Finset.expect_congr rfl
        intro y _
        exact Finset.expect_comm _ _ _
      _ = 𝔼 t, 𝔼 y, 𝔼 y', 𝔼 x, v y (t, x) * star (v y' (t, x)) :=
        Finset.expect_comm _ _ _
      _ = _ := by simp_rw [hchange]; exact Finset.expect_comm _ _ _
  have hcs := finite_family_cauchy_schwarz_re (fun u : T × G => b₁ u.1 u.2)
    v (fun u => hb₁ u.1 u.2)
  simp only [one_pow, one_mul, hleft, hright] at hcs
  rw [expect_re, Fintype.expect_eq_sum_div_card (fun z : G =>
    (𝔼 t, 𝔼 y, 𝔼 y', F t y (z - y - y') * star (F t y' (z - y - y')) *
      B z t y * star (B z t y')).re)] at hcs
  have hcard : (0 : ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos
  have hsum : (∑ _z : G,
      ‖𝔼 t, 𝔼 x, 𝔼 y, F t y x * b₁ t x * b₂ t y * b₃ t (x + y)‖ ^ 2) ≤
      ∑ z : G, (𝔼 t, 𝔼 y, 𝔼 y', F t y (z - y - y') * star (F t y' (z - y - y')) *
        B z t y * star (B z t y')).re := by
    simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm] using
      (le_div_iff₀ hcard).mp hcs
  obtain ⟨z, _, hz⟩ := Finset.exists_le_of_sum_le Finset.univ_nonempty hsum
  refine ⟨z, B z, ?_, hz⟩
  intro t y
  simp only [B, norm_mul, norm_star]
  exact (mul_le_of_le_one_left (norm_nonneg _) (hb₂ t y)).trans (hb₃ t _)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

namespace TailReflectionData

noncomputable def pair {n : ℕ} {T G : Type*} [AddCommGroup G]
    (D : TailReflectionData (n + 1) T G) : TailReflectionData n (T × (G × G)) G where
  kernel t h m v := D.kernel t.1 h m (Fin.cons t.2.1 v) *
    star (D.kernel t.1 h m (Fin.cons t.2.2 v))
  signal t w := D.signal t.1 (w + t.2.1) * star (D.signal t.1 (w + t.2.2))
  leftWeight t m v := D.leftWeight t.1 m (Fin.cons t.2.1 v) *
    star (D.leftWeight t.1 m (Fin.cons t.2.2 v))
  rightWeight t h v := D.rightWeight t.1 h (Fin.cons t.2.1 v) *
    star (D.rightWeight t.1 h (Fin.cons t.2.2 v))
  tailWeight t i h m v := boxTailTests (fun j => D.tailWeight t.1 j h m) t.2.1 t.2.2 i v
  signal_norm t w := by
    rw [norm_mul, norm_star]
    exact (mul_le_of_le_one_left (norm_nonneg _) (D.signal_norm _ _)).trans (D.signal_norm _ _)
  left_norm t m v := by
    rw [norm_mul, norm_star]
    exact (mul_le_of_le_one_left (norm_nonneg _) (D.left_norm _ _ _)).trans (D.left_norm _ _ _)
  right_norm t h v := by
    rw [norm_mul, norm_star]
    exact (mul_le_of_le_one_left (norm_nonneg _) (D.right_norm _ _ _)).trans (D.right_norm _ _ _)
  tail_norm t i h m v := boxTailTests_norm (fun j => D.tailWeight t.1 j h m)
    (fun j x => D.tail_norm t.1 j h m x) t.2.1 t.2.2 i v
  tail_misses t i h m := boxTailTests_misses (fun j => D.tailWeight t.1 j h m)
    (fun j => D.tail_misses t.1 j h m) t.2.1 t.2.2 i

theorem reflectedKernel_cons {n : ℕ} {T G : Type*} [AddCommGroup G]
    (D : TailReflectionData (n + 1) T G) (t : T) (a b : G)
    (u v : Fin n → G) (h m : G) :
    D.reflectedKernel t (Fin.cons a u) (Fin.cons b v) h m =
      D.pair.reflectedKernel (t, (a, b)) u v h m := by
  simp only [reflectedKernel, iteratedBoxDifference, Fin.cons_zero, Fin.tail_cons, pair]

end TailReflectionData

end Erdos3

end

section

namespace Erdos3.TailReflectionData

open scoped BigOperators Classical

theorem correlation_square_le_pair {n : ℕ} {T G : Type*} [Fintype T] [Nonempty T]
    [AddCommGroup G] [Fintype G] (D : TailReflectionData (n + 1) T G) :
    ‖D.correlation‖ ^ 2 ≤ D.pair.correlation.re := by
  let C (q : T × ((Fin n → G) × (G × G))) : ℂ :=
    D.tailWeight q.1 0 q.2.2.2 q.2.2.1 (Fin.cons 0 q.2.1)
  let V (a : G) (q : T × ((Fin n → G) × (G × G))) : ℂ :=
    D.signal q.1 (q.2.2.1 + q.2.2.2 + ∑ i, (Fin.cons a q.2.1) i) *
      D.kernel q.1 q.2.2.2 q.2.2.1 (Fin.cons a q.2.1) *
      D.leftWeight q.1 q.2.2.1 (Fin.cons a q.2.1) *
      D.rightWeight q.1 q.2.2.2 (Fin.cons a q.2.1) *
      ∏ i : Fin n, D.tailWeight q.1 i.succ q.2.2.2 q.2.2.1 (Fin.cons a q.2.1)
  have hleft : (𝔼 q, C q * (𝔼 a, V a q)) = D.correlation := by
    unfold correlation
    simp_rw [expect_dependent_fin_cons, Finset.mul_expect]
    rw [Finset.expect_comm]
    simp_rw [expect_prod_split]
    rw [Finset.expect_comm]
    apply Finset.expect_congr rfl
    intro t _
    apply Finset.expect_congr rfl
    intro a _
    apply Finset.expect_congr rfl
    intro v _
    apply Finset.expect_congr rfl
    intro m _
    apply Finset.expect_congr rfl
    intro h _
    dsimp only [C, V]
    rw [Fin.prod_univ_succ,
      missesBoxCoordinate_head (D.tail_misses t 0 h m) a 0 v]
    ring
  have hright : (𝔼 a, 𝔼 b, 𝔼 q, V a q * star (V b q)) = D.pair.correlation := by
    unfold correlation
    simp_rw [expect_prod_split]
    calc
      _ = 𝔼 a, 𝔼 t, 𝔼 b, 𝔼 v : Fin n → G, 𝔼 m, 𝔼 h,
          V a (t, (v, (m, h))) * star (V b (t, (v, (m, h)))) := by
        apply Finset.expect_congr rfl
        intro a _
        exact Finset.expect_comm _ _ _
      _ = 𝔼 t, 𝔼 a, 𝔼 b, 𝔼 v : Fin n → G, 𝔼 m, 𝔼 h,
          V a (t, (v, (m, h))) * star (V b (t, (v, (m, h)))) :=
        Finset.expect_comm _ _ _
      _ = _ := by
        apply Finset.expect_congr rfl
        intro t _
        apply Finset.expect_congr rfl
        intro a _
        apply Finset.expect_congr rfl
        intro b _
        apply Finset.expect_congr rfl
        intro v _
        apply Finset.expect_congr rfl
        intro m _
        apply Finset.expect_congr rfl
        intro h _
        dsimp only [V, pair]
        simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, boxTailTests,
          star_mul, star_prod, Finset.prod_mul_distrib]
        have ha : m + h + (a + ∑ i, v i) = (m + h + ∑ i, v i) + a := by abel
        have hb : m + h + (b + ∑ i, v i) = (m + h + ∑ i, v i) + b := by abel
        rw [ha, hb]
        ring
  have hcs := finite_family_cauchy_schwarz_re C V
    (fun q => D.tail_norm q.1 0 q.2.2.2 q.2.2.1 (Fin.cons 0 q.2.1))
  simpa only [hleft, hright, one_pow, one_mul] using hcs

end Erdos3.TailReflectionData

end

section

namespace Erdos3.TailReflectionData

open scoped BigOperators Classical

universe u

theorem exists_reflected_correlation (n : ℕ) :
    ∀ {T G : Type u} [Fintype T] [Nonempty T] [AddCommGroup G] [Fintype G]
      (D : TailReflectionData n T G),
      ∃ (z : G) (b : T → (Fin n → G) → (Fin n → G) → G → ℂ),
        (∀ t u v h, ‖b t u v h‖ ≤ 1) ∧
        ‖D.correlation‖ ^ (2 ^ (n + 1)) ≤
          (𝔼 t, 𝔼 u : Fin n → G, 𝔼 v : Fin n → G, 𝔼 h, 𝔼 h',
            D.reflectedKernel t u v h (z - h - h') *
              star (D.reflectedKernel t u v h' (z - h - h')) *
                b t u v h * star (b t u v h')).re := by
  induction n with
  | zero =>
      intro T G _ _ _ _ D
      let e : Fin 0 → G := fun i => Fin.elim0 i
      obtain ⟨z, b, hb, hcorr⟩ := exists_family_reflected_correlation
        (fun t h m => D.kernel t h m e)
        (fun t m => D.leftWeight t m e) (fun t h => D.rightWeight t h e) D.signal
        (fun t m => D.left_norm t m e) (fun t h => D.right_norm t h e) D.signal_norm
      refine ⟨z, (fun t _ _ h => b t h), (fun t _ _ h => hb t h), ?_⟩
      simpa only [correlation, reflectedKernel, iteratedBoxDifference, expect_empty_tuple,
        Fin.sum_univ_zero, Fin.prod_univ_zero, add_zero, mul_one, one_mul, Nat.zero_add, pow_one,
        e, mul_comm, mul_left_comm, mul_assoc] using hcorr
  | succ n ih =>
      intro T G _ _ _ _ D
      obtain ⟨z, b, hb, hcorr⟩ := ih D.pair
      let B (t : T) (u v : Fin (n + 1) → G) (h : G) :=
        b (t, (u 0, v 0)) (Fin.tail u) (Fin.tail v) h
      refine ⟨z, B, (fun t u v h => hb _ _ _ _), ?_⟩
      have hmean :
          (𝔼 t, 𝔼 u : Fin (n + 1) → G, 𝔼 v : Fin (n + 1) → G, 𝔼 h, 𝔼 h',
            D.reflectedKernel t u v h (z - h - h') *
              star (D.reflectedKernel t u v h' (z - h - h')) *
                B t u v h * star (B t u v h')) =
          𝔼 t : T × (G × G), 𝔼 u : Fin n → G, 𝔼 v : Fin n → G, 𝔼 h, 𝔼 h',
            D.pair.reflectedKernel t u v h (z - h - h') *
              star (D.pair.reflectedKernel t u v h' (z - h - h')) *
                b t u v h * star (b t u v h') := by
        simp_rw [expect_prod_split]
        apply Finset.expect_congr rfl
        intro t _
        rw [expect_two_dependent_fin_cons]
        simp only [B, Fin.cons_zero, Fin.tail_cons, reflectedKernel_cons]
      rw [hmean]
      calc
        _ = (‖D.correlation‖ ^ 2) ^ (2 ^ (n + 1)) := by
          rw [← pow_mul, pow_succ]
          congr 1
          omega
        _ ≤ ‖D.pair.correlation‖ ^ (2 ^ (n + 1)) :=
          pow_le_pow_left₀ (sq_nonneg _)
            (D.correlation_square_le_pair.trans (Complex.re_le_norm _)) _
        _ ≤ _ := hcorr

end Erdos3.TailReflectionData

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AnchoredReflectedFamily
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

universe u

theorem exists_mixed_reflected_correlation (n : ℕ)
    {T G : Type u} [Fintype T] [Nonempty T] [AddCommGroup G] [Fintype G]
    (K : T → G → G → (Fin n → G) → ℂ) (f : T → G → ℂ)
    (A : T → Fin (n + 2) → (Fin (n + 2) → G) → ℂ)
    (hf : ∀ t x, ‖f t x‖ ≤ 1) (hA : ∀ t i x, ‖A t i x‖ ≤ 1)
    (hmiss : ∀ t i, MissesBoxCoordinate (A t i) i) :
    ∃ (z : G) (b : T → (Fin n → G) → (Fin n → G) → G → ℂ),
      (∀ t u v h, ‖b t u v h‖ ≤ 1) ∧
      ‖𝔼 t, 𝔼 x : Fin n → G, 𝔼 m, 𝔼 h,
        f t (m + h + ∑ i, x i) * K t h m x * ∏ i, A t i (Fin.cons h (Fin.cons m x))‖ ^
          (2 ^ (n + 1)) ≤
        (𝔼 t, 𝔼 u : Fin n → G, 𝔼 v : Fin n → G, 𝔼 h, 𝔼 h',
          mixedTailDifference (K t) u v h (z - h - h') *
            star (mixedTailDifference (K t) u v h' (z - h - h')) *
              b t u v h * star (b t u v h')).re := by
  let D : TailReflectionData n T G := {
    kernel := K
    signal := f
    leftWeight := fun t m x => A t 0 (Fin.cons 0 (Fin.cons m x))
    rightWeight := fun t h x => A t 1 (Fin.cons h (Fin.cons 0 x))
    tailWeight := fun t i h m x => A t i.succ.succ (Fin.cons h (Fin.cons m x))
    signal_norm := hf
    left_norm := fun t m x => hA t 0 _
    right_norm := fun t h x => hA t 1 _
    tail_norm := fun t i h m x => hA t i.succ.succ _
    tail_misses := by
      intro t i h m x a
      simp only [Fin.cons_update]
      exact hmiss t i.succ.succ _ a }
  have hleft (t : T) (h m : G) (x : Fin n → G) :
      A t 0 (Fin.cons h (Fin.cons m x)) = A t 0 (Fin.cons 0 (Fin.cons m x)) :=
    missesBoxCoordinate_head (hmiss t 0) h 0 (Fin.cons m x)
  have hright (t : T) (h m : G) (x : Fin n → G) :
      A t 1 (Fin.cons h (Fin.cons m x)) = A t 1 (Fin.cons h (Fin.cons 0 x)) := by
    have H := hmiss t 1 (Fin.cons h (Fin.cons m x)) 0
    change A t 1 (Function.update (Fin.cons h (Fin.cons m x))
      (0 : Fin (n + 1)).succ 0) = _ at H
    rw [← Fin.cons_update, Fin.update_cons_zero] at H
    exact H.symm
  have hcorr_eq : D.correlation =
      𝔼 t, 𝔼 x : Fin n → G, 𝔼 m, 𝔼 h,
        f t (m + h + ∑ i, x i) * K t h m x * ∏ i, A t i (Fin.cons h (Fin.cons m x)) := by
    unfold TailReflectionData.correlation
    apply Finset.expect_congr rfl
    intro t _
    apply Finset.expect_congr rfl
    intro x _
    apply Finset.expect_congr rfl
    intro m _
    apply Finset.expect_congr rfl
    intro h _
    dsimp only [D]
    rw [Fin.prod_univ_succ, Fin.prod_univ_succ]
    change _ = _ * (A t 0 (Fin.cons h (Fin.cons m x)) *
      (A t 1 (Fin.cons h (Fin.cons m x)) *
        ∏ i : Fin n, A t i.succ.succ (Fin.cons h (Fin.cons m x))))
    simp only [hleft, hright]
    ring
  obtain ⟨z, b, hb, hcorr⟩ := TailReflectionData.exists_reflected_correlation n D
  refine ⟨z, b, hb, ?_⟩
  simpa only [hcorr_eq, TailReflectionData.reflectedKernel, mixedTailDifference, D] using hcorr

theorem exists_mixed_reflected_exp_correlation (n : ℕ)
    {T G : Type u} [Fintype T] [Nonempty T] [AddCommGroup G] [Fintype G]
    (K : T → G → G → (Fin n → G) → ℂ) (f : T → G → ℂ)
    (A : T → Fin (n + 2) → (Fin (n + 2) → G) → ℂ)
    (hf : ∀ t x, ‖f t x‖ ≤ 1) (hA : ∀ t i x, ‖A t i x‖ ≤ 1)
    (hmiss : ∀ t i, MissesBoxCoordinate (A t i) i) {p : ℝ}
    (hcorr : Real.exp (-p) ≤
      ‖𝔼 t, 𝔼 x : Fin n → G, 𝔼 m, 𝔼 h,
        f t (m + h + ∑ i, x i) * K t h m x * ∏ i, A t i (Fin.cons h (Fin.cons m x))‖) :
    ∃ (z : G) (b : T → (Fin n → G) → (Fin n → G) → G → ℂ),
      (∀ t u v h, ‖b t u v h‖ ≤ 1) ∧
      Real.exp (-((2 ^ (n + 1) : ℕ) : ℝ) * p) ≤
        (𝔼 t, 𝔼 u : Fin n → G, 𝔼 v : Fin n → G, 𝔼 h, 𝔼 h',
          mixedTailDifference (K t) u v h (z - h - h') *
            star (mixedTailDifference (K t) u v h' (z - h - h')) *
              b t u v h * star (b t u v h')).re := by
  obtain ⟨z, b, hb, hbound⟩ := exists_mixed_reflected_correlation n K f A hf hA hmiss
  refine ⟨z, b, hb, ?_⟩
  have hpower : Real.exp (-((2 ^ (n + 1) : ℕ) : ℝ) * p) =
      Real.exp (-p) ^ (2 ^ (n + 1)) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [hpower]
  exact (pow_le_pow_left₀ (Real.exp_nonneg _) hcorr _).trans hbound

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem mixedTailDifference_eq_anchor {n : ℕ} {G : Type*}
    (K : G → G → (Fin n → G) → ℂ) (u a : Fin n → G) (h m : G) :
    mixedTailDifference K u a h m =
      K h m u * boxCornerAnchor (fun x => K h m x) a u := by
  rw [mixedTailDifference, iteratedBoxDifference_eq_cornerProduct, boxCornerProduct_eq_mul_anchor]

theorem mixedTailDifference_norm {n : ℕ} {G : Type*}
    (K : G → G → (Fin n → G) → ℂ) (hK : ∀ h m x, ‖K h m x‖ ≤ 1)
    (u a : Fin n → G) (h m : G) : ‖mixedTailDifference K u a h m‖ ≤ 1 := by
  rw [mixedTailDifference_eq_anchor, norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) (hK h m u)).trans
    (boxCornerAnchor_norm_le_one (fun x => K h m x) (hK h m) a u)

theorem mixedTailDifference_map {n : ℕ} {X G : Type*} (φ : X → G)
    (K : G → G → (Fin n → G) → ℂ) (u v : Fin n → X) (h m : X) :
    mixedTailDifference (fun h m x => K (φ h) (φ m) (fun i => φ (x i))) u v h m =
      mixedTailDifference K (fun i => φ (u i)) (fun i => φ (v i)) (φ h) (φ m) := by
  simp only [mixedTailDifference, iteratedBoxDifference_eq_cornerProduct]
  exact boxCornerProduct_map φ (fun x => K (φ h) (φ m) x) u v

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem exists_mixed_anchor_weights {n : ℕ} {G : Type*} [AddCommGroup G]
    (K : G → G → (Fin n → G) → ℂ) (hK : ∀ h m x, ‖K h m x‖ ≤ 1)
    (c : G) (a : Fin n → G) (b d : (Fin n → G) → G → ℂ)
    (hb : ∀ u h, ‖b u h‖ ≤ 1) (hd : ∀ u h, ‖d u h‖ ≤ 1) :
    ∃ A : Fin (n + 2) → (Fin (n + 2) → G) → ℂ,
      (∀ i x, ‖A i x‖ ≤ 1) ∧
      (∀ i x y, (∀ k, k ≠ i → x k = y k) → A i x = A i y) ∧
      ∀ x, (mixedTailDifference K (fun i => x i.succ.succ) a (x 0) (c - x 0 - x 1) *
          star (mixedTailDifference K (fun i => x i.succ.succ) a (x 1) (c - x 0 - x 1)) *
          b (fun i => x i.succ.succ) (x 0) * d (fun i => x i.succ.succ) (x 1)) =
        (K (x 0) (c - x 0 - x 1) (fun i => x i.succ.succ) *
          star (K (x 1) (c - x 0 - x 1) (fun i => x i.succ.succ))) * ∏ i, A i x := by
  let S : Finset (Fin n → Bool) := Finset.univ.erase (fun _ => false)
  let F (ω : S) (x : Fin (n + 2) → G) := mixedReflectedCorner K c a ω.val x
  have hF : ∀ ω x, ‖F ω x‖ ≤ 1 := fun ω x => mixedReflectedCorner_norm K hK c a ω.val x
  have hFind : ∀ ω, ∃ i, ∀ x y, (∀ k, k ≠ i → x k = y k) → F ω x = F ω y := by
    intro ω
    have hne : ω.val ≠ fun _ => false := (Finset.mem_erase.mp ω.property).1
    obtain ⟨i, hi⟩ := exists_true_of_ne_false hne
    exact ⟨i.succ.succ, mixedReflectedCorner_independent K c a ω.val i hi⟩
  obtain ⟨D, hD, hDind, hDprod⟩ := exists_missing_coordinate_product_factors F hF hFind
  have hFprod (x : Fin (n + 2) → G) : (∏ ω : S, F ω x) =
      boxCornerAnchor (fun v => K (x 0) (c - x 0 - x 1) v) a (fun i => x i.succ.succ) *
        star (boxCornerAnchor (fun v => K (x 1) (c - x 0 - x 1) v) a (fun i => x i.succ.succ)) := by
    simp only [F, mixedReflectedCorner, Finset.prod_mul_distrib, ← star_prod]
    have he (h : G) :
        (∏ ω : S, conjugationPower (booleanWeight ω.val)
          (K h (c - x 0 - x 1) (boxCorner (fun i => x i.succ.succ) a ω.val))) =
          boxCornerAnchor (fun v => K h (c - x 0 - x 1) v) a (fun i => x i.succ.succ) :=
      Finset.prod_coe_sort S (fun ω => conjugationPower (booleanWeight ω)
        (K h (c - x 0 - x 1) (boxCorner (fun i => x i.succ.succ) a ω)))
    rw [he, he]
  let H (i : Fin (n + 2)) (x : Fin (n + 2) → G) : ℂ :=
    Fin.cases (d (fun j => x j.succ.succ) (x 1))
      (Fin.cases (b (fun j => x j.succ.succ) (x 0)) (fun _ => 1)) i
  have hH : ∀ i x, ‖H i x‖ ≤ 1 := by
    intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · intro x
      exact hd _ _
    · refine Fin.cases ?_ (fun j => ?_) i
      · intro x
        exact hb _ _
      · intro x
        change ‖(1 : ℂ)‖ ≤ 1
        norm_num
  have hHind : ∀ i x y, (∀ k, k ≠ i → x k = y k) → H i x = H i y := by
    intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · intro x y hxy
      have ht : (fun j : Fin n => x j.succ.succ) = fun j => y j.succ.succ :=
        funext (fun j => hxy j.succ.succ (Fin.succ_ne_zero j.succ))
      change d (fun j => x j.succ.succ) (x 1) = d (fun j => y j.succ.succ) (y 1)
      rw [ht, hxy 1 (Fin.succ_ne_zero (0 : Fin (n + 1)))]
    · refine Fin.cases ?_ (fun j => ?_) i
      · intro x y hxy
        have hne (j : Fin n) : j.succ.succ ≠ (1 : Fin (n + 2)) := by
          intro heq
          exact Fin.succ_ne_zero j (Fin.succ_injective (n + 1) heq)
        have ht : (fun j : Fin n => x j.succ.succ) = fun j => y j.succ.succ :=
          funext (fun j => hxy j.succ.succ (hne j))
        change b (fun j => x j.succ.succ) (x 0) = b (fun j => y j.succ.succ) (y 0)
        rw [ht, hxy 0 (Fin.succ_ne_zero (0 : Fin (n + 1))).symm]
      · intro x y _
        rfl
  have hHprod (x : Fin (n + 2) → G) : (∏ i, H i x) =
      d (fun j => x j.succ.succ) (x 1) * b (fun j => x j.succ.succ) (x 0) := by
    rw [Fin.prod_univ_succ, Fin.prod_univ_succ]
    change _ * (_ * (∏ _j : Fin n, (1 : ℂ))) = _
    simp only [Finset.prod_const_one, mul_one]
    rfl
  refine ⟨(fun i x => H i x * D i x), ?_, ?_, ?_⟩
  · intro i x
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hH i x)).trans (hD i x)
  · intro i x y hxy
    change H i x * D i x = H i y * D i y
    rw [hHind i x y hxy, hDind i x y hxy]
  · intro x
    rw [Finset.prod_mul_distrib, hHprod, hDprod, hFprod]
    simp only [mixedTailDifference_eq_anchor, star_mul]
    ring

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem exists_anchored_reflected_family {n : ℕ} {T X G : Type*}
    [Fintype T] [Nonempty T] [Fintype X] [Nonempty X] [AddCommGroup G]
    (φ : X → G) (ψ : G → X) (hψ : ∀ x, ψ (φ x) = x)
    (K : T → G → G → (Fin n → G) → ℂ) (hK : ∀ t h m u, ‖K t h m u‖ ≤ 1)
    (c : G) (B C : T → (Fin n → X) → (Fin n → X) → G → ℂ)
    (hB : ∀ t u v h, ‖B t u v h‖ ≤ 1) (hC : ∀ t u v h, ‖C t u v h‖ ≤ 1)
    {δ : ℝ} (hcorr : δ ≤ ‖𝔼 t, 𝔼 u : Fin n → X, 𝔼 v : Fin n → X, 𝔼 x, 𝔼 y,
      mixedTailDifference (K t) (fun i => φ (u i)) (fun i => φ (v i)) (φ x) (c - φ x - φ y) *
        star (mixedTailDifference (K t) (fun i => φ (u i)) (fun i => φ (v i)) (φ y)
          (c - φ x - φ y)) * B t u v (φ x) * C t u v (φ y)‖) :
    ∃ A : T → Fin (n + 2) → (Fin (n + 2) → G) → ℂ,
      (∀ t i x, ‖A t i x‖ ≤ 1) ∧
      (∀ t i x y, (∀ k, k ≠ i → x k = y k) → A t i x = A t i y) ∧
      δ ≤ ‖𝔼 t, 𝔼 u : Fin n → X, 𝔼 x, 𝔼 y,
        (K t (φ x) (c - φ x - φ y) (fun i => φ (u i)) *
          star (K t (φ y) (c - φ x - φ y) (fun i => φ (u i)))) *
            ∏ i, A t i (Fin.cons (φ x) (Fin.cons (φ y) (fun j => φ (u j))))‖ := by
  let F (t : T) (u v : Fin n → X) := 𝔼 x : X, 𝔼 y : X,
    mixedTailDifference (K t) (fun i => φ (u i)) (fun i => φ (v i)) (φ x) (c - φ x - φ y) *
      star (mixedTailDifference (K t) (fun i => φ (u i)) (fun i => φ (v i)) (φ y)
        (c - φ x - φ y)) * B t u v (φ x) * C t u v (φ y)
  have hcomm : (𝔼 t, 𝔼 u, 𝔼 v, F t u v) = 𝔼 v, 𝔼 t, 𝔼 u, F t u v := by
    calc
      _ = 𝔼 t, 𝔼 v, 𝔼 u, F t u v :=
        Finset.expect_congr rfl (fun _ _ => Finset.expect_comm _ _ _)
      _ = _ := Finset.expect_comm _ _ _
  change δ ≤ ‖𝔼 t, 𝔼 u, 𝔼 v, F t u v‖ at hcorr
  rw [hcomm] at hcorr
  have hmean : δ ≤ 𝔼 v, ‖𝔼 t, 𝔼 u, F t u v‖ :=
    hcorr.trans (RCLike.norm_expect_le (K := ℂ))
  obtain ⟨a, _, ha⟩ := Finset.exists_le_of_le_expect Finset.univ_nonempty hmean
  have hweights (t : T) := exists_mixed_anchor_weights (K t) (hK t) c (fun i => φ (a i))
    (fun u h => B t (fun i => ψ (u i)) a h) (fun u h => C t (fun i => ψ (u i)) a h)
    (fun u h => hB t _ a h) (fun u h => hC t _ a h)
  choose A hA hAind hpoint using hweights
  refine ⟨A, hA, hAind, ?_⟩
  have heq : (𝔼 t, 𝔼 u, F t u a) =
      𝔼 t, 𝔼 u : Fin n → X, 𝔼 x, 𝔼 y,
        (K t (φ x) (c - φ x - φ y) (fun i => φ (u i)) *
          star (K t (φ y) (c - φ x - φ y) (fun i => φ (u i)))) *
            ∏ i, A t i (Fin.cons (φ x) (Fin.cons (φ y) (fun j => φ (u j)))) := by
    apply Finset.expect_congr rfl
    intro t _
    apply Finset.expect_congr rfl
    intro u _
    apply Finset.expect_congr rfl
    intro x _
    apply Finset.expect_congr rfl
    intro y _
    have H := hpoint t (Fin.cons (φ x) (Fin.cons (φ y) (fun j => φ (u j))))
    have h1 : (Fin.cons (φ x) (Fin.cons (φ y) (fun j => φ (u j))) :
        Fin (n + 2) → G) 1 = φ y := rfl
    simpa only [Fin.cons_zero, Fin.cons_succ, h1, hψ] using H
  rw [← heq]
  exact ha

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MixedRootLosses
namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def mixedPostExchangePermutation {s : ℕ} (v : Fin (s + 3) → Fin 2) :
    Equiv.Perm (Fin (s + 2)) :=
  Tuple.sort (fun j => mixedSwapSample (mixedPreExchangeSample v) j.succ)

theorem mixedCanonicalSample_of_first_zero {s : ℕ} (v : MixedNonconstantCorner s)
    (h0 : v.val 0 = 0) :
    mixedCanonicalSample v.val = mixedPermuteSample (mixedPostExchangePermutation v.val)
      (mixedSwapSample (mixedPreExchangeSample v.val)) := by
  calc
    mixedCanonicalSample v.val = binarySorted (mixedCornerSample v.val) :=
      mixedCanonicalSample_eq_sorted _
    _ = binarySorted (mixedPreExchangeSample v.val) := by
      rw [mixedPreExchangeSample, mixedPermuteSample_eq_comp, binarySorted_comp]
    _ = binarySorted (mixedSwapSample (mixedPreExchangeSample v.val)) := by
      exact (binarySorted_comp (mixedPreExchangeSample v.val) (mixedExchangePermutation s)).symm
    _ = _ := by
      rw [mixedPermuteSample_eq_comp]
      exact binarySorted_tail _ (mixedPreExchangeSample_one v h0)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CubeSignalAlgebra
namespace OAI

section

namespace Erdos3

open scoped BigOperators

def mixedCubeInputHom {d : ℕ} (ω : Fin d → Bool) : Fin 2 → ((Fin (d + 2) → ℤ) →+ ℤ) :=
  fun i =>
    { toFun := fun x => mixedCubeInput ω x i
      map_zero' := by
        fin_cases i <;> simp [mixedCubeInput, correlationInput, cubeShift]
        rfl
      map_add' := by
        intro x y
        fin_cases i
        · rfl
        · change x 1 + y 1 + cubeShift (fun j => x j.succ.succ + y j.succ.succ) ω =
            (x 1 + cubeShift (fun j => x j.succ.succ) ω) +
              (y 1 + cubeShift (fun j => y j.succ.succ) ω)
          have hs : cubeShift (fun j => x j.succ.succ + y j.succ.succ) ω =
              cubeShift (fun j => x j.succ.succ) ω + cubeShift (fun j => y j.succ.succ) ω := by
            simp only [cubeShift, ← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro j _
            split_ifs <;> simp
          rw [hs]
          ring }

theorem mixedCubeObservable_unit {J : Type*} [Fintype J] {d : ℕ}
    (f : J → (Fin 2 → ℤ) → ℂ) (hf : ∀ y, ∑ j, ‖f j y‖ ^ 2 = 1)
    (x : Fin (d + 2) → ℤ) : ∑ a, ‖mixedCubeObservable f a x‖ ^ 2 = 1 := by
  simp only [mixedCubeObservable, norm_prod, ← Finset.prod_pow, conjugationPower_norm]
  rw [← Fintype.prod_sum (fun ω (j : J) => ‖f j (mixedCubeInput ω x)‖ ^ 2)]
  simp only [hf, Finset.prod_const_one]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.PreparedFiniteStageNativeBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators

noncomputable def preparedFiniteForwardWorkPolynomial (A : ℕ)
    (stageCountConstant : ℕ → ℕ) (n : ℕ) : Polynomial ℕ :=
  (preparedFiniteForwardParameterPolynomial A stageCountConstant n + Polynomial.C A) ^ A

noncomputable def preparedFiniteForwardCapPolynomial (A : ℕ)
    (stageCountConstant : ℕ → ℕ) (n : ℕ) : Polynomial ℕ :=
  (4 * preparedFiniteForwardParameterPolynomial A stageCountConstant n +
    4 * preparedFiniteForwardWorkPolynomial A stageCountConstant n + 16 + Polynomial.C A) ^ A

noncomputable def preparedFiniteForwardCountPolynomial (A : ℕ)
    (stageCountConstant : ℕ → ℕ) (n : ℕ) : Polynomial ℕ :=
  preparedFiniteForwardParameterPolynomial A stageCountConstant n +
    preparedFiniteForwardCapPolynomial A stageCountConstant n

noncomputable def preparedFiniteForwardBranchPolynomial (A : ℕ)
    (stageCountConstant : ℕ → ℕ) (n : ℕ) : Polynomial ℕ :=
  Polynomial.X * preparedFiniteForwardCapPolynomial A stageCountConstant n +
    (preparedFiniteForwardCountPolynomial A stageCountConstant n + 8) ^ 8 +
    (preparedFiniteForwardCountPolynomial A stageCountConstant n +
      Polynomial.C (stageCountConstant n)) ^ stageCountConstant n

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.FiniteNormalizedChartCorrection
namespace OAI

section

namespace Erdos3
open _root_.MvPolynomial
open scoped BigOperators Classical

variable {U B : Type*}

theorem normalizedChart_spatial_support (P : MvPolynomial U ℝ) :
    rename (Sum.inl : U → U ⊕ B) P ∈ weightedSupportLE normalizedChartTagWeight 0 := by
  rw [rename_eq_aeval]
  apply weightedSupportLE_aeval (fun _ : U => 0) normalizedChartTagWeight
  · intro i
    exact weightedSupportLE_X _ (Sum.inl i)
  · intro α _
    simp [Finsupp.weight_apply]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.FullChartHomogeneousCorrection
namespace OAI

section

namespace Erdos3

theorem weightedHomogeneousComponent_totalDegree_le_of_positive
    {σ R : Type*} [CommRing R] (w : σ → ℕ) (hw : ∀ i, 0 < w i)
    (k : ℕ) (p : MvPolynomial σ R) :
    (MvPolynomial.weightedHomogeneousComponent w k p).totalDegree ≤ k := by
  classical
  unfold MvPolynomial.totalDegree
  apply Finset.sup_le
  intro α hα
  rw [MvPolynomial.support_weightedHomogeneousComponent] at hα
  exact (exponentSum_le_positive_weight w hw α).trans (Finset.mem_filter.mp hα).2.le

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.AllocatedExternalCandidateSpatialNativeBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

variable {m : ℕ} {X : Type*} (J : Fin m → Type*)

noncomputable def fullTaggedSpatialIntegerChart (x : X) : MvPolynomial (X ⊕ (Σ j, J j)) ℤ :=
  MvPolynomial.X (Sum.inl x)

end Erdos3.VectorPolynomial

end

end OAI
end


