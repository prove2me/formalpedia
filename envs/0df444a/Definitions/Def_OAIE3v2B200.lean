-- Prove2me | Definitions.Def_OAIE3v2B200
-- name    : OAIE3v2B200
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-18T04:10:38.21614+00:00
-- url     : https://prove2.me/theorems/7fe6ff4a-16a8-43b9-835c-23cefc7ad154
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 204 of 311
-- statement:
--   Definitions bundle 204 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B180`, `OAIE3v2B181`, `OAIE3v2B182`, `OAIE3v2B183` of this split.
--
--   Modules: `Estimates/ExtractedInitialState.lean`, `Estimates/FastHorizontalFactorization.lean`, `Estimates/GradedUnitEvaluation.lean`, `Estimates/NativeWeightPairRemoval.lean`, `Linear/FullFastRelativeSpanning.lean`, `Linear/RealGradedFastCoefficientKernel.lean`, `Polynomial/GradedPolynomialSymbolInverse.lean`, `Polynomial/NativeFormalPolynomialSystems.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B180
import Definitions.Def_OAIE3v2B181
import Definitions.Def_OAIE3v2B182
import Definitions.Def_OAIE3v2B183

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FastHorizontalFactorization
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1))
  (U : LieSubalgebra ℚ (F.squareFiltration.quotientTop.PolynomialSymbol (fun _ : σ => 1)))

variable {ι : Type*} (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))

include e ω hF

theorem realFastCoefficientDirectionMap_triple
    (a b c : F.realFastDiagonalSubgroup (fun _ : σ => 1) U) (v : σ → ℝ) :
    F.realFastCoefficientDirectionMap U (a * b * c).val v =
      F.realFastCoefficientDirectionMap U a.val v +
        F.realFastCoefficientAction (fun _ => 1) (fun _ => Nat.zero_lt_one) U a
          (F.realFastCoefficientDirectionMap U b.val v) +
        F.realFastCoefficientAction (fun _ => 1) (fun _ => Nat.zero_lt_one) U a
          (F.realFastCoefficientAction (fun _ => 1) (fun _ => Nat.zero_lt_one) U b
            (F.realFastCoefficientDirectionMap U c.val v)) := by
  exact linear_cocycle_triple (F.realFastCoefficientAction (fun _ : σ => 1)
    (fun _ => Nat.zero_lt_one) U)
    (fun g => F.realFastCoefficientDirectionMap U g.val v)
    (fun g h => F.realFastCoefficientDirectionMap_mul U e ω hF g h v) a b c

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module
open scoped TensorProduct

variable {σ ι L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1))
  (U : LieSubalgebra ℚ (F.squareFiltration.quotientTop.PolynomialSymbol (fun _ : σ => 1)))
  (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))

include e ω hF

theorem realFastCoefficient_remove_derivative
    (a b c : F.realFastDiagonalSubgroup (fun _ : σ => 1) U) (v : σ → ℝ)
    (small rational z : F.RealFastCoefficientModule (fun _ : σ => 1) (fun _ => Nat.zero_lt_one) U)
    (hsystem : F.realFastCoefficientDirectionMap U (a * b * c).val v = small +
      F.realFastCoefficientAction (fun _ => 1) (fun _ => Nat.zero_lt_one) U (a * b * c) rational + z) :
    F.realFastCoefficientDirectionMap U b.val v =
      (F.realFastCoefficientAction (fun _ => 1) (fun _ => Nat.zero_lt_one) U a).symm
        (small - F.realFastCoefficientDirectionMap U a.val v) +
      F.realFastCoefficientAction (fun _ => 1) (fun _ => Nat.zero_lt_one) U b
        (F.realFastCoefficientAction (fun _ => 1) (fun _ => Nat.zero_lt_one) U c rational -
          F.realFastCoefficientDirectionMap U c.val v) +
      (F.realFastCoefficientAction (fun _ => 1) (fun _ => Nat.zero_lt_one) U a).symm z := by
  let ρ := F.realFastCoefficientAction (fun _ : σ => 1) (fun _ => Nat.zero_lt_one) U
  apply linear_derivative_remove (ρ a) (ρ c) (ρ (a * b * c)) (ρ b)
    (linear_action_triple ρ a b c)
    _ _ _ _ small rational z
    (F.realFastCoefficientDirectionMap_triple U e ω hF a b c v) hsystem

omit [Fintype σ] in
theorem realFastCoefficient_remove_horizontal_lifts {K : Type*}
    [AddCommGroup K] [Module ℝ K]
    (a c : F.realFastDiagonalSubgroup (fun _ : σ => 1) U)
    (S R : K →ₗ[ℝ] F.RealFastCoefficientModule (fun _ : σ => 1) (fun _ => Nat.zero_lt_one) U)
    (I : K →ₗ[ℝ] (ℝ ⊗[ℚ] (L ⧸ F.layer 2)))
    (hS : (F.realFastCoefficientHorizontal (fun _ => 1) (fun _ => Nat.zero_lt_one)
      (F.reducedSquareFastRelativeSubmodule (fun _ => 1) U)).comp S = I)
    (hR : (F.realFastCoefficientHorizontal (fun _ => 1) (fun _ => Nat.zero_lt_one)
      (F.reducedSquareFastRelativeSubmodule (fun _ => 1) U)).comp R = I) :
    let P := F.realFastCoefficientHorizontal (fun _ => 1) (fun _ => Nat.zero_lt_one)
      (F.reducedSquareFastRelativeSubmodule (fun _ => 1) U)
    P.comp ((F.realFastCoefficientAction (fun _ => 1) (fun _ => Nat.zero_lt_one) U a).symm.toLinearMap.comp S) = I ∧
      P.comp ((F.realFastCoefficientAction (fun _ => 1) (fun _ => Nat.zero_lt_one) U c).toLinearMap.comp R) = I := by
  exact horizontal_lift_remove _ _ _
    (F.realFastCoefficientAction_horizontal (fun _ => 1) (fun _ => Nat.zero_lt_one) U e ω hF a)
    (F.realFastCoefficientAction_horizontal (fun _ => 1) (fun _ => Nat.zero_lt_one) U e ω hF c) S R I hS hR

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.GradedUnitEvaluation
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1))

variable (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))

local notation "ωW" => (fun i : ReducedSquareBasisIndex s ω => squareBasisWeight ω (Subtype.val i))
local notation "bW" => F.squareFiltration.quotientTop.associatedGradedBasis
  (F.reducedSquareBasis e ω hF) ωW (F.reducedSquareBasis_layers e ω hF)

theorem fullFastPointwise_subgroup_eq [Fintype σ] [Fintype ι] (w : σ → ℕ) (hw : ∀ i, 0 < w i)
    (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded)
    (hW : BasisGradedSubmodule bW ωW W.toSubmodule) :
    F.realPointwisePolynomialSubgroup e ω hF w (F.fullFastGradedDiagonal W) =
      F.realFastDiagonalSubgroup w (F.fastPointwiseSquare e ω hF w W) := by
  ext g
  rw [F.mem_realPointwisePolynomialSubgroup, F.mem_realFastDiagonalSubgroup,
    F.adaptedReducedRealSymbolHom_coord]
  change F.realExtendedSymbolMap w g.coord ∈
      (F.symbolPointwiseSubalgebra e ω hF w (F.fullFastGradedDiagonal W)).toSubmodule.baseChange ℝ ↔
    (F.quotientTopSymbolMap w).toLinearMap.baseChange ℝ (F.realExtendedSymbolMap w g.coord) ∈
      (F.reducedSquareFastDiagonalSubalgebra w (F.fastPointwiseSquare e ω hF w W)).toSubmodule.baseChange ℝ
  have he : (F.symbolPointwiseSubalgebra e ω hF w (F.fullFastGradedDiagonal W)).toSubmodule =
      (F.reducedSquareFastDiagonalSubalgebra w (F.fastPointwiseSquare e ω hF w W)).toSubmodule.comap
        (F.quotientTopSymbolMap w).toLinearMap :=
    congrArg LieSubalgebra.toSubmodule (F.fullFastPointwise_eq_comap e ω hF w hw W hW)
  rw [he, realification_comap]
  rfl

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i})) (w : σ → ℕ)

local notation "ωW" => (fun a : ReducedSquareBasisIndex s ω => squareBasisWeight ω (Subtype.val a))

theorem firstCoefficientGradedPolynomial_reducedSquare_symbol
    (p : F.squareFiltration.quotientTop.adaptedLieSubalgebra w) (α : σ →₀ ℕ) :
    coefficients (F.firstCoefficientGradedPolynomial e ω hF w (F.reducedSquareCoefficientMap w
      (F.squareFiltration.quotientTop.polynomialSymbolMap w p))) α =
      F.reducedSquareGradedDifference e ω hF
        (coefficients (F.squareFiltration.quotientTop.gradedSymbolPolynomial
          (F.reducedSquareBasis e ω hF) ωW (F.reducedSquareBasis_layers e ω hF) w
            (F.squareFiltration.quotientTop.polynomialSymbolMap w p)) α) := by
  have hl : coefficients (F.firstCoefficientGradedPolynomial e ω hF w (F.reducedSquareCoefficientMap w
      (F.squareFiltration.quotientTop.polynomialSymbolMap w p))) α =
      F.gradedPieceProjection e ω hF (Finsupp.weight w α + 1)
        (F.reducedSquareDifference (coefficients p.val α)) := by
    rw [F.reducedSquareCoefficientMap_symbol, F.firstCoefficientGradedPolynomial_normalized,
      F.shiftedGradedPolynomial_coefficient, F.reducedSquareDifferenceRelative_coefficient]
  have hr : coefficients (F.squareFiltration.quotientTop.gradedSymbolPolynomial
      (F.reducedSquareBasis e ω hF) ωW (F.reducedSquareBasis_layers e ω hF) w
        (F.squareFiltration.quotientTop.polynomialSymbolMap w p)) α =
      F.squareFiltration.quotientTop.gradedPieceProjection
        (F.reducedSquareBasis e ω hF) ωW (F.reducedSquareBasis_layers e ω hF)
        (Finsupp.weight w α) (coefficients p.val α) := by
    rw [← F.squareFiltration.quotientTop.shiftedGradedPolynomial_zero
      (F.reducedSquareBasis e ω hF) ωW (F.reducedSquareBasis_layers e ω hF) w p,
      F.squareFiltration.quotientTop.shiftedGradedPolynomial_coefficient]
    simp only [Nat.add_zero]
  calc
    _ = F.gradedPieceProjection e ω hF (Finsupp.weight w α + 1)
        (F.reducedSquareDifference (coefficients p.val α)) := hl
    _ = F.reducedSquareGradedDifference e ω hF
        (F.squareFiltration.quotientTop.gradedPieceProjection
          (F.reducedSquareBasis e ω hF) ωW (F.reducedSquareBasis_layers e ω hF)
          (Finsupp.weight w α) (coefficients p.val α)) :=
      (F.reducedSquareGradedDifference_projection e ω hF (Finsupp.weight w α) (coefficients p.val α)).symm
    _ = _ := congrArg (F.reducedSquareGradedDifference e ω hF) hr.symm

theorem firstCoefficientGradedPolynomial_reducedSquare_coefficient
    (x : F.squareFiltration.quotientTop.PolynomialSymbol w) (α : σ →₀ ℕ) :
    coefficients (F.firstCoefficientGradedPolynomial e ω hF w (F.reducedSquareCoefficientMap w x)) α =
      F.reducedSquareGradedDifference e ω hF
        (coefficients (F.squareFiltration.quotientTop.gradedSymbolPolynomial
          (F.reducedSquareBasis e ω hF) ωW (F.reducedSquareBasis_layers e ω hF) w x) α) := by
  obtain ⟨p, rfl⟩ := F.squareFiltration.quotientTop.polynomialSymbolMap_surjective w x
  exact F.firstCoefficientGradedPolynomial_reducedSquare_symbol e ω hF w p α

theorem firstCoefficientGradedPolynomial_reducedSquare
    (x : F.squareFiltration.quotientTop.PolynomialSymbol w) :
    F.firstCoefficientGradedPolynomial e ω hF w (F.reducedSquareCoefficientMap w x) =
      VectorPolynomial.map (F.reducedSquareGradedDifference e ω hF)
        (F.squareFiltration.quotientTop.gradedSymbolPolynomial
          (F.reducedSquareBasis e ω hF) ωW (F.reducedSquareBasis_layers e ω hF) w x) := by
  apply coefficients.injective
  ext α
  rw [coefficients_map, F.firstCoefficientGradedPolynomial_reducedSquare_coefficient]

theorem firstCoefficientGradedPolynomial_reducedSquare_homogeneous (α : σ →₀ ℕ)
    (x : F.squareFiltration.quotientTop.AssociatedGraded) :
    F.firstCoefficientGradedPolynomial e ω hF w
        (F.reducedSquareCoefficientMap w
          (F.squareFiltration.quotientTop.homogeneousSymbolLift
            (F.reducedSquareBasis e ω hF) ωW (F.reducedSquareBasis_layers e ω hF) w α x)) =
      monomial α (basisGradeProjection (F.associatedGradedBasis e ω hF) ω (Finsupp.weight w α + 1)
        (F.reducedSquareGradedDifference e ω hF x)) := by
  rw [F.firstCoefficientGradedPolynomial_reducedSquare,
    F.squareFiltration.quotientTop.gradedSymbolPolynomial_homogeneousSymbolLift,
    VectorPolynomial.map_monomial, F.reducedSquareGradedDifference_gradeProjection]

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.GradedPolynomialSymbolInverse
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [Fintype σ] [Fintype ι] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
  (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded)

theorem realAdaptedGradedPolynomialLie_fullFast_mem
    (hW : BasisGradedSubmodule
      (F.squareFiltration.quotientTop.associatedGradedBasis (F.reducedSquareBasis e ω hF)
        (fun i => squareBasisWeight ω i.val) (F.reducedSquareBasis_layers e ω hF))
      (fun i => squareBasisWeight ω i.val) W.toSubmodule)
    (g : F.realFastDiagonalSubgroup (fun _ : σ => 1) (F.fastPointwiseSquare e ω hF (fun _ => 1) W))
    (α : σ →₀ ℕ) :
    coefficients (F.realAdaptedGradedPolynomialLie e ω hF (fun _ : σ => 1) g.val.coord) α ∈
      realificationLieSubalgebra (F.fullFastGradedDiagonal W) := by
  have hg : g.val ∈ F.realPointwisePolynomialSubgroup e ω hF (fun _ : σ => 1)
      (F.fullFastGradedDiagonal W) := by
    rw [F.fullFastPointwise_subgroup_eq e ω hF (fun _ => 1) (fun _ => Nat.zero_lt_one) W hW]
    exact g.property
  have hs := (F.mem_realPointwisePolynomialSubgroup e ω hF (fun _ => 1)
    (F.fullFastGradedDiagonal W) g.val).mp hg
  have hc := (F.mem_real_symbolPointwiseSubalgebra_iff_coefficients e ω hF (fun _ => 1)
    (F.fullFastGradedDiagonal W) _).mp hs α
  rw [F.realAdaptedGradedPolynomialLie_symbol]
  exact hc

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RealGradedFastCoefficientKernel
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))

local notation "ωW" => (fun a : ReducedSquareBasisIndex s ω => squareBasisWeight ω (Subtype.val a))
local notation "bW" => F.squareFiltration.quotientTop.associatedGradedBasis
  (F.reducedSquareBasis e ω hF) ωW (F.reducedSquareBasis_layers e ω hF)

variable (w : σ → ℕ) (hw : ∀ i, 0 < w i)
  (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded)

theorem firstCoefficientFastSubmodule_graded_coefficients (x : F.FirstCoefficientModule w)
    (hx : x ∈ F.firstCoefficientFastSubmodule w hw (F.fastPointwiseSquare e ω hF w W).toSubmodule) :
    ∀ α, coefficients (F.firstCoefficientGradedPolynomial e ω hF w x) α ∈
      F.fullFastGradedRelative e ω hF W := by
  rw [F.firstCoefficientFastSubmodule_eq_image] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  intro α
  rw [F.firstCoefficientGradedPolynomial_reducedSquare_coefficient]
  refine ⟨coefficients (F.squareFiltration.quotientTop.gradedSymbolPolynomial
    (F.reducedSquareBasis e ω hF) ωW (F.reducedSquareBasis_layers e ω hF) w y) α, ?_, rfl⟩
  constructor
  · exact (F.squareFiltration.quotientTop.mem_symbolPointwiseSubalgebra_iff
      (F.reducedSquareBasis e ω hF) ωW (F.reducedSquareBasis_layers e ω hF) w W y).mp hy.1 α
  · change F.reducedSquareGradedSndMap _ = 0
    rw [F.reducedSquareGradedSnd_coefficient]
    have hz : F.reducedSquareSndSymbolMap w y = 0 := hy.2
    simp only [hz, map_zero, Finsupp.zero_apply]

theorem firstCoefficientFastSubmodule_iff_graded
    (hW : BasisGradedSubmodule bW ωW W.toSubmodule) (x : F.FirstCoefficientModule w) :
    x ∈ F.firstCoefficientFastSubmodule w hw (F.fastPointwiseSquare e ω hF w W).toSubmodule ↔
      ∀ α, coefficients (F.firstCoefficientGradedPolynomial e ω hF w x) α ∈
        F.fullFastGradedRelative e ω hF W := by
  classical
  constructor
  · exact F.firstCoefficientFastSubmodule_graded_coefficients e ω hF w hw W x
  · intro hx
    have hex (α : σ →₀ ℕ) : ∃ y, y ∈ F.fastGradedRelativeKernel W ∧
        F.reducedSquareGradedDifference e ω hF y =
          coefficients (F.firstCoefficientGradedPolynomial e ω hF w x) α := hx α
    choose y hy hey using hex
    let q (α : σ →₀ ℕ) : F.FirstCoefficientModule w :=
      F.reducedSquareCoefficientMap w (F.squareFiltration.quotientTop.homogeneousSymbolLift
        (F.reducedSquareBasis e ω hF) ωW (F.reducedSquareBasis_layers e ω hF) w α (y α))
    have hq (α : σ →₀ ℕ) : q α ∈
        F.firstCoefficientFastSubmodule w hw (F.fastPointwiseSquare e ω hF w W).toSubmodule := by
      rw [F.firstCoefficientFastSubmodule_eq_image]
      refine ⟨F.squareFiltration.quotientTop.homogeneousSymbolLift
        (F.reducedSquareBasis e ω hF) ωW (F.reducedSquareBasis_layers e ω hF) w α (y α), ?_, rfl⟩
      constructor
      · exact F.squareFiltration.quotientTop.homogeneousSymbolLift_mem_pointwise
          (F.reducedSquareBasis e ω hF) ωW (F.reducedSquareBasis_layers e ω hF) w W hW α (y α) (hy α).1
      · change F.reducedSquareSndSymbolMap w _ = 0
        rw [F.reducedSquareSnd_homogeneousSymbolLift]
        have hz : F.reducedSquareGradedSndMap (y α) = 0 := (hy α).2
        rw [hz, map_zero]
    have hp (α : σ →₀ ℕ) : F.firstCoefficientGradedPolynomial e ω hF w (q α) =
        monomial α (coefficients (F.firstCoefficientGradedPolynomial e ω hF w x) α) := by
      dsimp only [q]
      rw [F.firstCoefficientGradedPolynomial_reducedSquare_homogeneous, hey,
        F.firstCoefficientGradedPolynomial_homogeneous]
    have he : (∑ α ∈ (coefficients (F.firstCoefficientGradedPolynomial e ω hF w x)).support, q α) = x := by
      apply F.firstCoefficientGradedPolynomial_injective e ω hF w
      rw [map_sum]
      simp_rw [hp]
      exact sum_monomial_coefficients _
    rw [← he]
    exact Submodule.sum_mem _ (fun α _ => hq α)

theorem firstCoefficientFastSubmodule_eq_gradedKernel
    (hW : BasisGradedSubmodule bW ωW W.toSubmodule) :
    F.firstCoefficientFastSubmodule w hw (F.fastPointwiseSquare e ω hF w W).toSubmodule =
      LinearMap.ker (F.firstCoefficientGradedQuotientMap e ω hF w W) := by
  ext x
  rw [F.firstCoefficientFastSubmodule_iff_graded e ω hF w hw W hW]
  change (∀ α, coefficients (F.firstCoefficientGradedPolynomial e ω hF w x) α ∈
    F.fullFastGradedRelative e ω hF W) ↔ F.firstCoefficientGradedQuotientMap e ω hF w W x = 0
  constructor
  · intro hx
    apply coefficients.injective
    ext α
    change coefficients (VectorPolynomial.map (F.fullFastGradedRelative e ω hF W).mkQ
      (F.firstCoefficientGradedPolynomial e ω hF w x)) α = _
    rw [coefficients_map, map_zero, Finsupp.zero_apply]
    exact (Submodule.Quotient.mk_eq_zero _).mpr (hx α)
  · intro hx α
    have hc := congrArg (fun p => coefficients p α) hx
    change coefficients (VectorPolynomial.map (F.fullFastGradedRelative e ω hF W).mkQ
      (F.firstCoefficientGradedPolynomial e ω hF w x)) α = _ at hc
    rw [coefficients_map, map_zero, Finsupp.zero_apply] at hc
    exact (Submodule.Quotient.mk_eq_zero _).mp hc

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
  (w : σ → ℕ) (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded)

local notation "ωW" => (fun a : ReducedSquareBasisIndex s ω => squareBasisWeight ω (Subtype.val a))
local notation "bW" => F.squareFiltration.quotientTop.associatedGradedBasis
  (F.reducedSquareBasis e ω hF) ωW (F.reducedSquareBasis_layers e ω hF)

theorem realFirstCoefficientFastSubmodule_iff_graded (hw : ∀ i, 0 < w i)
    (hW : BasisGradedSubmodule bW ωW W.toSubmodule) (x : F.RealFirstCoefficientModule w) :
    x ∈ F.realFirstCoefficientFastSubmodule w hw (F.fastPointwiseSquare e ω hF w W).toSubmodule ↔
      ∀ α, coefficients (F.realFirstCoefficientGradedPolynomial e ω hF w x) α ∈
        (F.fullFastGradedRelative e ω hF W).baseChange ℝ := by
  obtain ⟨y, rfl⟩ := (F.firstCoefficientRealEquiv w).surjective x
  have hmem : F.firstCoefficientRealEquiv w y ∈
      F.realFirstCoefficientFastSubmodule w hw (F.fastPointwiseSquare e ω hF w W).toSubmodule ↔
      y ∈ (F.firstCoefficientFastSubmodule w hw (F.fastPointwiseSquare e ω hF w W).toSubmodule).baseChange ℝ := by
    constructor
    · rintro ⟨z, hz, he⟩
      have hzy : z = y := (F.firstCoefficientRealEquiv w).injective he
      rwa [hzy] at hz
    · intro hy
      exact ⟨y, hy, rfl⟩
  rw [hmem, F.firstCoefficientFastSubmodule_eq_gradedKernel e ω hF w hw W hW, realification_ker]
  change (F.firstCoefficientGradedQuotientMap e ω hF w W).baseChange ℝ y = 0 ↔ _
  rw [realificationLinearEquiv_eq_zero_iff]
  have hker : (F.fullFastGradedRelative e ω hF W).baseChange ℝ =
      LinearMap.ker ((F.fullFastGradedRelative e ω hF W).mkQ.baseChange ℝ) := by
    simpa only [Submodule.ker_mkQ] using
      realification_ker (F.fullFastGradedRelative e ω hF W).mkQ
  constructor
  · intro hy α
    rw [hker]
    change (F.fullFastGradedRelative e ω hF W).mkQ.baseChange ℝ _ = 0
    exact (F.realFirstCoefficientGradedQuotient_coefficient e ω hF w W y α).symm.trans (hy α)
  · intro hy α
    have h := hy α
    rw [hker] at h
    exact (F.realFirstCoefficientGradedQuotient_coefficient e ω hF w W y α).trans h

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.NativeFormalPolynomialSystems
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

variable {σ ι κ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
  (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded)

local notation "ωW" => (fun a : ReducedSquareBasisIndex s ω => squareBasisWeight ω (Subtype.val a))
local notation "bW" => F.squareFiltration.quotientTop.associatedGradedBasis
  (F.reducedSquareBasis e ω hF) ωW (F.reducedSquareBasis_layers e ω hF)
local notation "Wf" => F.fastPointwiseSquare e ω hF (fun _ : σ => 1) W
local notation "Kf" => F.realFirstCoefficientFastSubmodule (fun _ : σ => 1) (fun _ => Nat.zero_lt_one)
  (F.reducedSquareFastRelativeSubmodule (fun _ : σ => 1) Wf)
local notation "φ" => F.realFirstCoefficientGradedPolynomial e ω hF (fun _ : σ => 1)
local notation "Vg" => Submodule.restrictScalars ℚ (Submodule.baseChange ℝ (F.fullFastGradedRelative e ω hF W))

theorem realFastCoefficient_relative_iff_polynomial
    (hW : BasisGradedSubmodule bW ωW W.toSubmodule)
    (x : F.RealFirstCoefficientModule (fun _ : σ => 1)) :
    x ∈ Kf ↔ φ x ∈ coefficientSubmodule Vg := by
  rw [F.realFirstCoefficientFastSubmodule_relative]
  exact F.realFirstCoefficientFastSubmodule_iff_graded e ω hF (fun _ : σ => 1) W
    (fun _ => Nat.zero_lt_one) hW x

theorem nativeFast_liftSystem_to_formal
    (hW : BasisGradedSubmodule bW ωW W.toSubmodule)
    (g : F.realFastDiagonalSubgroup (fun _ : σ => 1) Wf)
    (S R : κ → F.RealFirstCoefficientModule (fun _ : σ => 1))
    (h : ∀ z, (Kf).mkQ (S z) =
      F.realFastCoefficientAction (fun _ : σ => 1) (fun _ => Nat.zero_lt_one) Wf g ((Kf).mkQ (R z))) :
    PolynomialLiftSystemMod Vg (F.realAdaptedGradedPolynomialHom e ω hF (fun _ : σ => 1) g.val)
      (fun z => φ (S z)) (fun z => φ (R z)) := by
  intro z
  have hz := h z
  rw [F.realFastCoefficientAction_mk] at hz
  have hq : (Kf).mkQ (S z - F.realFirstCoefficientAdjoint (fun _ : σ => 1) g.val (R z)) = 0 := by
    rw [map_sub, hz, sub_self]
  have hm : S z - F.realFirstCoefficientAdjoint (fun _ : σ => 1) g.val (R z) ∈ Kf :=
    (Submodule.Quotient.mk_eq_zero _).mp hq
  have hp := (F.realFastCoefficient_relative_iff_polynomial e ω hF W hW _).mp hm
  simpa only [map_sub, F.realFirstCoefficientGradedPolynomial_adjoint] using hp

variable [Fintype σ] [DecidableEq σ]

theorem nativeFast_derivativeSystem_to_formal
    (hW : BasisGradedSubmodule bW ωW W.toSubmodule)
    (g : F.realFastDiagonalSubgroup (fun _ : σ => 1) Wf)
    (small rational extra : σ → F.RealFirstCoefficientModule (fun _ : σ => 1))
    (h : ∀ i, F.realFastCoefficientDirectionMap Wf g.val (Pi.single i 1) =
      (Kf).mkQ (small i) +
        F.realFastCoefficientAction (fun _ : σ => 1) (fun _ => Nat.zero_lt_one) Wf g ((Kf).mkQ (rational i)) +
          (Kf).mkQ (extra i)) :
    PolynomialDerivativeSystemMod Vg (F.realAdaptedGradedPolynomialHom e ω hF (fun _ : σ => 1) g.val)
      (fun i => φ (small i)) (fun i => φ (rational i)) (fun i => φ (extra i)) := by
  intro i
  have hi := h i
  rw [F.realFastCoefficientAction_mk] at hi
  change (Kf).mkQ (F.realFirstCoefficientDirectionMap g.val.coord (Pi.single i 1)) = _ at hi
  have hq : (Kf).mkQ (F.realFirstCoefficientDirectionMap g.val.coord (Pi.single i 1) -
      (small i + F.realFirstCoefficientAdjoint (fun _ : σ => 1) g.val (rational i) + extra i)) = 0 := by
    rw [map_sub, map_add, map_add]
    exact sub_eq_zero.mpr hi
  have hm : F.realFirstCoefficientDirectionMap g.val.coord (Pi.single i 1) -
      (small i + F.realFirstCoefficientAdjoint (fun _ : σ => 1) g.val (rational i) + extra i) ∈ Kf :=
    (Submodule.Quotient.mk_eq_zero _).mp hq
  have hp := (F.realFastCoefficient_relative_iff_polynomial e ω hF W hW
    (F.realFirstCoefficientDirectionMap g.val.coord (Pi.single i 1) -
      (small i + F.realFirstCoefficientAdjoint (fun _ : σ => 1) g.val (rational i) + extra i))).mp hm
  simpa only [map_sub, map_add, F.realFirstCoefficientGradedPolynomial_direction,
    F.realFirstCoefficientGradedPolynomial_adjoint] using hp

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ExtractedInitialState
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

variable {σ ι κ L : Type*} [Fintype σ] [DecidableEq σ] [Fintype ι] [Fintype κ]
  [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
  (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded)

local notation "ωW" => (fun a : ReducedSquareBasisIndex s ω => squareBasisWeight ω (Subtype.val a))
local notation "bW" => F.squareFiltration.quotientTop.associatedGradedBasis
  (F.reducedSquareBasis e ω hF) ωW (F.reducedSquareBasis_layers e ω hF)
local notation "bG" => F.associatedGradedBasis e ω hF
local notation "Wf" => F.fastPointwiseSquare e ω hF (fun _ : σ => 1) W
local notation "Kf" => F.realFirstCoefficientFastSubmodule (fun _ : σ => 1) (fun _ => Nat.zero_lt_one)
  (F.reducedSquareFastRelativeSubmodule (fun _ : σ => 1) Wf)
local notation "E" => F.RealFirstCoefficientModule (fun _ : σ => 1)
local notation "φ" => F.realFirstCoefficientGradedPolynomial e ω hF (fun _ : σ => 1)
local notation "ρ" => F.realFastCoefficientAction (fun _ : σ => 1) (fun _ => Nat.zero_lt_one) Wf
local notation "H₁" => F.realFirstCoefficientHorizontal (fun _ : σ => 1)

noncomputable def nativeInitialFormalState
    (hW : BasisGradedSubmodule bW ωW W.toSubmodule)
    (g : F.realFastDiagonalSubgroup (fun _ : σ => 1) Wf)
    (K : Submodule ℚ (L ⧸ F.layer 2)) (bK : Basis κ ℚ K)
    (S R : (κ → ℝ) →ₗ[ℝ] E)
    (small rational : σ → E) (k : σ → κ → ℝ)
    (hSR : ∀ z, (Kf).mkQ (S (Pi.basisFun ℝ κ z)) =
      ρ g ((Kf).mkQ (R (Pi.basisFun ℝ κ z))))
    (hsystem : ∀ i, F.realFastCoefficientDirectionMap Wf g.val (Pi.single i 1) =
      (Kf).mkQ (small i) + ρ g ((Kf).mkQ (rational i)) + (Kf).mkQ (S (k i)))
    (hS : ∀ z, H₁ (S (Pi.basisFun ℝ κ z)) = (1 : ℝ) ⊗ₜ[ℚ] (bK z : L ⧸ F.layer 2))
    (hR : ∀ z, H₁ (R (Pi.basisFun ℝ κ z)) = (1 : ℝ) ⊗ₜ[ℚ] (bK z : L ⧸ F.layer 2))
    (hsmall : ∀ i, H₁ (small i) = 0) (hrational : ∀ i, H₁ (rational i) = 0)
    (hhorizontal : ∀ i, (F.layer 2).mkQ.baseChange ℝ
      (coefficients (F.realAdaptedPolynomialMap (fun _ : σ => 1) g.val.coord) (Finsupp.single i 1)) ∈
        K.baseChange ℝ)
    (T : σ → ℝ) (hT : ∀ i, 0 < T i) (p : ℝ) (l : ℕ) (hl : 0 < l)
    (hlp : (l : ℝ) ≤ Real.exp p)
    (hSbound : ∀ z, F.FirstCoefficientSlowBound e ω hF (fun _ : σ => 1) T
      (Real.exp p) (S (Pi.basisFun ℝ κ z)))
    (hRgrid : ∀ z, F.FirstCoefficientGrid e ω hF (fun _ : σ => 1) l (R (Pi.basisFun ℝ κ z)))
    (hsmallBound : ∀ i, F.FirstCoefficientSlowBound e ω hF (fun _ : σ => 1) T
      (Real.exp p / T i) (small i))
    (hrationalGrid : ∀ i, F.FirstCoefficientGrid e ω hF (fun _ : σ => 1) l (rational i)) :
    F.associatedGradedFiltration.FormalInductionState bG ω
      (realificationLieSubalgebra (F.fullFastGradedDiagonal W))
      (F.fullFastGradedRelative e ω hF W) (F.gradedHorizontalKernel e ω hF K)
      (F.gradedHorizontalKernelBasis e ω hF K bK) T 2 p where
  P := F.realAdaptedGradedPolynomialHom e ω hF (fun _ : σ => 1) g.val
  S := fun z => φ (S (Pi.basisFun ℝ κ z))
  R := fun z => φ (R (Pi.basisFun ℝ κ z))
  small := fun i => φ (small i)
  rational := fun i => φ (rational i)
  k := k
  denominator := l
  denominator_pos := hl
  denominator_bound := hlp
  constant_zero := F.realAdaptedGradedPolynomialLie_constant e ω hF (fun _ : σ => 1) g.val.coord
  mem_U := F.realAdaptedGradedPolynomialLie_fullFast_mem e ω hF W hW g
  graded := F.realAdaptedGradedPolynomialLie_graded e ω hF (fun _ : σ => 1) g.val.coord
  horizontal := F.realAdaptedGradedPolynomialLie_horizontal_mem e ω hF g.val.coord
    ((F.gradedHorizontalKernel e ω hF K).baseChange ℝ)
    (fun i => F.gradedHorizontalKernel_real_mem e ω hF K _ (hhorizontal i))
  lower_log := by intro α d hd hlt; omega
  lower_bracket := by
    intro d hd z α
    have hd0 : d = 0 := by omega
    subst d
    have hz := F.associatedGradedFiltration.realGradeProjection_eq_zero_of_mem_next_layer
      bG ω (F.associatedGradedFiltration_layer e ω hF) 0
      (coefficients (F.realAdaptedGradedPolynomialLie e ω hF (fun _ : σ => 1) g.val.coord) α)
      (by rw [Nat.zero_add, F.associatedGradedFiltration.realification.one_eq_top]; trivial)
    change ⁅basisGradeProjection ((bG).baseChange ℝ) ω 0
      (coefficients (F.realAdaptedGradedPolynomialLie e ω hF (fun _ : σ => 1) g.val.coord) α),
      (1 : ℝ) ⊗ₜ[ℚ] (F.gradedHorizontalKernelBasis e ω hF K bK z : F.AssociatedGraded)⁆ ∈ _
    rw [hz, zero_lie]
    exact Submodule.zero_mem _
  lift_system := F.nativeFast_liftSystem_to_formal e ω hF W hW g
    (fun z => S (Pi.basisFun ℝ κ z)) (fun z => R (Pi.basisFun ℝ κ z)) hSR
  derivative_system := by
    have he : (fun i : σ => basisPolynomialLift (Pi.basisFun ℝ κ)
        (fun z => φ (S (Pi.basisFun ℝ κ z))) (k i)) = (fun i : σ => φ (S (k i))) := by
      funext i
      exact (F.realFirstCoefficientGradedPolynomial_basisLift e ω hF (Pi.basisFun ℝ κ) S (k i)).symm
    rw [he]
    exact F.nativeFast_derivativeSystem_to_formal e ω hF W hW g small rational (fun i => S (k i)) hsystem
  S_shift := fun z => F.realFirstCoefficientGradedPolynomial_homogeneous e ω hF (fun _ : σ => 1) _
  R_shift := fun z => F.realFirstCoefficientGradedPolynomial_homogeneous e ω hF (fun _ : σ => 1) _
  small_shift := fun i => F.realFirstCoefficientGradedPolynomial_homogeneous e ω hF (fun _ : σ => 1) _
  rational_shift := fun i => F.realFirstCoefficientGradedPolynomial_homogeneous e ω hF (fun _ : σ => 1) _
  S_remainder := by
    intro z α
    apply Submodule.mem_sup_right
    have h := F.realFirstCoefficientGradedPolynomial_initial_remainder e ω hF (fun _ : σ => 1)
      (fun _ => Nat.zero_lt_one) (S (Pi.basisFun ℝ κ z)) α
    rw [hS z, LinearMap.baseChange_tmul] at h
    rw [F.gradedHorizontalKernelBasis_coe]
    exact h
  R_remainder := by
    intro z α
    apply Submodule.mem_sup_right
    have h := F.realFirstCoefficientGradedPolynomial_initial_remainder e ω hF (fun _ : σ => 1)
      (fun _ => Nat.zero_lt_one) (R (Pi.basisFun ℝ κ z)) α
    rw [hR z, LinearMap.baseChange_tmul] at h
    rw [F.gradedHorizontalKernelBasis_coe]
    exact h
  small_remainder := fun i α => Submodule.mem_sup_right
    (F.realFirstCoefficientGradedPolynomial_mem_second e ω hF (fun _ : σ => 1)
      (fun _ => Nat.zero_lt_one) (small i) (hsmall i) α)
  rational_remainder := fun i α => Submodule.mem_sup_right
    (F.realFirstCoefficientGradedPolynomial_mem_second e ω hF (fun _ : σ => 1)
      (fun _ => Nat.zero_lt_one) (rational i) (hrational i) α)
  S_bound := fun z => F.realFirstCoefficientGradedPolynomial_bound e ω hF (fun _ : σ => 1) T hT
    (Real.exp_pos p).le _ (hSbound z)
  R_grid := fun z => F.realFirstCoefficientGradedPolynomial_grid e ω hF (fun _ : σ => 1) l _ (hRgrid z)
  small_bound := fun i => F.realFirstCoefficientGradedPolynomial_bound e ω hF (fun _ : σ => 1) T hT
    (div_nonneg (Real.exp_pos p).le (hT i).le) _ (hsmallBound i)
  rational_grid := fun i => F.realFirstCoefficientGradedPolynomial_grid e ω hF (fun _ : σ => 1) l _ (hrationalGrid i)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

variable {σ ι κ ν L : Type*} [Fintype σ] [DecidableEq σ] [Fintype ι]
  [Fintype κ] [Fintype ν] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
  (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded)

local notation "ωW" => (fun a : ReducedSquareBasisIndex s ω => squareBasisWeight ω (Subtype.val a))
local notation "bW" => F.squareFiltration.quotientTop.associatedGradedBasis
  (F.reducedSquareBasis e ω hF) ωW (F.reducedSquareBasis_layers e ω hF)
local notation "Wf" => F.fastPointwiseSquare e ω hF (fun _ : σ => 1) W
local notation "Uf" => F.reducedSquareFastRelativeSubmodule (fun _ : σ => 1) Wf
local notation "J" => F.realFirstCoefficientFastSubmodule (fun _ : σ => 1) (fun _ => Nat.zero_lt_one) Uf
local notation "E" => F.RealFirstCoefficientModule (fun _ : σ => 1)
local notation "Q" => (E ⧸ J)
local notation "ρ" => F.realFastCoefficientAction (fun _ : σ => 1) (fun _ => Nat.zero_lt_one) Wf
local notation "Hq" => F.realFastCoefficientHorizontal (fun _ : σ => 1) (fun _ => Nat.zero_lt_one) Uf

theorem exists_initialFormalState_of_quotient_section
    (hW : BasisGradedSubmodule bW ωW W.toSubmodule)
    (g : F.realFastDiagonalSubgroup (fun _ : σ => 1) Wf)
    (K : Submodule ℚ (L ⧸ F.layer 2)) (bK : Basis κ ℚ K)
    (b : Basis ν ℝ Q) (rows : ν → FirstCoefficientIndex (fun _ : σ => 1) ω)
    (sectionMap : (ν → ℝ) →ₗ[ℝ] E)
    (hsection : ∀ y, (J).mkQ (sectionMap y) = b.equivFun.symm y)
    (S R : (κ → ℝ) →ₗ[ℝ] Q) (small rational : σ → Q) (k : σ → κ → ℝ)
    (hSR : ∀ z, S (Pi.basisFun ℝ κ z) = ρ g (R (Pi.basisFun ℝ κ z)))
    (hsystem : ∀ i, F.realFastCoefficientDirectionMap Wf g.val (Pi.single i 1) =
      small i + ρ g (rational i) + S (k i))
    (hS : ∀ z, Hq (S (Pi.basisFun ℝ κ z)) = (1 : ℝ) ⊗ₜ[ℚ] (bK z : L ⧸ F.layer 2))
    (hR : ∀ z, Hq (R (Pi.basisFun ℝ κ z)) = (1 : ℝ) ⊗ₜ[ℚ] (bK z : L ⧸ F.layer 2))
    (hsmall : ∀ i, Hq (small i) = 0) (hrational : ∀ i, Hq (rational i) = 0)
    (hhorizontal : ∀ i, (F.layer 2).mkQ.baseChange ℝ
      (coefficients (F.realAdaptedPolynomialMap (fun _ : σ => 1) g.val.coord) (Finsupp.single i 1)) ∈
        K.baseChange ℝ)
    (T : σ → ℝ) (hT : ∀ i, 0 < T i) (C p q : ℝ)
    (hbudget : C * Real.exp p ≤ Real.exp q)
    (hsectionBound : ∀ M : ℝ, 0 ≤ M → ∀ y : ν → ℝ,
      (∀ i, |y i| ≤ M / monomialScale T (rows i).val.1) →
        F.FirstCoefficientSlowBound e ω hF (fun _ : σ => 1) T (C * M) (sectionMap y))
    (l m : ℕ) (hm : 0 < m) (hmp : (m : ℝ) ≤ Real.exp q)
    (hsectionGrid : ∀ y : ν → ℝ, y ∈ realDenominatorGrid l →
      F.FirstCoefficientGrid e ω hF (fun _ : σ => 1) m (sectionMap y))
    (hSbound : ∀ z i, |b.equivFun (S (Pi.basisFun ℝ κ z)) i| ≤
      Real.exp p / monomialScale T (rows i).val.1)
    (hRgrid : ∀ z, b.equivFun (R (Pi.basisFun ℝ κ z)) ∈ realDenominatorGrid l)
    (hsmallBound : ∀ j i, |b.equivFun (small j) i| ≤
      (Real.exp p / T j) / monomialScale T (rows i).val.1)
    (hrationalGrid : ∀ i, b.equivFun (rational i) ∈ realDenominatorGrid l) :
    ∃ X : F.associatedGradedFiltration.FormalInductionState (F.associatedGradedBasis e ω hF) ω
      (realificationLieSubalgebra (F.fullFastGradedDiagonal W))
      (F.fullFastGradedRelative e ω hF W) (F.gradedHorizontalKernel e ω hF K)
      (F.gradedHorizontalKernelBasis e ω hF K bK) T 2 q,
      X.P = F.realAdaptedGradedPolynomialHom e ω hF (fun _ : σ => 1) g.val := by
  let rep := F.realFastCoefficientRepresentative (fun _ : σ => 1) (fun _ => Nat.zero_lt_one) Uf b sectionMap
  have hrep (x : Q) : (J).mkQ (rep x) = x :=
    F.realFastCoefficientRepresentative_mk (fun _ : σ => 1) (fun _ => Nat.zero_lt_one) Uf b sectionMap hsection x
  have hrepH (x : Q) : F.realFirstCoefficientHorizontal (fun _ : σ => 1) (rep x) = Hq x :=
    F.realFastCoefficientRepresentative_horizontal (fun _ : σ => 1) (fun _ => Nat.zero_lt_one)
      Uf b sectionMap hsection x
  have hrepBound {M : ℝ} (hM : 0 ≤ M) (x : Q)
      (hx : ∀ i, |b.equivFun x i| ≤ M / monomialScale T (rows i).val.1) :
      F.FirstCoefficientSlowBound e ω hF (fun _ : σ => 1) T (C * M) (rep x) :=
    hsectionBound M hM (b.equivFun x) hx
  have hrepGrid (x : Q) (hx : b.equivFun x ∈ realDenominatorGrid l) :
      F.FirstCoefficientGrid e ω hF (fun _ : σ => 1) m (rep x) :=
    hsectionGrid (b.equivFun x) hx
  have hnSR (z : κ) : (J).mkQ ((rep.comp S) (Pi.basisFun ℝ κ z)) =
      ρ g ((J).mkQ ((rep.comp R) (Pi.basisFun ℝ κ z))) := by
    simp only [LinearMap.comp_apply, hrep]
    exact hSR z
  have hnSystem (i : σ) : F.realFastCoefficientDirectionMap Wf g.val (Pi.single i 1) =
      (J).mkQ (rep (small i)) + ρ g ((J).mkQ (rep (rational i))) + (J).mkQ ((rep.comp S) (k i)) := by
    simp only [LinearMap.comp_apply, hrep]
    exact hsystem i
  have hnSBound (z : κ) : F.FirstCoefficientSlowBound e ω hF (fun _ : σ => 1) T
      (Real.exp q) ((rep.comp S) (Pi.basisFun ℝ κ z)) :=
    FirstCoefficientSlowBound.mono F e ω hF (fun _ : σ => 1) T hT hbudget _
      (hrepBound (Real.exp_pos p).le _ (hSbound z))
  have hnSmallBound (i : σ) : F.FirstCoefficientSlowBound e ω hF (fun _ : σ => 1) T
      (Real.exp q / T i) (rep (small i)) := by
    have hb : C * (Real.exp p / T i) ≤ Real.exp q / T i := by
      rw [← mul_div_assoc]
      exact div_le_div_of_nonneg_right hbudget (hT i).le
    exact FirstCoefficientSlowBound.mono F e ω hF (fun _ : σ => 1) T hT hb _
      (hrepBound (div_nonneg (Real.exp_pos p).le (hT i).le) _ (hsmallBound i))
  let X := F.nativeInitialFormalState e ω hF W hW g K bK (rep.comp S) (rep.comp R)
    (fun i => rep (small i)) (fun i => rep (rational i)) k hnSR hnSystem
    (fun z => (hrepH _).trans (hS z)) (fun z => (hrepH _).trans (hR z))
    (fun i => (hrepH _).trans (hsmall i)) (fun i => (hrepH _).trans (hrational i))
    hhorizontal T hT q m hm hmp hnSBound (fun z => hrepGrid _ (hRgrid z))
    hnSmallBound (fun i => hrepGrid _ (hrationalGrid i))
  exact ⟨X, rfl⟩

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

variable {σ ι κ ν L : Type*} [Fintype σ] [DecidableEq σ] [Fintype ι]
  [Fintype κ] [Fintype ν] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
  (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded)

local notation "ωW" => (fun a : ReducedSquareBasisIndex s ω => squareBasisWeight ω (Subtype.val a))
local notation "bW" => F.squareFiltration.quotientTop.associatedGradedBasis
  (F.reducedSquareBasis e ω hF) ωW (F.reducedSquareBasis_layers e ω hF)
local notation "Wf" => F.fastPointwiseSquare e ω hF (fun _ : σ => 1) W
local notation "Uf" => F.reducedSquareFastRelativeSubmodule (fun _ : σ => 1) Wf
local notation "J" => F.realFirstCoefficientFastSubmodule (fun _ : σ => 1) (fun _ => Nat.zero_lt_one) Uf
local notation "E" => F.RealFirstCoefficientModule (fun _ : σ => 1)
local notation "Q" => (E ⧸ J)
local notation "ρ" => F.realFastCoefficientAction (fun _ : σ => 1) (fun _ => Nat.zero_lt_one) Wf
local notation "Hq" => F.realFastCoefficientHorizontal (fun _ : σ => 1) (fun _ => Nat.zero_lt_one) Uf

theorem exists_initialFormalState_of_normalized_quotient
    (hW : BasisGradedSubmodule bW ωW W.toSubmodule)
    (g : F.realFastDiagonalSubgroup (fun _ : σ => 1) Wf)
    (K : Submodule ℚ (L ⧸ F.layer 2)) (bK : Basis κ ℚ K)
    (b : Basis ν ℝ Q) (rows : ν → FirstCoefficientIndex (fun _ : σ => 1) ω)
    (sectionMap : (ν → ℝ) →ₗ[ℝ] E)
    (hsection : ∀ y, (J).mkQ (sectionMap y) = b.equivFun.symm y)
    (S R : (K.baseChange ℝ) →ₗ[ℝ] Q) (small rational : σ → Q) (k : σ → K.baseChange ℝ)
    (hSR : S = (ρ g).toLinearMap.comp R)
    (hsystem : ∀ i, F.realFastCoefficientDirectionMap Wf g.val (Pi.single i 1) =
      small i + ρ g (rational i) + S (k i))
    (hS : (Hq).comp S = (K.baseChange ℝ).subtype)
    (hR : (Hq).comp R = (K.baseChange ℝ).subtype)
    (hsmall : ∀ i, Hq (small i) = 0) (hrational : ∀ i, Hq (rational i) = 0)
    (hlinear : ∀ i, (F.layer 2).mkQ.baseChange ℝ
      (coefficients (F.realAdaptedPolynomialMap (fun _ : σ => 1) g.val.coord) (Finsupp.single i 1)) =
        (k i).val)
    (T : σ → ℝ) (hT : ∀ i, 0 < T i) (C p q : ℝ)
    (hbudget : C * Real.exp p ≤ Real.exp q)
    (hsectionBound : ∀ M : ℝ, 0 ≤ M → ∀ y : ν → ℝ,
      (∀ i, |y i| ≤ M / monomialScale T (rows i).val.1) →
        F.FirstCoefficientSlowBound e ω hF (fun _ : σ => 1) T (C * M) (sectionMap y))
    (l m : ℕ) (hm : 0 < m) (hmp : (m : ℝ) ≤ Real.exp q)
    (hsectionGrid : ∀ y : ν → ℝ, y ∈ realDenominatorGrid l →
      F.FirstCoefficientGrid e ω hF (fun _ : σ => 1) m (sectionMap y))
    (hSbound : ∀ z i, |b.equivFun (S (realSubmoduleBasis K bK z)) i| ≤
      Real.exp p / monomialScale T (rows i).val.1)
    (hRgrid : ∀ z, b.equivFun (R (realSubmoduleBasis K bK z)) ∈ realDenominatorGrid l)
    (hsmallBound : ∀ j i, |b.equivFun (small j) i| ≤
      (Real.exp p / T j) / monomialScale T (rows i).val.1)
    (hrationalGrid : ∀ i, b.equivFun (rational i) ∈ realDenominatorGrid l) :
    ∃ X : F.associatedGradedFiltration.FormalInductionState (F.associatedGradedBasis e ω hF) ω
      (realificationLieSubalgebra (F.fullFastGradedDiagonal W))
      (F.fullFastGradedRelative e ω hF W) (F.gradedHorizontalKernel e ω hF K)
      (F.gradedHorizontalKernelBasis e ω hF K bK) T 2 q,
      X.P = F.realAdaptedGradedPolynomialHom e ω hF (fun _ : σ => 1) g.val := by
  let I := realSubmoduleParameterization K bK
  let Sc := S.comp I.toLinearMap
  let Rc := R.comp I.toLinearMap
  let kc := fun i => I.symm (k i)
  have hSc (z : κ) : Sc (Pi.basisFun ℝ κ z) = S (realSubmoduleBasis K bK z) := by
    change S (realSubmoduleParameterization K bK (Pi.basisFun ℝ κ z)) = _
    rw [realSubmoduleParameterization_basis]
  have hRc (z : κ) : Rc (Pi.basisFun ℝ κ z) = R (realSubmoduleBasis K bK z) := by
    change R (realSubmoduleParameterization K bK (Pi.basisFun ℝ κ z)) = _
    rw [realSubmoduleParameterization_basis]
  have hSRc (z : κ) : Sc (Pi.basisFun ℝ κ z) = ρ g (Rc (Pi.basisFun ℝ κ z)) := by
    exact LinearMap.congr_fun hSR (I (Pi.basisFun ℝ κ z))
  have hScH (z : κ) : Hq (Sc (Pi.basisFun ℝ κ z)) = (1 : ℝ) ⊗ₜ[ℚ] (bK z : L ⧸ F.layer 2) := by
    have h := LinearMap.congr_fun hS (I (Pi.basisFun ℝ κ z))
    change Hq (Sc (Pi.basisFun ℝ κ z)) = (I (Pi.basisFun ℝ κ z)).val at h
    exact h.trans ((congrArg Subtype.val (realSubmoduleParameterization_basis K bK z)).trans
      (realSubmoduleBasis_coe K bK z))
  have hRcH (z : κ) : Hq (Rc (Pi.basisFun ℝ κ z)) = (1 : ℝ) ⊗ₜ[ℚ] (bK z : L ⧸ F.layer 2) := by
    have h := LinearMap.congr_fun hR (I (Pi.basisFun ℝ κ z))
    change Hq (Rc (Pi.basisFun ℝ κ z)) = (I (Pi.basisFun ℝ κ z)).val at h
    exact h.trans ((congrArg Subtype.val (realSubmoduleParameterization_basis K bK z)).trans
      (realSubmoduleBasis_coe K bK z))
  have hsys (i : σ) : F.realFastCoefficientDirectionMap Wf g.val (Pi.single i 1) =
      small i + ρ g (rational i) + Sc (kc i) := by
    change _ = small i + ρ g (rational i) + S (I (I.symm (k i)))
    rw [LinearEquiv.apply_symm_apply]
    exact hsystem i
  apply F.exists_initialFormalState_of_quotient_section e ω hF W hW g K bK b rows sectionMap hsection
    Sc Rc small rational kc hSRc hsys hScH hRcH hsmall hrational
    (fun i => (hlinear i).symm ▸ (k i).property) T hT C p q hbudget hsectionBound l m hm hmp hsectionGrid
  · intro z i
    exact (congrArg (fun x : Q => |b.equivFun x i|) (hSc z)).le.trans (hSbound z i)
  · intro z
    exact (congrArg (fun x : Q => b.equivFun x ∈ realDenominatorGrid l) (hRc z)).mpr (hRgrid z)
  · exact hsmallBound
  · exact hrationalGrid

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeWeightPairRemoval
namespace OAI

section

namespace Erdos3

open scoped BigOperators TensorProduct

namespace NativeMixedReductionData

attribute [local instance] NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s : ℕ} {p P : ℝ}
  {V : NativeMultidegreeNilcharacter (fun _ : ReplicatedIndex (mixedCorrelationDegree s) => 1) p}
  (D : NativeMixedReductionData V P)

noncomputable def correction (h δ : ℤ) (k : Fin V.outputDim) (a : MixedExpansionIndex V)
    (b : Fin (D.translation.selectedExpansion k a).count) (c : Fin (D.lower h δ a).count) (n : ℤ) : ℂ :=
  V.eval (firstTranslationCoordinate (mixedTranslationCoordinates s) a) (fun j => correlationInput h n j.1) *
    D.translationTerm k a b ![h, n, δ] * D.lowerTerm h δ a c n

end NativeMixedReductionData

end Erdos3

end

section

namespace Erdos3

namespace NativeMixedReductionData

attribute [local instance] NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s : ℕ} {p P : ℝ}
  {V : NativeMultidegreeNilcharacter (fun _ : ReplicatedIndex (mixedCorrelationDegree s) => 1) p}
  (D : NativeMixedReductionData V P)

theorem translationGlobal_sample (k : Fin 4 → Fin V.outputDim) (t : D.TranslationCode k)
    (h₁ h₂ h₃ h₄ n δ : ℤ) (hrel : -h₁ + h₂ + h₃ - h₄ = 0) :
    D.translationGlobal k t ![h₁, h₂, h₃, n, δ] =
      D.translationTerm (k 1) t.second t.secondTerm ![h₂, n, δ] *
        star (D.translationTerm (k 3) t.fourth t.fourthTerm ![h₄, n, δ]) := by
  have hh₄ : h₄ = h₂ + h₃ - h₁ := by omega
  subst h₄
  rfl

end NativeMixedReductionData

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.FullFastRelativeSpanning
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {ι κ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))

local notation "ωW" => (fun a : ReducedSquareBasisIndex s ω => squareBasisWeight ω (Subtype.val a))
local notation "bW" => F.squareFiltration.quotientTop.associatedGradedBasis
  (F.reducedSquareBasis e ω hF) ωW (F.reducedSquareBasis_layers e ω hF)
local notation "ωQ" => (fun a : QuotientTopBasisIndex s ω => ω (Subtype.val a))
local notation "bQ" => F.quotientTop.associatedGradedBasis
  (F.quotientTopBasis e ω hF) ωQ (F.quotientTopBasis_layers e ω hF)

theorem reducedSquareGradedSndMap_basis_height (a : ReducedSquareBasisIndex s ω)
    (i : QuotientTopBasisIndex s ω) :
    RationalHeightLE ((bQ).repr (F.reducedSquareGradedSndMap (bW a)) i) 1 := by
  rw [F.reducedSquareGradedSndMap_coordinate e ω hF]
  exact basis_repr_height_one bW a _

end Erdos3.NilpotentLieFiltration

end

end OAI
end


