-- Prove2me | Definitions.Def_OAIE3v2B183
-- name    : OAIE3v2B183
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T11:52:55.534395+00:00
-- url     : https://prove2.me/theorems/02756bcd-05a1-4db0-b560-5c5bbaa20e65
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 186 of 311
-- statement:
--   Definitions bundle 186 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B161`, `OAIE3v2B162`, `OAIE3v2B166`, `OAIE3v2B167`, `OAIE3v2B168` of this split.
--
--   Modules: `Estimates/ExtractedInitialState.lean`, `Estimates/FastHorizontalFactorization.lean`, `Estimates/GradedUnitEvaluation.lean`, `Estimates/NativeCrossFactorization.lean`, `Estimates/ReducedRelativeCoefficientBounds.lean`, `Estimates/ReindexedFastCoefficientSection.lean`, `Geometry/ControlledLayerOneCoordinates.lean`, `Geometry/FastCoefficientDerivativeCoordinates.lean`, `Geometry/GradedTopCoordinates.lean`, `Geometry/NativeCoordinateDerivativeSystem.lean`, `Geometry/RealFastCoefficientCoordinates.lean`, `Linear/FullFastHorizontalSpanning.lean`, `Linear/LayerOneProjectionMatrixBounds.lean`, `Polynomial/NativeFormalPolynomialSystems.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B161
import Definitions.Def_OAIE3v2B162
import Definitions.Def_OAIE3v2B166
import Definitions.Def_OAIE3v2B167
import Definitions.Def_OAIE3v2B168

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.RealFastCoefficientCoordinates
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module
open scoped TensorProduct

variable {σ ι L : Type*} [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})) (w : σ → ℕ)

theorem realFirstCoefficientHorizontal_projector_repr
    (x : F.RealFirstCoefficientModule w) (z : FirstCoefficientIndex w ω) :
    (F.realFirstCoefficientBasis b ω hF w).repr
        (F.realFirstCoefficientHorizontalSection w (F.realFirstCoefficientHorizontal w x)) z =
      if z.val.1 = 0 then (F.realFirstCoefficientBasis b ω hF w).repr x z else 0 := by
  classical
  obtain ⟨x, rfl⟩ := (F.firstCoefficientRealEquiv w).surjective x
  change (F.realFirstCoefficientBasis b ω hF w).repr
    (F.firstCoefficientRealEquiv w ((F.firstCoefficientHorizontalSection w).baseChange ℝ
      ((F.firstCoefficientHorizontal w).baseChange ℝ
        ((F.firstCoefficientRealEquiv w).symm (F.firstCoefficientRealEquiv w x))))) z = _
  rw [LinearEquiv.symm_apply_apply, F.firstCoefficientRealEquiv_coordinates,
    F.firstCoefficientRealEquiv_coordinates]
  exact baseChange_coordinate_projector_repr (F.firstCoefficientBasis b ω hF w)
    (F.firstCoefficientHorizontal w) (F.firstCoefficientHorizontalSection w)
    (fun z => z.val.1 = 0) (F.firstCoefficientHorizontal_projector_repr b ω hF w) x z

theorem realFirstCoefficientHorizontal_projector (x : F.RealFirstCoefficientModule w) :
    F.realFirstCoefficientHorizontalSection w (F.realFirstCoefficientHorizontal w x) =
      basisCoordinateProjection (F.realFirstCoefficientBasis b ω hF w) {z | z.val.1 = 0} x := by
  classical
  apply (F.realFirstCoefficientBasis b ω hF w).repr.injective
  ext z
  rw [F.realFirstCoefficientHorizontal_projector_repr, basisCoordinateProjection_repr]
  rfl

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module
open scoped TensorProduct

variable {σ ι L : Type*} [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
  (w : σ → ℕ) (hw : ∀ i, 0 < w i)
  (U : Submodule ℚ (F.squareFiltration.quotientTop.PolynomialSymbol w))
  (b : Basis (Fin d) ℝ (F.RealFirstCoefficientModule w ⧸
    F.realFirstCoefficientFastSubmodule w hw U))
  (rows : Fin d → FirstCoefficientIndex w ω)
  (hblock : ∀ i j, (rows j).val.1 ≠ i.val.1 →
    b.repr ((F.realFirstCoefficientFastSubmodule w hw U).mkQ
      (F.realFirstCoefficientBasis e ω hF w i)) j = 0)

include hblock

theorem realFastCoefficientHorizontal_projector
    (x : F.RealFirstCoefficientModule w ⧸ F.realFirstCoefficientFastSubmodule w hw U) :
    F.realFastCoefficientHorizontalSection w hw U (F.realFastCoefficientHorizontal w hw U x) =
      basisCoordinateProjection b {j | (rows j).val.1 = 0} x := by
  classical
  obtain ⟨x, rfl⟩ := (F.realFirstCoefficientFastSubmodule w hw U).mkQ_surjective x
  change (F.realFirstCoefficientFastSubmodule w hw U).mkQ
    (F.realFirstCoefficientHorizontalSection w (F.realFirstCoefficientHorizontal w x)) = _
  rw [F.realFirstCoefficientHorizontal_projector e ω hF w]
  exact basisBlockMap_commutes (F.realFirstCoefficientBasis e ω hF w) b
    (fun i => i.val.1) (fun j => (rows j).val.1)
    (F.realFirstCoefficientFastSubmodule w hw U).mkQ hblock 0 x

theorem realFastCoefficientHorizontal_projector_repr
    (x : F.RealFirstCoefficientModule w ⧸ F.realFirstCoefficientFastSubmodule w hw U)
    (j : Fin d) :
    b.repr (F.realFastCoefficientHorizontalSection w hw U
      (F.realFastCoefficientHorizontal w hw U x)) j =
      if (rows j).val.1 = 0 then b.repr x j else 0 := by
  rw [F.realFastCoefficientHorizontal_projector e ω hF w hw U b rows hblock]
  exact basisCoordinateProjection_repr b {j | (rows j).val.1 = 0} x j

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ReducedRelativeCoefficientBounds
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

theorem realFirstCoefficientAdjoint_matrix_entry (w : σ → ℕ)
    [Fintype (FirstCoefficientIndex w ω)] [DecidableEq (FirstCoefficientIndex w ω)]
    (g : F.RealAdaptedPolynomialGroup w) (i k : FirstCoefficientIndex w ω)
    (hki : ω k.val.2 ≤ ω i.val.2) :
    LinearMap.toMatrix (F.realFirstCoefficientBasis b ω hF w) (F.realFirstCoefficientBasis b ω hF w)
      (F.realFirstCoefficientAdjoint w g).toLinearMap k i = if i = k then 1 else 0 := by
  rw [LinearMap.toMatrix_apply]
  change (F.realFirstCoefficientBasis b ω hF w).repr
    (F.realFirstCoefficientAdjoint w g (F.realFirstCoefficientBasis b ω hF w i)) k = _
  rw [F.realFirstCoefficientAdjoint_basis_coordinate b ω hF w g i k hki]
  exact (F.realFirstCoefficientBasis b ω hF w).equivFun_self i k

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FastHorizontalFactorization
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))

theorem mem_realLayerOneGradedSubmodule_mk (U : LieSubalgebra ℚ F.AssociatedGraded)
    (x : ℝ ⊗[ℚ] L) :
    (F.layer 2).mkQ.baseChange ℝ x ∈ (F.layerOneGradedSubmodule e ω hF U).baseChange ℝ ↔
      (F.gradedPieceProjection e ω hF 1).baseChange ℝ x ∈ realificationLieSubalgebra U := by
  rw [F.mem_realLayerOneGradedSubmodule, F.realLayerOneGradedMap_mk]

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
  (U : LieSubalgebra ℚ F.AssociatedGraded)

omit [Fintype σ] in
theorem pointwise_horizontal_coefficient_mem
    (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra (fun _ : σ => 1))
    (hx : F.realExtendedSymbolMap (fun _ => 1) x ∈
      realificationLieSubalgebra (F.symbolPointwiseSubalgebra e ω hF (fun _ => 1) U)) (i : σ) :
    (F.layer 2).mkQ.baseChange ℝ
      (coefficients (F.realAdaptedPolynomialMap (fun _ => 1) x) (Finsupp.single i 1)) ∈
        (F.layerOneGradedSubmodule e ω hF U).baseChange ℝ := by
  apply (F.mem_realLayerOneGradedSubmodule_mk e ω hF U _).mpr
  have h := (F.mem_real_symbolPointwiseSubalgebra_iff_coefficients e ω hF (fun _ => 1) U _).mp hx
    (Finsupp.single i 1)
  rw [← F.realSymbolOfPolynomial_realAdaptedPolynomialMap e ω hF,
    F.realGradedSymbolPolynomial_coefficient_of_polynomial] at h
  simpa only [Finsupp.weight_single, one_smul] using h

theorem pointwise_horizontal_derivative_mem [DecidableEq σ]
    (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra (fun _ : σ => 1))
    (hx : F.realExtendedSymbolMap (fun _ => 1) x ∈
      realificationLieSubalgebra (F.symbolPointwiseSubalgebra e ω hF (fun _ => 1) U))
    (hzero : coefficients (F.realAdaptedPolynomialMap (fun _ => 1) x) 0 = 0) (i : σ) :
    F.realFirstCoefficientHorizontal (fun _ => 1)
      (F.realFirstCoefficientDirectionMap x (Pi.single i 1)) ∈
        (F.layerOneGradedSubmodule e ω hF U).baseChange ℝ := by
  rw [F.realFirstCoefficientDirectionMap_horizontal_unit e ω hF i x hzero]
  exact F.pointwise_horizontal_coefficient_mem e ω hF U x hx i

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

omit e ω hF [Fintype σ] in
theorem realFastCoefficient_remove_lifts {K : Type*} [AddCommGroup K] [Module ℝ K]
    (a b c : F.realFastDiagonalSubgroup (fun _ : σ => 1) U)
    (S R : K →ₗ[ℝ] F.RealFastCoefficientModule (fun _ : σ => 1) (fun _ => Nat.zero_lt_one) U)
    (hSR : S = (F.realFastCoefficientAction (fun _ => 1) (fun _ => Nat.zero_lt_one) U (a * b * c)).toLinearMap.comp R) :
    (F.realFastCoefficientAction (fun _ => 1) (fun _ => Nat.zero_lt_one) U a).symm.toLinearMap.comp S =
      (F.realFastCoefficientAction (fun _ => 1) (fun _ => Nat.zero_lt_one) U b).toLinearMap.comp
        ((F.realFastCoefficientAction (fun _ => 1) (fun _ => Nat.zero_lt_one) U c).toLinearMap.comp R) := by
  let ρ := F.realFastCoefficientAction (fun _ : σ => 1) (fun _ => Nat.zero_lt_one) U
  exact linear_lift_remove (ρ a) (ρ c) (ρ (a * b * c)) (ρ b)
    (linear_action_triple ρ a b c) S R hSR

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
local notation "ωQ" => (fun i : QuotientTopBasisIndex s ω => ω (Subtype.val i))
local notation "bQ" => F.quotientTop.associatedGradedBasis
  (F.quotientTopBasis e ω hF) ωQ (F.quotientTopBasis_layers e ω hF)

theorem fastGradedDiagonal_graded
    (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded)
    (hW : BasisGradedSubmodule bW ωW W.toSubmodule) :
    BasisGradedSubmodule bQ ωQ (F.fastGradedDiagonal W).toSubmodule :=
  F.squareFiltration.quotientTop.associatedGradedMap_image_graded F.quotientTop
    (F.reducedSquareBasis e ω hF) ωW (F.reducedSquareBasis_layers e ω hF)
    (F.quotientTopBasis e ω hF) ωQ (F.quotientTopBasis_layers e ω hF)
    F.reducedSquareSnd F.reducedSquareSnd_mem W hW

theorem fullFastGradedDiagonal_graded
    (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded)
    (hW : BasisGradedSubmodule bW ωW W.toSubmodule) :
    BasisGradedSubmodule (F.associatedGradedBasis e ω hF) ω (F.fullFastGradedDiagonal W).toSubmodule :=
  F.associatedGradedMap_comap_graded F.quotientTop e ω hF
    (F.quotientTopBasis e ω hF) ωQ (F.quotientTopBasis_layers e ω hF)
    (lieQuotientMap (F.layerIdeal (s + 1))) (fun _ _ hx => F.quotientLie_mem _ le_rfl hx)
    (F.fastGradedDiagonal W) (F.fastGradedDiagonal_graded e ω hF W hW)

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.GradedTopCoordinates
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))

local notation "ωQ" => (fun i : QuotientTopBasisIndex s ω => ω (Subtype.val i))
local notation "bQ" => F.quotientTop.associatedGradedBasis
  (F.quotientTopBasis e ω hF) ωQ (F.quotientTopBasis_layers e ω hF)
local notation "ωW" => (fun i : ReducedSquareBasisIndex s ω => squareBasisWeight ω (Subtype.val i))
local notation "bW" => F.squareFiltration.quotientTop.associatedGradedBasis
  (F.reducedSquareBasis e ω hF) ωW (F.reducedSquareBasis_layers e ω hF)

theorem quotientTopGradedMap_kernel :
    LinearMap.ker F.quotientTopGradedMap.toLinearMap =
      Submodule.span ℚ (F.associatedGradedBasis e ω hF '' {i | s + 1 ≤ ω i}) := by
  ext x
  rw [basis_mem_span_image_iff]
  constructor
  · intro hx i hi
    have he := congrArg (fun y => (bQ).repr y ⟨i, hi⟩) (show F.quotientTopGradedMap x = 0 from hx)
    simpa only [F.quotientTopGradedMap_coordinate, map_zero, Finsupp.zero_apply] using he
  · intro hx
    change F.quotientTopGradedMap x = 0
    apply (bQ).repr.injective
    ext i
    rw [F.quotientTopGradedMap_coordinate, map_zero, Finsupp.zero_apply]
    exact hx i.val i.property

theorem reducedSquareGradedSndMap_coordinate (x : F.squareFiltration.quotientTop.AssociatedGraded)
    (i : QuotientTopBasisIndex s ω) :
    (bQ).repr (F.reducedSquareGradedSndMap x) i = (bW).repr x (reducedSquareDiagonalIndex s ω i) := by
  rw [F.quotientTop.associatedGradedBasis_repr, F.squareFiltration.quotientTop.associatedGradedBasis_repr]
  exact F.reducedSquareSndSymbolMap_repr e ω hF (fun _ : Unit => 1) x
    ⟨(unitMonomial (ω i.val), i), weight_unitMonomial (ω i.val)⟩

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

variable {ι κ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))

theorem layerOneGradedMap_projection (x : F.AssociatedGraded) :
    F.layerOneGradedMap e ω hF (F.gradedLayerOneProjection e ω hF x) =
      basisGradeProjection (F.associatedGradedBasis e ω hF) ω 1 x := by
  apply (F.associatedGradedBasis e ω hF).repr.injective
  ext i
  change (F.associatedGradedBasis e ω hF).repr
    (F.gradedPieceProjection e ω hF 1 (supportedQuotientSection e (F.layer 2) {i | 2 ≤ ω i}
      (hF 2) (F.gradedLayerOneProjection e ω hF x))) i = _
  rw [F.gradedPieceProjection_coordinate, basisGradeProjection_repr]
  by_cases hi : ω i = 1
  · rw [if_pos hi, if_pos hi]
    have hni : ¬2 ≤ ω i := by omega
    rw [supportedQuotientSection_coordinate e (F.layer 2) {i | 2 ≤ ω i}
      (hF 2) _ ⟨i, hni⟩]
    exact F.gradedLayerOneProjection_coordinate e ω hF x ⟨i, hni⟩
  · rw [if_neg hi, if_neg hi]

theorem layerOneGradedSubmodule_eq_image (U : LieSubalgebra ℚ F.AssociatedGraded)
    (hU : BasisGradedSubmodule (F.associatedGradedBasis e ω hF) ω U.toSubmodule) :
    F.layerOneGradedSubmodule e ω hF U = U.toSubmodule.map (F.gradedLayerOneProjection e ω hF) := by
  ext x
  constructor
  · intro hx
    exact ⟨F.layerOneGradedMap e ω hF x, hx, F.gradedLayerOneProjection_rightInverse e ω hF x⟩
  · rintro ⟨v, hv, rfl⟩
    change F.layerOneGradedMap e ω hF (F.gradedLayerOneProjection e ω hF v) ∈ U
    rw [F.layerOneGradedMap_projection]
    exact hU 1 v hv

theorem gradedLayerOneProjection_spanning (U : LieSubalgebra ℚ F.AssociatedGraded)
    (hU : BasisGradedSubmodule (F.associatedGradedBasis e ω hF) ω U.toSubmodule)
    (v : κ → F.AssociatedGraded) (hv : Submodule.span ℚ (Set.range v) = U.toSubmodule) :
    Submodule.span ℚ (Set.range (fun j => F.gradedLayerOneProjection e ω hF (v j))) =
      F.layerOneGradedSubmodule e ω hF U := by
  rw [F.layerOneGradedSubmodule_eq_image e ω hF U hU, ← hv, Submodule.map_span, ← Set.range_comp]
  rfl

theorem gradedLayerOneProjection_height (x : F.AssociatedGraded) {H : ℕ}
    (hx : ∀ i, RationalHeightLE ((F.associatedGradedBasis e ω hF).repr x i) H) :
    ∀ i, RationalHeightLE ((F.layerOneBasis e ω hF).repr (F.gradedLayerOneProjection e ω hF x) i) H := by
  intro i
  rw [F.gradedLayerOneProjection_coordinate]
  exact hx i.val

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {ι κ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))

local notation "ωW" => (fun i : ReducedSquareBasisIndex s ω => squareBasisWeight ω (Subtype.val i))
local notation "bW" => F.squareFiltration.quotientTop.associatedGradedBasis
  (F.reducedSquareBasis e ω hF) ωW (F.reducedSquareBasis_layers e ω hF)

theorem fullFastDiagonalGenerators_span
    (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded)
    (v : κ → F.squareFiltration.quotientTop.AssociatedGraded)
    (hv : Submodule.span ℚ (Set.range v) = W.toSubmodule) :
    Submodule.span ℚ (Set.range (F.fullFastDiagonalGenerators e ω hF v)) =
      (F.fullFastGradedDiagonal W).toSubmodule := by
  have himage : Submodule.span ℚ (Set.range (fun j => F.reducedSquareGradedSndMap (v j))) =
      (F.fastGradedDiagonal W).toSubmodule := by
    change _ = W.toSubmodule.map F.reducedSquareGradedSndMap.toLinearMap
    rw [← hv, Submodule.map_span, ← Set.range_comp]
    rfl
  have hker : Submodule.span ℚ (Set.range (fun i : TopGradedBasisIndex s ω =>
      F.associatedGradedBasis e ω hF i.val)) = LinearMap.ker F.quotientTopGradedMap.toLinearMap := by
    rw [F.quotientTopGradedMap_kernel e ω hF]
    congr 1
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨i.val, i.property, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨⟨i, hi⟩, rfl⟩
  exact split_preimage_spanning F.quotientTopGradedMap.toLinearMap
    (F.quotientTopGradedSection e ω hF) (F.quotientTopGradedSection_rightInverse e ω hF)
    (F.fastGradedDiagonal W).toSubmodule (fun j => F.reducedSquareGradedSndMap (v j)) himage
    (fun i : TopGradedBasisIndex s ω => F.associatedGradedBasis e ω hF i.val) hker

theorem fullFastDiagonalGenerators_height
    (v : κ → F.squareFiltration.quotientTop.AssociatedGraded) {H : ℕ} (hH : 1 ≤ H)
    (hv : ∀ j i, RationalHeightLE ((bW).repr (v j) i) H) :
    ∀ j i, RationalHeightLE ((F.associatedGradedBasis e ω hF).repr
      (F.fullFastDiagonalGenerators e ω hF v j) i) H := by
  intro j i
  cases j with
  | inl j =>
    change RationalHeightLE ((F.associatedGradedBasis e ω hF).repr
      (F.quotientTopGradedSection e ω hF (F.reducedSquareGradedSndMap (v j))) i) H
    by_cases hi : s + 1 ≤ ω i
    · rw [F.quotientTopGradedSection_coordinate_zero e ω hF _ i hi]
      exact rationalHeightLE_zero hH
    · rw [F.quotientTopGradedSection_coordinate e ω hF _ ⟨i, hi⟩,
        F.reducedSquareGradedSndMap_coordinate]
      exact hv j _
  | inr j =>
    exact (basis_repr_height_one (F.associatedGradedBasis e ω hF) j.val i).mono hH

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module
open scoped TensorProduct Matrix

variable {ι κ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))

local notation "ωW" => (fun i : ReducedSquareBasisIndex s ω => squareBasisWeight ω (Subtype.val i))
local notation "bW" => F.squareFiltration.quotientTop.associatedGradedBasis
  (F.reducedSquareBasis e ω hF) ωW (F.reducedSquareBasis_layers e ω hF)

noncomputable def fullFastHorizontalGenerators
    (v : κ → F.squareFiltration.quotientTop.AssociatedGraded) :
    κ ⊕ TopGradedBasisIndex s ω → L ⧸ F.layer 2 :=
  fun j => F.gradedLayerOneProjection e ω hF (F.fullFastDiagonalGenerators e ω hF v j)

theorem fullFastHorizontalGenerators_span
    (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded)
    (hW : BasisGradedSubmodule bW ωW W.toSubmodule)
    (v : κ → F.squareFiltration.quotientTop.AssociatedGraded)
    (hv : Submodule.span ℚ (Set.range v) = W.toSubmodule) :
    Submodule.span ℚ (Set.range (F.fullFastHorizontalGenerators e ω hF v)) =
      F.layerOneGradedSubmodule e ω hF (F.fullFastGradedDiagonal W) :=
  F.gradedLayerOneProjection_spanning e ω hF (F.fullFastGradedDiagonal W)
    (F.fullFastGradedDiagonal_graded e ω hF W hW) (F.fullFastDiagonalGenerators e ω hF v)
    (F.fullFastDiagonalGenerators_span e ω hF W v hv)

theorem fullFastHorizontalGenerators_height
    (v : κ → F.squareFiltration.quotientTop.AssociatedGraded) {H : ℕ} (hH : 1 ≤ H)
    (hv : ∀ j i, RationalHeightLE ((bW).repr (v j) i) H) :
    ∀ j i, RationalHeightLE ((F.layerOneBasis e ω hF).repr
      (F.fullFastHorizontalGenerators e ω hF v j) i) H := by
  intro j
  exact F.gradedLayerOneProjection_height e ω hF (F.fullFastDiagonalGenerators e ω hF v j)
    (F.fullFastDiagonalGenerators_height e ω hF v hH hv j)

noncomputable def fullFastHorizontalMatrix
    (v : κ → F.squareFiltration.quotientTop.AssociatedGraded) :
    Matrix (LayerOneBasisIndex ω) (κ ⊕ TopGradedBasisIndex s ω) ℚ :=
  fun i j => (F.layerOneBasis e ω hF).repr (F.fullFastHorizontalGenerators e ω hF v j) i

theorem fullFastHorizontalMatrix_height
    (v : κ → F.squareFiltration.quotientTop.AssociatedGraded) {H : ℕ} (hH : 1 ≤ H)
    (hv : ∀ j i, RationalHeightLE ((bW).repr (v j) i) H) :
    ∀ i j, RationalHeightLE (F.fullFastHorizontalMatrix e ω hF v i j) H := by
  intro i j
  exact F.fullFastHorizontalGenerators_height e ω hF v hH hv j i

theorem fullFastHorizontalMatrix_span [Fintype ι]
    (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded)
    (hW : BasisGradedSubmodule bW ωW W.toSubmodule)
    (v : κ → F.squareFiltration.quotientTop.AssociatedGraded)
    (hv : Submodule.span ℚ (Set.range v) = W.toSubmodule) :
    Submodule.span ℝ (Set.range ((F.fullFastHorizontalMatrix e ω hF v).map (Rat.castHom ℝ)).col) =
      F.fullFastHorizontalCoordinates e ω hF W := by
  have hspan : Submodule.span ℝ (Set.range (fun j => (1 : ℝ) ⊗ₜ[ℚ]
      F.fullFastHorizontalGenerators e ω hF v j)) =
      (F.layerOneGradedSubmodule e ω hF (F.fullFastGradedDiagonal W)).baseChange ℝ := by
    rw [← F.fullFastHorizontalGenerators_span e ω hF W hW v hv,
      Submodule.baseChange_span, ← Set.range_comp]
    rfl
  rw [fullFastHorizontalCoordinates, ← hspan, Submodule.map_span, ← Set.range_comp]
  congr 1
  apply congrArg Set.range
  funext j i
  change ((F.layerOneBasis e ω hF).repr (F.fullFastHorizontalGenerators e ω hF v j) i : ℝ) =
    ((F.layerOneBasis e ω hF).baseChange ℝ).repr
      ((1 : ℝ) ⊗ₜ[ℚ] F.fullFastHorizontalGenerators e ω hF v j) i
  rw [Basis.baseChange_repr_tmul]
  simp only [Rat.smul_def, mul_one]

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.FastCoefficientDerivativeCoordinates
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module
open scoped Matrix

variable {σ κ L : Type*} [Fintype σ] [Fintype κ] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1))
  (U : LieSubalgebra ℚ (F.squareFiltration.quotientTop.PolynomialSymbol (fun _ : σ => 1)))
  (b : Basis κ ℝ (F.RealFirstCoefficientModule (fun _ : σ => 1) ⧸
    F.realFirstCoefficientFastSubmodule (fun _ => 1) (by simp)
      (F.reducedSquareFastRelativeSubmodule (fun _ => 1) U)))

omit [Fintype σ] in
theorem fastCoefficientAdjoint_coordinates [DecidableEq κ]
    (B : F.RealAdaptedPolynomialGroup (fun _ : σ => 1))
    (hB : (F.adaptedReducedRealSymbolHom (fun _ => 1) B).coord ∈
      realificationLieSubalgebra (F.reducedSquareFastDiagonalSubalgebra (fun _ => 1) U))
    (x : F.RealFirstCoefficientModule (fun _ : σ => 1)) :
    b.equivFun ((F.realFirstCoefficientFastSubmodule (fun _ => 1) (by simp)
      (F.reducedSquareFastRelativeSubmodule (fun _ => 1) U)).mkQ
        (F.realFirstCoefficientAdjoint (fun _ => 1) B x)) =
      LinearMap.toMatrix b b (F.realFastCoefficientAdjoint (fun _ => 1) (by simp) U B hB).toLinearMap *ᵥ
        b.equivFun ((F.realFirstCoefficientFastSubmodule (fun _ => 1) (by simp)
          (F.reducedSquareFastRelativeSubmodule (fun _ => 1) U)).mkQ x) := by
  have h := LinearMap.toMatrix_mulVec_repr b b
    (F.realFastCoefficientAdjoint (fun _ => 1) (by simp) U B hB).toLinearMap
    ((F.realFirstCoefficientFastSubmodule (fun _ => 1) (by simp)
      (F.reducedSquareFastRelativeSubmodule (fun _ => 1) U)).mkQ x)
  exact (congrArg b.equivFun (F.realFastCoefficientAdjoint_mk (fun _ => 1) (by simp) U B hB x)).symm.trans
    h.symm

theorem fastCoefficientDerivative_coordinates [DecidableEq κ]
    (B : F.RealAdaptedPolynomialGroup (fun _ : σ => 1))
    (hB : (F.adaptedReducedRealSymbolHom (fun _ => 1) B).coord ∈
      realificationLieSubalgebra (F.reducedSquareFastDiagonalSubalgebra (fun _ => 1) U))
    (h : σ → ℝ) (S R : F.RealFirstCoefficientModule (fun _ : σ => 1))
    (heq : F.realFirstCoefficientDirectionMap B.coord h -
      (S + F.realFirstCoefficientAdjoint (fun _ => 1) B R) ∈
        F.realFirstCoefficientFastSubmodule (fun _ => 1) (by simp)
          (F.reducedSquareFastRelativeSubmodule (fun _ => 1) U)) :
    F.fastCoefficientDirectionCoordinates U b B h =
      b.equivFun ((F.realFirstCoefficientFastSubmodule (fun _ => 1) (by simp)
        (F.reducedSquareFastRelativeSubmodule (fun _ => 1) U)).mkQ S) +
      LinearMap.toMatrix b b (F.realFastCoefficientAdjoint (fun _ => 1) (by simp) U B hB).toLinearMap *ᵥ
        b.equivFun ((F.realFirstCoefficientFastSubmodule (fun _ => 1) (by simp)
          (F.reducedSquareFastRelativeSubmodule (fun _ => 1) U)).mkQ R) := by
  have hq := (Submodule.Quotient.eq
    (F.realFirstCoefficientFastSubmodule (fun _ => 1) (by simp)
      (F.reducedSquareFastRelativeSubmodule (fun _ => 1) U))).mpr heq
  let q := (F.realFirstCoefficientFastSubmodule (fun _ => 1) (by simp)
    (F.reducedSquareFastRelativeSubmodule (fun _ => 1) U)).mkQ
  have hadd := (b.equivFun.toLinearMap.comp q).map_add S (F.realFirstCoefficientAdjoint (fun _ => 1) B R)
  have hadj := F.fastCoefficientAdjoint_coordinates U b B hB R
  exact (congrArg b.equivFun hq).trans (hadd.trans (congrArg₂ (· + ·) rfl hadj))

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ReindexedFastCoefficientSection
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module
open scoped TensorProduct

variable {σ ι L : Type*} [Fintype ι]
  [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i})) (w : σ → ℕ)

omit [Fintype ι] in
theorem realHorizontalSection_constant_coordinate
    (x : ℝ ⊗[ℚ] (L ⧸ F.layer 2)) (z : FirstCoefficientIndex w ω) (hz : z.val.1 = 0) :
    (F.realFirstCoefficientBasis e ω hF w).repr (F.realFirstCoefficientHorizontalSection w x) z =
      ((F.layerOneBasis e ω hF).baseChange ℝ).repr x (layerOneIndexOfConstant ω w z hz) := by
  have h := F.realFirstCoefficientHorizontal_coordinates e ω hF w
    (F.realFirstCoefficientHorizontalSection w x) (layerOneIndexOfConstant ω w z hz)
  rw [F.realFirstCoefficientHorizontal_section, F.horizontalCoefficientIndex_of_constant] at h
  exact h.symm

omit [Fintype ι] in
theorem realHorizontalSection_nonconstant_coordinate
    (x : ℝ ⊗[ℚ] (L ⧸ F.layer 2)) (z : FirstCoefficientIndex w ω) (hz : z.val.1 ≠ 0) :
    (F.realFirstCoefficientBasis e ω hF w).repr (F.realFirstCoefficientHorizontalSection w x) z = 0 := by
  classical
  have h := F.realFirstCoefficientHorizontal_projector_repr e ω hF w
    (F.realFirstCoefficientHorizontalSection w x) z
  simpa only [F.realFirstCoefficientHorizontal_section, hz, ite_false] using h

theorem realHorizontalSection_slow_bound (T : σ → ℝ) (hT : ∀ i, 0 < T i)
    (x : ℝ ⊗[ℚ] (L ⧸ F.layer 2)) {M : ℝ} (hM : 0 ≤ M)
    (hx : ‖((F.layerOneBasis e ω hF).baseChange ℝ).equivFun x‖ ≤ M) :
    F.FirstCoefficientSlowBound e ω hF w T M (F.realFirstCoefficientHorizontalSection w x) := by
  classical
  intro z
  by_cases hz : z.val.1 = 0
  · rw [F.realHorizontalSection_constant_coordinate e ω hF w x z hz,
      hz, monomialScale_zero, div_one]
    exact (norm_le_pi_norm (((F.layerOneBasis e ω hF).baseChange ℝ).equivFun x)
      (layerOneIndexOfConstant ω w z hz)).trans hx
  · rw [F.realHorizontalSection_nonconstant_coordinate e ω hF w x z hz, abs_zero]
    exact div_nonneg hM (monomialScale_pos T hT _).le

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.ControlledLayerOneCoordinates
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module
open scoped TensorProduct

variable {σ ι L : Type*} [Fintype ι]
  [LieRing L] [LieAlgebra ℚ L] {s a d : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
  (w : σ → ℕ) (hw : ∀ i, 0 < w i)
  (U : Submodule ℚ (F.squareFiltration.quotientTop.PolynomialSymbol w))
  (b : Basis (Fin d) ℝ (F.RealFirstCoefficientModule w ⧸
    F.realFirstCoefficientFastSubmodule w hw U))
  (ha : a ≤ d) (η : (Fin a → ℝ) ≃ₗ[ℝ] (ℝ ⊗[ℚ] (L ⧸ F.layer 2)))
  (hη : ∀ x, η (fun i => b.equivFun x (Fin.castLE ha i)) = F.realFastCoefficientHorizontal w hw U x)

include hη

theorem layerOne_equiv_grid (l m : ℕ)
    (R : (Fin d → ℝ) →ₗ[ℝ] F.RealFirstCoefficientModule w)
    (hR : ∀ y, (F.realFirstCoefficientFastSubmodule w hw U).mkQ (R y) = b.equivFun.symm y)
    (hgrid : ∀ y, y ∈ realDenominatorGrid l → F.FirstCoefficientGrid e ω hF w m (R y))
    (x : Fin a → ℝ) (hx : x ∈ realDenominatorGrid l) :
    ((F.layerOneBasis e ω hF).baseChange ℝ).equivFun (η x) ∈ realDenominatorGrid m := by
  rw [F.layerOne_equiv_representative w hw U b ha η hη R hR x]
  exact F.realFirstCoefficientHorizontal_grid e ω hF w m _
    (hgrid _ (extendInitialCoordinates_grid l x hx))

theorem layerOne_equiv_norm (C : ℝ) (hC : 0 ≤ C)
    (R : (Fin d → ℝ) →ₗ[ℝ] F.RealFirstCoefficientModule w)
    (hR : ∀ y, (F.realFirstCoefficientFastSubmodule w hw U).mkQ (R y) = b.equivFun.symm y)
    (hbound : ∀ (y : Fin d → ℝ) (M : ℝ), 0 ≤ M → (∀ j, |y j| ≤ M) →
      F.FirstCoefficientSlowBound e ω hF w (fun _ => 1) (C * M) (R y))
    (x : Fin a → ℝ) :
    ‖((F.layerOneBasis e ω hF).baseChange ℝ).equivFun (η x)‖ ≤ C * ‖x‖ := by
  rw [F.layerOne_equiv_representative w hw U b ha η hη R hR x]
  apply F.realFirstCoefficientHorizontal_bound e ω hF w (fun _ => 1)
    (mul_nonneg hC (norm_nonneg _))
  apply hbound _ ‖x‖ (norm_nonneg x)
  intro j
  exact (norm_le_pi_norm (extendInitialCoordinates x : Fin d → ℝ) j).trans
    (norm_extendInitialCoordinates_le x)

theorem layerOne_equiv_symm_norm (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ (x : F.RealFirstCoefficientModule w) (M : ℝ), 0 ≤ M →
      F.FirstCoefficientSlowBound e ω hF w (fun _ => 1) M x → ∀ j,
        |b.equivFun ((F.realFirstCoefficientFastSubmodule w hw U).mkQ x) j| ≤ C * M)
    (x : ℝ ⊗[ℚ] (L ⧸ F.layer 2)) :
    ‖η.symm x‖ ≤ C * ‖((F.layerOneBasis e ω hF).baseChange ℝ).equivFun x‖ := by
  rw [F.layerOne_equiv_symm_coordinates w hw U b ha η hη x]
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg hC (norm_nonneg _))).mpr
  intro i
  exact hbound _ _ (norm_nonneg _) (F.realHorizontalSection_slow_bound e ω hF w
    (fun _ => 1) (by intro i; norm_num) x (norm_nonneg _) le_rfl) (Fin.castLE ha i)

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.LayerOneProjectionMatrixBounds
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module
open scoped TensorProduct Matrix

variable {σ ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] {s a d : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
  (w : σ → ℕ) (hw : ∀ i, 0 < w i)
  (U : Submodule ℚ (F.squareFiltration.quotientTop.PolynomialSymbol w))
  (b : Basis (Fin d) ℝ (F.RealFirstCoefficientModule w ⧸
    F.realFirstCoefficientFastSubmodule w hw U))
  (ha : a ≤ d) (η : (Fin a → ℝ) ≃ₗ[ℝ] (ℝ ⊗[ℚ] (L ⧸ F.layer 2)))
  (hη : ∀ x, η (fun i => b.equivFun x (Fin.castLE ha i)) = F.realFastCoefficientHorizontal w hw U x)
  (R : (Fin d → ℝ) →ₗ[ℝ] F.RealFirstCoefficientModule w)
  (hR : ∀ y, (F.realFirstCoefficientFastSubmodule w hw U).mkQ (R y) = b.equivFun.symm y)
  (l m : ℕ) (hm : 0 < m) (C : ℝ) (hC : 0 ≤ C)
  (hgrid : ∀ y, y ∈ realDenominatorGrid l → F.FirstCoefficientGrid e ω hF w m (R y))
  (hbound : ∀ (y : Fin d → ℝ) (M : ℝ), 0 ≤ M → (∀ j, |y j| ≤ M) →
    F.FirstCoefficientSlowBound e ω hF w (fun _ => 1) (C * M) (R y))

include hη hR hm hC hgrid hbound

theorem layerOne_equiv_rational_matrix :
    ∃ A : Matrix (LayerOneBasisIndex ω) (Fin a) ℚ,
      (∀ i j, RationalHeightLE (A i j) (max m (Nat.ceil ((m : ℝ) * C)))) ∧
      ∀ x, ((F.layerOneBasis e ω hF).baseChange ℝ).equivFun (η x) =
        A.map (Rat.castHom ℝ) *ᵥ x := by
  exact exists_bounded_rational_map_matrix
    (((F.layerOneBasis e ω hF).baseChange ℝ).equivFun.toLinearMap.comp η.toLinearMap)
    m hm (fun j => F.layerOne_equiv_grid e ω hF w hw U b ha η hη l m R hR hgrid
      (Pi.single j 1) (realDenominatorGrid_single l j)) C
    (F.layerOne_equiv_norm e ω hF w hw U b ha η hη C hC R hR hbound)

theorem layerOne_rational_kernel_basis {ν : Type*}
    (K : Submodule ℝ (Fin a → ℝ)) (Q : Matrix (Fin a) ν ℚ)
    (hK : K = Submodule.span ℝ (Set.range (Q.map (Rat.castHom ℝ)).col))
    (hQ : LinearIndependent ℝ (Q.map (Rat.castHom ℝ)).col)
    {J : ℕ} (hQJ : ∀ i j, RationalHeightLE (Q i j) J) :
    ∃ v : ν → L ⧸ F.layer 2,
      (∀ j, (1 : ℝ) ⊗ₜ[ℚ] v j = η ((Q.map (Rat.castHom ℝ)).col j)) ∧
      K.map η.toLinearMap = (Submodule.span ℚ (Set.range v)).baseChange ℝ ∧
      LinearIndependent ℚ v ∧
      ∀ i j, RationalHeightLE ((F.layerOneBasis e ω hF).repr (v j) i)
        ((a + 1) * (max m (Nat.ceil ((m : ℝ) * C)) * J) ^ a) := by
  obtain ⟨A, hA, heq⟩ := F.layerOne_equiv_rational_matrix e ω hF w hw U b ha η hη
    R hR l m hm C hC hgrid hbound
  simpa only [Fintype.card_fin] using rational_horizontal_basis_transport
    (F.layerOneBasis e ω hF) η A heq K Q hK hQ hA hQJ

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.NativeCoordinateDerivativeSystem
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module
open scoped TensorProduct

variable {σ ι L : Type*} [Fintype σ] [DecidableEq σ] [Fintype ι]
  [LieRing L] [LieAlgebra ℚ L] {s a d : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
  (U : LieSubalgebra ℚ (F.squareFiltration.quotientTop.PolynomialSymbol (fun _ : σ => 1)))

local notation "Uf" => F.reducedSquareFastRelativeSubmodule (fun _ : σ => 1) U
local notation "J" => F.realFirstCoefficientFastSubmodule (fun _ : σ => 1) (fun _ => Nat.zero_lt_one) Uf
local notation "E" => F.RealFirstCoefficientModule (fun _ : σ => 1)
local notation "Q" => (E ⧸ J)
local notation "Hq" => F.realFastCoefficientHorizontal (fun _ : σ => 1) (fun _ => Nat.zero_lt_one) Uf
local notation "cH" => Basis.equivFun (Basis.baseChange ℝ (F.layerOneBasis e ω hF))
local notation "ρ" => F.realFastCoefficientAction (fun _ : σ => 1) (fun _ => Nat.zero_lt_one) U

def NativeCoordinateDerivativeSpec : Prop :=
  ∀ (b : Basis (Fin d) ℝ Q) (rows : Fin d → FirstCoefficientIndex (fun _ : σ => 1) ω)
    (ha : a ≤ d) (η : (Fin a → ℝ) ≃ₗ[ℝ] (ℝ ⊗[ℚ] (L ⧸ F.layer 2)))
    (_hη : ∀ x, η (fun i => b.equivFun x (Fin.castLE ha i)) = Hq x)
    (sectionMap : (Fin d → ℝ) →ₗ[ℝ] E)
    (_hsection : ∀ y, (J).mkQ (sectionMap y) = b.equivFun.symm y)
    (Cscale : ℝ) (_hC : 0 ≤ Cscale)
    (_hweighted : ∀ (T : σ → ℝ), (∀ i, 0 < T i) → ∀ M : ℝ, 0 ≤ M →
      (∀ x, F.FirstCoefficientSlowBound e ω hF (fun _ : σ => 1) T M x → ∀ i,
        |b.equivFun ((J).mkQ x) i| ≤ Cscale * M / monomialScale T (rows i).val.1) ∧
      (∀ y, (∀ i, |y i| ≤ M / monomialScale T (rows i).val.1) →
        F.FirstCoefficientSlowBound e ω hF (fun _ : σ => 1) T (Cscale * M) (sectionMap y)))
    (m : ℕ) (_hm : 0 < m)
    (_hgrid : ∀ y, y ∈ realDenominatorGrid 1 → F.FirstCoefficientGrid e ω hF (fun _ : σ => 1) m (sectionMap y))
    (T : σ → ℝ) (_hT : ∀ i, 0 < T i)
    (g : F.realFastDiagonalSubgroup (fun _ : σ => 1) U)
    (bound : ℝ) (_hbound : 0 ≤ bound)
    (D : CoordinateDerivativeSystem ha T (b.equivFun.toLinearMap.comp (F.realFastCoefficientDirectionMap U g.val))
      (b.equivFun.symm.trans ((ρ g).trans b.equivFun))
      (fun i => monomialScale T (rows i).val.1) bound)
    (p : ℝ) (_hp : 0 ≤ p) (_hap : (a : ℝ) ≤ p) (_hmp : (m : ℝ) ≤ Real.exp p)
    (_hCp : Cscale ≤ Real.exp p) (_hDp : (D.heightBound : ℝ) ≤ Real.exp p),
    D.k ≤ a ∧ ∃ (K : Submodule ℚ (L ⧸ F.layer 2)) (bK : Basis (Fin D.k) ℚ K),
      ∃ H : ℕ, 1 ≤ H ∧ (H : ℝ) ≤ Real.exp ((p + 2) ^ 3) ∧
        (∀ i j, RationalHeightLE ((F.layerOneBasis e ω hF).repr (bK j : L ⧸ F.layer 2) i) H) ∧
        ∃ l : ℕ, 0 < l ∧ (l : ℝ) ≤ bound ^ 2 ∧
          ∃ S R : (K.baseChange ℝ) →ₗ[ℝ] Q,
            S = (ρ g).toLinearMap.comp R ∧ (Hq).comp S = (K.baseChange ℝ).subtype ∧
            (Hq).comp R = (K.baseChange ℝ).subtype ∧
            (∀ x, ‖basisWeightedCoordinates b (fun i => monomialScale T (rows i).val.1) (S x)‖ ≤
              (bound * Cscale) * ‖cH x.val‖) ∧
            (∀ j, b.equivFun (R (realSubmoduleBasis K bK j)) ∈ realDenominatorGrid l) ∧
            ∃ (small rational : σ → Q) (k : σ → K.baseChange ℝ),
              (∀ i, F.realFastCoefficientDirectionMap U g.val (Pi.single i 1) =
                small i + ρ g (rational i) + S (k i)) ∧
              (∀ i, b.equivFun (rational i) ∈ realDenominatorGrid l) ∧
              (∀ i, ‖basisWeightedCoordinates b (fun j => monomialScale T (rows j).val.1) (small i)‖ ≤
                bound / T i) ∧
              (∀ i, ‖cH (Hq (small i))‖ ≤ (Cscale * bound) / T i)

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

local notation "φ" => F.realFirstCoefficientGradedPolynomial e ω hF (fun _ : σ => 1)

theorem realFirstCoefficientGradedPolynomial_basisLift {K : Type*}
    [AddCommGroup K] [Module ℝ K] (b : Basis κ ℝ K)
    (S : K →ₗ[ℝ] F.RealFirstCoefficientModule (fun _ : σ => 1)) (x : K) :
    φ (S x) = basisPolynomialLift b (fun z => φ (S (b z))) x := by
  have he : (φ).comp S = basisPolynomialLift b (fun z => φ (S (b z))) := by
    apply b.ext
    intro z
    simp only [LinearMap.comp_apply, basisPolynomialLift_basis]
  exact LinearMap.congr_fun he x

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

def ControlledInitialRemovalSpec (s aExp C : ℕ) : Prop :=
    ∀ {σ ι κ ν L : Type*} [Fintype σ] [DecidableEq σ] [Fintype ι]
      [Fintype κ] [Fintype ν] [LieRing L] [LieAlgebra ℚ L]
      (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
      (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
      (H : ℕ) (p : ℝ), 1 ≤ H → 0 ≤ p →
      (Fintype.card ι : ℝ) ≤ p → (Fintype.card σ : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p →
      (∀ i j k, RationalHeightLE (e.repr ⁅e i, e j⁆ k) H) →
      ∀ W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded,
      let Wf := F.fastPointwiseSquare e ω hF (fun _ : σ => 1) W
      let E := F.RealFirstCoefficientModule (fun _ : σ => 1)
      let J := F.realFirstCoefficientFastSubmodule (fun _ : σ => 1) (fun _ => Nat.zero_lt_one)
        (F.reducedSquareFastRelativeSubmodule (fun _ : σ => 1) Wf)
      let Q := E ⧸ J
      let G := F.realFastDiagonalSubgroup (fun _ : σ => 1) Wf
      let ρ := F.realFastCoefficientAction (fun _ : σ => 1) (fun _ => Nat.zero_lt_one) Wf
      let Hq := F.realFastCoefficientHorizontal (fun _ : σ => 1) (fun _ => Nat.zero_lt_one)
        (F.reducedSquareFastRelativeSubmodule (fun _ : σ => 1) Wf)
      let Y := fun (g : G) i => F.realFastCoefficientDirectionMap Wf g.val (Pi.single i 1)
      BasisGradedSubmodule
        (F.squareFiltration.quotientTop.associatedGradedBasis (F.reducedSquareBasis e ω hF)
          (fun a : ReducedSquareBasisIndex s ω => squareBasisWeight ω a.val)
          (F.reducedSquareBasis_layers e ω hF))
        (fun a : ReducedSquareBasisIndex s ω => squareBasisWeight ω a.val) W.toSubmodule →
      ∀ (a g c : G) (K : Submodule ℚ (L ⧸ F.layer 2)) (bK : Basis κ ℚ K)
        (b : Basis ν ℝ Q) (rows : ν → FirstCoefficientIndex (fun _ : σ => 1) ω)
        (sectionMap : (ν → ℝ) →ₗ[ℝ] E),
      (∀ y, J.mkQ (sectionMap y) = b.equivFun.symm y) →
      ∀ (T : σ → ℝ), (∀ i, 0 < T i) → ∀ Kscale : ℝ, 0 ≤ Kscale → Kscale ≤ Real.exp p →
      (∀ M, 0 ≤ M → ∀ x, F.FirstCoefficientSlowBound e ω hF (fun _ : σ => 1) T M x →
        ∀ i, |b.equivFun (J.mkQ x) i| ≤ Kscale * M / monomialScale T (rows i).val.1) →
      (∀ M, 0 ≤ M → ∀ y : ν → ℝ, (∀ i, |y i| ≤ M / monomialScale T (rows i).val.1) →
        F.FirstCoefficientSlowBound e ω hF (fun _ : σ => 1) T (Kscale * M) (sectionMap y)) →
      ∀ l δ : ℕ, 0 < l → 0 < δ → ((δ * l : ℕ) : ℝ) ≤ Real.exp p →
      (∀ m x, F.FirstCoefficientGrid e ω hF (fun _ : σ => 1) m x →
        b.equivFun (J.mkQ x) ∈ realDenominatorGrid (δ * m)) →
      (∀ m (y : ν → ℝ), y ∈ realDenominatorGrid m →
        F.FirstCoefficientGrid e ω hF (fun _ : σ => 1) (δ * m) (sectionMap y)) →
      F.RealAdaptedCoefficientBound e ω hF (fun _ : σ => 1) T
        (Real.exp ((p + 2) ^ aExp)) a.val.coord →
      F.RealAdaptedCoefficientGrid e ω hF (fun _ : σ => 1) (δ * l) c.val.coord →
      ∀ (S R : (K.baseChange ℝ) →ₗ[ℝ] Q) (small rational : σ → Q) (k : σ → K.baseChange ℝ),
      S = (ρ (a * g * c)).toLinearMap.comp R →
      (∀ i, Y (a * g * c) i = small i + ρ (a * g * c) (rational i) + S (k i)) →
      Hq.comp S = (K.baseChange ℝ).subtype → Hq.comp R = (K.baseChange ℝ).subtype →
      (∀ i, Hq (Y a i) = Hq (small i)) → (∀ i, Hq (Y c i) = Hq (rational i)) →
      (∀ i, (F.layer 2).mkQ.baseChange ℝ
        (coefficients (F.realAdaptedPolynomialMap (fun _ : σ => 1) g.val.coord) (Finsupp.single i 1)) =
          (k i).val) →
      (∀ i, ‖basisWeightedCoordinates b (fun j => monomialScale T (rows j).val.1) (small i)‖ ≤
        Real.exp p / T i) →
      (∀ z, ‖basisWeightedCoordinates b (fun i => monomialScale T (rows i).val.1)
        (S (realSubmoduleBasis K bK z))‖ ≤ Real.exp p) →
      (∀ z, b.equivFun (R (realSubmoduleBasis K bK z)) ∈ realDenominatorGrid l) →
      (∀ i, b.equivFun (rational i) ∈ realDenominatorGrid l) →
      ∃ X : F.associatedGradedFiltration.FormalInductionState (F.associatedGradedBasis e ω hF) ω
        (realificationLieSubalgebra (F.fullFastGradedDiagonal W))
        (F.fullFastGradedRelative e ω hF W) (F.gradedHorizontalKernel e ω hF K)
        (F.gradedHorizontalKernelBasis e ω hF K bK) T 2 ((p + C) ^ C),
        X.P = F.realAdaptedGradedPolynomialHom e ω hF (fun _ : σ => 1) g.val

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

universe uσ uι uκ uν uL

variable {σ : Type uσ} {ι : Type uι} {κ : Type uκ} {ν : Type uν} {L : Type uL}
  [Fintype σ] [DecidableEq σ] [Fintype ι]
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
local notation "G" => F.realFastDiagonalSubgroup (fun _ : σ => 1) Wf
local notation "ρ" => F.realFastCoefficientAction (fun _ : σ => 1) (fun _ => Nat.zero_lt_one) Wf
local notation "Hq" => F.realFastCoefficientHorizontal (fun _ : σ => 1) (fun _ => Nat.zero_lt_one) Uf
local notation "Y" => (fun (g : G) i => F.realFastCoefficientDirectionMap Wf (Subtype.val g) (Pi.single i 1))
local notation "UH" => Submodule.baseChange ℝ (F.layerOneGradedSubmodule e ω hF (F.fullFastGradedDiagonal W))

def HorizontalInitialStateSpec (aExp C : ℕ) : Prop :=
  ∀ (H : ℕ) (p : ℝ) (_hH : 1 ≤ H) (_hp : 0 ≤ p)
    (_hι : (Fintype.card ι : ℝ) ≤ p) (_hσ : (Fintype.card σ : ℝ) ≤ p)
    (_hHp : (H : ℝ) ≤ Real.exp p)
    (_hstructure : ∀ i j k, RationalHeightLE (e.repr ⁅e i, e j⁆ k) H)
    (_hW : BasisGradedSubmodule bW ωW W.toSubmodule)
    (g₀ : G) (_hzero : coefficients (F.realAdaptedPolynomialMap (fun _ : σ => 1) g₀.val.coord) 0 = 0)
    (K : Submodule ℚ (L ⧸ F.layer 2)) (bK : Basis κ ℚ K)
    (b : Basis ν ℝ Q) (rows : ν → FirstCoefficientIndex (fun _ : σ => 1) ω)
    (sectionMap : (ν → ℝ) →ₗ[ℝ] E)
    (_hsection : ∀ y, (J).mkQ (sectionMap y) = b.equivFun.symm y)
    (T : σ → ℝ) (_hT : ∀ i, 0 < T i)
    (Kscale : ℝ) (_hKscale : 0 ≤ Kscale) (_hKscalep : Kscale ≤ Real.exp p)
    (_hprojection : ∀ M, 0 ≤ M → ∀ x, F.FirstCoefficientSlowBound e ω hF (fun _ : σ => 1) T M x →
      ∀ i, |b.equivFun ((J).mkQ x) i| ≤ Kscale * M / monomialScale T (rows i).val.1)
    (_hsectionBound : ∀ M, 0 ≤ M → ∀ y : ν → ℝ,
      (∀ i, |y i| ≤ M / monomialScale T (rows i).val.1) →
        F.FirstCoefficientSlowBound e ω hF (fun _ : σ => 1) T (Kscale * M) (sectionMap y))
    (l δ : ℕ) (_hl : 0 < l) (_hδ : 0 < δ) (_hδlp : ((δ * l : ℕ) : ℝ) ≤ Real.exp p)
    (_hprojectionGrid : ∀ m x, F.FirstCoefficientGrid e ω hF (fun _ : σ => 1) m x →
      b.equivFun ((J).mkQ x) ∈ realDenominatorGrid (δ * m))
    (_hsectionGrid : ∀ m (y : ν → ℝ), y ∈ realDenominatorGrid m →
      F.FirstCoefficientGrid e ω hF (fun _ : σ => 1) (δ * m) (sectionMap y))
    (S R : (K.baseChange ℝ) →ₗ[ℝ] Q) (small rational : σ → Q) (k : σ → K.baseChange ℝ)
    (_hSR : S = (ρ g₀).toLinearMap.comp R)
    (_hsystem : ∀ i, Y g₀ i = small i + ρ g₀ (rational i) + S (k i))
    (_hS : (Hq).comp S = (K.baseChange ℝ).subtype)
    (_hR : (Hq).comp R = (K.baseChange ℝ).subtype)
    (_hsmallH : ∀ i, Hq (small i) ∈ UH) (_hrationalH : ∀ i, Hq (rational i) ∈ UH)
    (_hkH : ∀ i, (k i).val ∈ UH)
    (_hsmall : ∀ i, ‖basisWeightedCoordinates b (fun j => monomialScale T (rows j).val.1) (small i)‖ ≤
      Real.exp p / T i)
    (_hSbound : ∀ z, ‖basisWeightedCoordinates b (fun i => monomialScale T (rows i).val.1)
      (S (realSubmoduleBasis K bK z))‖ ≤ Real.exp p)
    (_hRgrid : ∀ z, b.equivFun (R (realSubmoduleBasis K bK z)) ∈ realDenominatorGrid l)
    (_hrational : ∀ i, b.equivFun (rational i) ∈ realDenominatorGrid l),
    ∃ a g c : G, a * g * c = g₀ ∧
      F.RealAdaptedCoefficientBound e ω hF (fun _ : σ => 1) T (Real.exp ((p + 2) ^ aExp)) a.val.coord ∧
      F.RealAdaptedCoefficientGrid e ω hF (fun _ : σ => 1) (δ * l) c.val.coord ∧
      ∃ X : F.associatedGradedFiltration.FormalInductionState (F.associatedGradedBasis e ω hF) ω
        (realificationLieSubalgebra (F.fullFastGradedDiagonal W))
        (F.fullFastGradedRelative e ω hF W) (F.gradedHorizontalKernel e ω hF K)
        (F.gradedHorizontalKernelBasis e ω hF K bK) T 2 ((p + C) ^ C),
        X.P = F.realAdaptedGradedPolynomialHom e ω hF (fun _ : σ => 1) g.val

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

universe uσ uι uκ uν uτ uL

variable {σ : Type uσ} {ι : Type uι} {κ : Type uκ} {ν : Type uν} {τ : Type uτ} {L : Type uL}
  [Fintype σ] [DecidableEq σ] [Fintype ι] [Fintype κ] [Fintype ν] [Fintype τ]
  [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
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
local notation "G" => F.realFastDiagonalSubgroup (fun _ : σ => 1) Wf
local notation "ρ" => F.realFastCoefficientAction (fun _ : σ => 1) (fun _ => Nat.zero_lt_one) Wf
local notation "Hq" => F.realFastCoefficientHorizontal (fun _ : σ => 1) (fun _ => Nat.zero_lt_one) Uf
local notation "Y" => (fun (g : G) i => F.realFastCoefficientDirectionMap Wf (Subtype.val g) (Pi.single i 1))
local notation "cH" => Basis.equivFun (Basis.baseChange ℝ (F.layerOneBasis e ω hF))

def AbsorbedInitialStateSpec (C : ℕ) : Prop :=
  ∀ (H : ℕ) (p : ℝ) (_hH : 1 ≤ H) (_hp : 0 ≤ p)
    (_hι : (Fintype.card ι : ℝ) ≤ p) (_hσ : (Fintype.card σ : ℝ) ≤ p)
    (_hHp : (H : ℝ) ≤ Real.exp p)
    (_hstructure : ∀ i j k, RationalHeightLE (e.repr ⁅e i, e j⁆ k) H)
    (_hW : BasisGradedSubmodule bW ωW W.toSubmodule)
    (v : τ → F.squareFiltration.quotientTop.AssociatedGraded)
    (_hv : Submodule.span ℚ (Set.range v) = W.toSubmodule)
    (_hheight : ∀ j i, RationalHeightLE ((bW).repr (v j) i) H)
    (_hsize : ((Fintype.card τ + Fintype.card ι + Fintype.card κ : ℕ) : ℝ) ≤ p)
    (g₀ : G) (_hzero : coefficients (F.realAdaptedPolynomialMap (fun _ : σ => 1) g₀.val.coord) 0 = 0)
    (K : Submodule ℚ (L ⧸ F.layer 2)) (bK : Basis κ ℚ K)
    (_hKb : ∀ i j, RationalHeightLE ((F.layerOneBasis e ω hF).repr (bK j).val i) H)
    (b : Basis ν ℝ Q) (rows : ν → FirstCoefficientIndex (fun _ : σ => 1) ω)
    (sectionMap : (ν → ℝ) →ₗ[ℝ] E)
    (_hsection : ∀ y, (J).mkQ (sectionMap y) = b.equivFun.symm y)
    (T : σ → ℝ) (_hT : ∀ i, Real.exp (separationBudget p) ≤ T i)
    (Kscale : ℝ) (_hKscale : 0 ≤ Kscale) (_hKscalep : Kscale ≤ Real.exp p)
    (_hprojection : ∀ M, 0 ≤ M → ∀ x, F.FirstCoefficientSlowBound e ω hF (fun _ : σ => 1) T M x →
      ∀ i, |b.equivFun ((J).mkQ x) i| ≤ Kscale * M / monomialScale T (rows i).val.1)
    (_hsectionBound : ∀ M, 0 ≤ M → ∀ y : ν → ℝ,
      (∀ i, |y i| ≤ M / monomialScale T (rows i).val.1) →
        F.FirstCoefficientSlowBound e ω hF (fun _ : σ => 1) T (Kscale * M) (sectionMap y))
    (l δ : ℕ) (_hl : 0 < l) (_hδ : 0 < δ) (_hδlp : ((δ * l : ℕ) : ℝ) ≤ Real.exp p)
    (_hprojectionGrid : ∀ m x, F.FirstCoefficientGrid e ω hF (fun _ : σ => 1) m x →
      b.equivFun ((J).mkQ x) ∈ realDenominatorGrid (δ * m))
    (_hsectionGrid : ∀ m (y : ν → ℝ), y ∈ realDenominatorGrid m →
      F.FirstCoefficientGrid e ω hF (fun _ : σ => 1) (δ * m) (sectionMap y))
    (S R : (K.baseChange ℝ) →ₗ[ℝ] Q) (small rational : σ → Q) (k : σ → K.baseChange ℝ)
    (_hSR : S = (ρ g₀).toLinearMap.comp R)
    (_hsystem : ∀ i, Y g₀ i = small i + ρ g₀ (rational i) + S (k i))
    (_hS : (Hq).comp S = (K.baseChange ℝ).subtype)
    (_hR : (Hq).comp R = (K.baseChange ℝ).subtype)
    (_hsmallH : ∀ i, ‖cH (Hq (small i))‖ ≤ Real.exp p / T i)
    (_hsmall : ∀ i, ‖basisWeightedCoordinates b (fun j => monomialScale T (rows j).val.1) (small i)‖ ≤
      Real.exp p / T i)
    (_hSbound : ∀ x, ‖basisWeightedCoordinates b (fun i => monomialScale T (rows i).val.1) (S x)‖ ≤
      Real.exp p * ‖cH x.val‖)
    (_hRgrid : ∀ z, b.equivFun (R (realSubmoduleBasis K bK z)) ∈ realDenominatorGrid l)
    (_hrational : ∀ i, b.equivFun (rational i) ∈ realDenominatorGrid l),
    ∃ d : ℕ, 0 < d ∧ (d : ℝ) ≤ Real.exp (absorbedInitialParameter p) ∧
      ∃ a g c : G, a * g * c = g₀ ∧
        F.RealAdaptedCoefficientBound e ω hF (fun _ : σ => 1) T
          (Real.exp ((absorbedInitialParameter p + 2) ^ 2)) a.val.coord ∧
        F.RealAdaptedCoefficientGrid e ω hF (fun _ : σ => 1) d c.val.coord ∧
        ∃ X : F.associatedGradedFiltration.FormalInductionState (F.associatedGradedBasis e ω hF) ω
          (realificationLieSubalgebra (F.fullFastGradedDiagonal W))
          (F.fullFastGradedRelative e ω hF W) (F.gradedHorizontalKernel e ω hF K)
          (F.gradedHorizontalKernelBasis e ω hF K bK) T 2 ((absorbedInitialParameter p + C) ^ C),
          X.P = F.realAdaptedGradedPolynomialHom e ω hF (fun _ : σ => 1) g.val

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

universe uσ uι uτ uL

variable {σ : Type uσ} {ι : Type uι} {τ : Type uτ} {L : Type uL}
  [Fintype σ] [DecidableEq σ] [Fintype ι] [Fintype τ]
  [LieRing L] [LieAlgebra ℚ L] {s a d : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
  (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded)

local notation "ωW" => (fun i : ReducedSquareBasisIndex s ω => squareBasisWeight ω (Subtype.val i))
local notation "bW" => F.squareFiltration.quotientTop.associatedGradedBasis
  (F.reducedSquareBasis e ω hF) ωW (F.reducedSquareBasis_layers e ω hF)
local notation "Wf" => F.fastPointwiseSquare e ω hF (fun _ : σ => 1) W
local notation "Uf" => F.reducedSquareFastRelativeSubmodule (fun _ : σ => 1) Wf
local notation "J" => F.realFirstCoefficientFastSubmodule (fun _ : σ => 1) (fun _ => Nat.zero_lt_one) Uf
local notation "E" => F.RealFirstCoefficientModule (fun _ : σ => 1)
local notation "Q" => (E ⧸ J)
local notation "G" => F.realFastDiagonalSubgroup (fun _ : σ => 1) Wf
local notation "ρ" => F.realFastCoefficientAction (fun _ : σ => 1) (fun _ => Nat.zero_lt_one) Wf
local notation "Hq" => F.realFastCoefficientHorizontal (fun _ : σ => 1) (fun _ => Nat.zero_lt_one) Uf

def ExtractedInitialStateSpec (C : ℕ) : Prop :=
  ∀ (H : ℕ) (p : ℝ) (_hH : 1 ≤ H) (_hp : 0 ≤ p)
    (_hι : (Fintype.card ι : ℝ) ≤ p) (_hσ : (Fintype.card σ : ℝ) ≤ p)
    (_hτ : (Fintype.card τ : ℝ) ≤ p) (_hap : (a : ℝ) ≤ p)
    (_hHp : (H : ℝ) ≤ Real.exp p)
    (_hstructure : ∀ i j k, RationalHeightLE (e.repr ⁅e i, e j⁆ k) H)
    (_hW : BasisGradedSubmodule bW ωW W.toSubmodule)
    (v : τ → F.squareFiltration.quotientTop.AssociatedGraded)
    (_hv : Submodule.span ℚ (Set.range v) = W.toSubmodule)
    (_hheight : ∀ j i, RationalHeightLE ((bW).repr (v j) i) H)
    (g₀ : G) (_hzero : coefficients (F.realAdaptedPolynomialMap (fun _ : σ => 1) g₀.val.coord) 0 = 0)
    (b : Basis (Fin d) ℝ Q) (rows : Fin d → FirstCoefficientIndex (fun _ : σ => 1) ω)
    (ha : a ≤ d) (η : (Fin a → ℝ) ≃ₗ[ℝ] (ℝ ⊗[ℚ] (L ⧸ F.layer 2)))
    (_hη : ∀ x, η (fun i => b.equivFun x (Fin.castLE ha i)) = Hq x)
    (sectionMap : (Fin d → ℝ) →ₗ[ℝ] E)
    (_hsection : ∀ y, (J).mkQ (sectionMap y) = b.equivFun.symm y)
    (Cscale : ℝ) (_hC : 0 ≤ Cscale) (_hCp : Cscale ≤ Real.exp p)
    (_hweighted : ∀ (T : σ → ℝ), (∀ i, 0 < T i) → ∀ M : ℝ, 0 ≤ M →
      (∀ x, F.FirstCoefficientSlowBound e ω hF (fun _ : σ => 1) T M x → ∀ i,
        |b.equivFun ((J).mkQ x) i| ≤ Cscale * M / monomialScale T (rows i).val.1) ∧
      (∀ y, (∀ i, |y i| ≤ M / monomialScale T (rows i).val.1) →
        F.FirstCoefficientSlowBound e ω hF (fun _ : σ => 1) T (Cscale * M) (sectionMap y)))
    (δ : ℕ) (_hδ : 0 < δ) (_hδp : (δ : ℝ) ≤ Real.exp p)
    (_hprojectionGrid : ∀ m x, F.FirstCoefficientGrid e ω hF (fun _ : σ => 1) m x →
      b.equivFun ((J).mkQ x) ∈ realDenominatorGrid (δ * m))
    (_hsectionGrid : ∀ m (y : Fin d → ℝ), y ∈ realDenominatorGrid m →
      F.FirstCoefficientGrid e ω hF (fun _ : σ => 1) (δ * m) (sectionMap y))
    (T : σ → ℝ) (_hT : ∀ i, Real.exp ((p + C) ^ C) ≤ T i)
    (B : ℝ) (_hB : 0 ≤ B) (_hBp : B ≤ Real.exp p)
    (D : CoordinateDerivativeSystem ha T
      (b.equivFun.toLinearMap.comp (F.realFastCoefficientDirectionMap Wf g₀.val))
      (b.equivFun.symm.trans ((ρ g₀).trans b.equivFun))
      (fun i => monomialScale T (rows i).val.1) B),
    D.k ≤ a ∧ ∃ (K : Submodule ℚ (L ⧸ F.layer 2)) (bK : Basis (Fin D.k) ℚ K),
      ∃ Hk : ℕ, 1 ≤ Hk ∧ (Hk : ℝ) ≤ Real.exp ((p + 2) ^ 3) ∧
        (∀ i j, RationalHeightLE ((F.layerOneBasis e ω hF).repr (bK j).val i) Hk) ∧
        ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
          ∃ x g z : G, x * g * z = g₀ ∧
            F.RealAdaptedCoefficientBound e ω hF (fun _ : σ => 1) T
              (Real.exp ((p + C) ^ C)) x.val.coord ∧
            F.RealAdaptedCoefficientGrid e ω hF (fun _ : σ => 1) m z.val.coord ∧
            ∃ X : F.associatedGradedFiltration.FormalInductionState (F.associatedGradedBasis e ω hF) ω
              (realificationLieSubalgebra (F.fullFastGradedDiagonal W))
              (F.fullFastGradedRelative e ω hF W) (F.gradedHorizontalKernel e ω hF K)
              (F.gradedHorizontalKernelBasis e ω hF K bK) T 2 ((p + C) ^ C),
              X.P = F.realAdaptedGradedPolynomialHom e ω hF (fun _ : σ => 1) g.val

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeCrossFactorization
namespace OAI

section

namespace Erdos3.NativeCrossWitnesses

open scoped TensorProduct BigOperators

attribute [local instance] NativeVectorCorrelation.lie NativeVectorCorrelation.algebra
  NativeVectorCorrelation.topology NativeVectorCorrelation.topologicalAdd
  NativeVectorCorrelation.continuousSMul NativeVectorCorrelation.hausdorff

variable {s N : ℕ} [NeZero N] {p : ℝ} {f₀ f₁ : ZMod N → ℂ}
  {m : ZMod N → ZMod N → ℂ} {H : Finset (ZMod N)}
  (U : NativeCrossWitnesses s N p f₀ f₁ m H)

noncomputable def lower (h : H) (x : ZMod N) : ℂ := (U h).test.evalCyclic N (fun _ => x)

end Erdos3.NativeCrossWitnesses

end

end OAI
end


