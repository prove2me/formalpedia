-- Prove2me | Definitions.Def_GaussianPerimeter_Geometry
-- name    : GaussianPerimeter_Geometry
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T10:08:22.038103+00:00
-- url     : https://prove2.me/theorems/bd7390cd-9c62-4d33-b27c-a60c77ba6127
-- title:
--   Geometry
-- statement:
--   Definitions and structural lemmas for Geometry, from XinyuanXie-hub (XinyuanXie-hub/GaussianPerimeter; see pinned Apache-2.0 LICENSE)'s pinned Asymptotic lower bound for Gaussian perimeter of convex bodies development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/XinyuanXie-hub/GaussianPerimeter/blob/c54671095b3fdc672137addf46aa638c813db46a/GaussianPerimeter/Geometry.lean

module
public import Definitions.Def_GaussianPerimeter_Definitions
public import Mathlib.MeasureTheory.Integral.Lebesgue.Map
public import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
set_option autoImplicit true
@[expose] public section
public section
@[expose] section
open Function Set MeasureTheory MeasureTheory.Measure
open scoped ENNReal InnerProductSpace RealInnerProductSpace Function
namespace GaussianPerimeter
local notation "Euc" k => EuclideanSpace ℝ (Fin k)
noncomputable def facetBasis {k : ℕ} (u : Euc (k + 1)) (hu : ‖u‖ = 1) :
    OrthonormalBasis (Fin k) ℝ (ℝ ∙ u)ᗮ :=
  letI : Fact (Module.finrank ℝ (Euc (k + 1)) = k + 1) := ⟨by simp⟩
  OrthonormalBasis.fromOrthogonalSpanSingleton k (v := u) (by
    intro h
    simp [h] at hu)
noncomputable def referenceNormal (k : ℕ) : Euc (k + 1) :=
  EuclideanSpace.basisFun (Fin (k + 1)) ℝ 0
theorem norm_referenceNormal (k : ℕ) : ‖referenceNormal k‖ = 1 :=
  (EuclideanSpace.basisFun (Fin (k + 1)) ℝ).norm_eq_one 0
noncomputable def referenceTangent {k : ℕ} (y : Euc k) :
    (ℝ ∙ referenceNormal k)ᗮ :=
  (facetBasis (referenceNormal k) (norm_referenceNormal k)).repr.symm y
noncomputable def normalReflection {k : ℕ} (u : Euc (k + 1)) :
    (Euc (k + 1)) ≃ₗᵢ[ℝ] (Euc (k + 1)) :=
  (ℝ ∙ (referenceNormal k - u))ᗮ.reflection
noncomputable def facetTangent {k : ℕ} (u : Euc (k + 1)) (y : Euc k) :
    Euc (k + 1) :=
  normalReflection u (referenceTangent y)
noncomputable def facetEmbedding {k : ℕ} (u : Euc (k + 1)) (_hu : ‖u‖ = 1) (ρ : ℝ)
    (y : Euc k) : Euc (k + 1) :=
  ρ • u + facetTangent u y
variable {k : ℕ} {ι : Type*}
def halfspaceIntersection (u : ι → Euc (k + 1)) (ρ : ℝ) : Set (Euc (k + 1)) :=
  ⋂ i, {x | ⟪u i, x⟫_ℝ ≤ ρ}
def strictFacet (u : ι → Euc (k + 1)) (ρ : ℝ) (i : ι) : Set (Euc (k + 1)) :=
  {x | ⟪u i, x⟫_ℝ = ρ} ∩ ⋂ j : {j // j ≠ i}, {x | ⟪u j.1, x⟫_ℝ < ρ}
end GaussianPerimeter


