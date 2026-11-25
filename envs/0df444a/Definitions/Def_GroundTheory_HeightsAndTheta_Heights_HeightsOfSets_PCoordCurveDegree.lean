-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_PCoordCurveDegree
-- name    : GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_PCoordCurveDegree
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T02:18:00.071366+00:00
-- url     : https://prove2.me/theorems/61ce722c-57e1-4a98-8da8-7ec971fc5370
-- title:
--   PCoord Curve Degree
-- statement:
--   Definitions and structural lemmas for PCoord Curve Degree, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/PCoordCurveDegree.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_PCoordCurveAlgebraic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4
namespace CoordCurveDegree
set_option linter.unusedSectionVars false
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [CharZero Ω]
def blockDeg (m : (Σ k, ι k) →₀ ℕ) (k : K) : ℕ := ∑ i, m ⟨k, i⟩
def homog (d : ∀ k, ι k) (N : ℕ) (g : MvPolynomial (Σ k, ι k) ℚ) : MvPolynomial (Σ k, ι k) ℚ :=
  ∑ m ∈ g.support, monomial m (coeff m g) * ∏ k, X ⟨k, d k⟩ ^ (N - blockDeg m k)
theorem ratio_mem (y : (Σ k, ι k) → Ω) {p q : Σ k, ι k} (h : p.1 = q.1) : y p / y q ∈ blockFnField y :=
  IntermediateField.subset_adjoin _ _ ⟨p, q, h, rfl⟩
def ratioF (y : (Σ k, ι k) → Ω) (d : ∀ k, ι k) (p : Σ k, ι k) : blockFnField y :=
  ⟨y p / y ⟨p.1, d p.1⟩, ratio_mem y rfl⟩
def ptOf (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (φ : blockFnField y →ₐ[ℚ] ℂ) : (Σ k, ι k) → ℂ :=
  fun p ↦ φ (ratioF y c p)
end CoordCurveDegree
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet


