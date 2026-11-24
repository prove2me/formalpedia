-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitConjSum
-- name    : GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitConjSum
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T06:13:11.994663+00:00
-- url     : https://prove2.me/theorems/ea119936-6938-48eb-94e5-3ad63a7120a3
-- title:
--   Height Orbit Conj Sum
-- statement:
--   Definitions and structural lemmas for Height Orbit Conj Sum, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/HeightOrbitConjSum.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightPtsIntegralPoints
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_samplePoint_blockNonzero_cdc1bb3eff09

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
open ReciprocityTheory.ChartRestriction.G
def OrbitConjSum.Statement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (n : ι → ℕ) (x : Cone n (AlgebraicClosure ℚ))
    (g : (Coord n → ℂ) → ℝ), BlockNonzero x →
    (∀ (c : ι → ℂ) (z : Coord n → ℂ), (∀ k, c k ≠ 0) →
      z ∈ Geo.mcPts (ι := blockIdx n) (orbitIdeal x) → g (fun p ↦ c p.1 * z p) = g z) →
    (Geo.degC (ι := blockIdx n) (orbitIdeal x) : ℝ) *
        ∑ σ : coordField x →+* ℂ, g (fun p ↦ σ (coordVec x p.1 p.2)) =
      (Module.finrank ℚ (coordField x) : ℝ) *
        ∑ᶠ q : projPts (ι := blockIdx n) (orbitIdeal x),
          g (Quot.out q : Geo.mcPts (ι := blockIdx n) (orbitIdeal x))
example : BlockNonzero samplePoint ∧
    ∀ (c : Unit → ℂ) (z : Coord (fun _ : Unit ↦ 1) → ℂ), (∀ k, c k ≠ 0) →
      z ∈ Geo.mcPts (ι := blockIdx (fun _ : Unit ↦ 1)) (orbitIdeal samplePoint) →
      (fun w : Coord (fun _ : Unit ↦ 1) → ℂ ↦ ‖w ⟨(), 0⟩‖ / ‖w ⟨(), 1⟩‖) (fun p ↦ c p.1 * z p) =
        (fun w : Coord (fun _ : Unit ↦ 1) → ℂ ↦ ‖w ⟨(), 0⟩‖ / ‖w ⟨(), 1⟩‖) z := by
  refine ⟨samplePoint_blockNonzero, fun c z hc _ ↦ ?_⟩
  simp only [norm_mul]
  exact mul_div_mul_left _ _ (norm_ne_zero_iff.mpr (hc ()))
end GroundTheory.Heights₂.Heights


