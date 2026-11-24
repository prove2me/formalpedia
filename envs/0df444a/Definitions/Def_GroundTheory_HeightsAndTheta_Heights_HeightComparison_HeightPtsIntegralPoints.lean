-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightPtsIntegralPoints
-- name    : GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightPtsIntegralPoints
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T06:06:56.855953+00:00
-- url     : https://prove2.me/theorems/24565b47-8279-4ce9-a2fe-cd50468bbaf0
-- title:
--   Height Pts Integral Points
-- statement:
--   Definitions and structural lemmas for Height Pts Integral Points, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/HeightPtsIntegralPoints.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitDegree
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_OrbitDegree_full_f938816fbbe2
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
abbrev projPts {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
    (P : Ideal (Geo.MRing ι)) :=
  Quot fun z z' : Geo.mcPts P ↦
    ∃ c : K → ℂ, (∀ k, c k ≠ 0) ∧ (z' : (Σ k, ι k) → ℂ) = fun p ↦ c p.1 * (z : (Σ k, ι k) → ℂ) p
def PtsIntegralPoints.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [Nonempty K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (P : Ideal (Geo.MRing ι)) (g : ((Σ k, ι k) → ℂ) → ℝ),
    Finite (projPts P) →
    (∀ (c : K → ℂ) (z : (Σ k, ι k) → ℂ), (∀ k, c k ≠ 0) → z ∈ Geo.mcPts P →
      g (fun p ↦ c p.1 * z p) = g z) →
    Geo.ptsIntegral P (Fin.elim0 : Fin 0 → ((Σ k, ι k) → ℂ) → ℝ) g =
      ∑ᶠ q : projPts P, g (Quot.out q : Geo.mcPts P)
example : Finite (projPts (ι := blockIdx (fun _ : Unit ↦ 1)) (orbitIdeal samplePoint)) ∧
    ∀ (c : Unit → ℂ) (z : Coord (fun _ : Unit ↦ 1) → ℂ), (∀ k, c k ≠ 0) →
      z ∈ Geo.mcPts (ι := blockIdx (fun _ : Unit ↦ 1)) (orbitIdeal samplePoint) →
      (fun w : Coord (fun _ : Unit ↦ 1) → ℂ ↦ ‖w ⟨(), 0⟩‖ / ‖w ⟨(), 1⟩‖) (fun p ↦ c p.1 * z p) =
        (fun w : Coord (fun _ : Unit ↦ 1) → ℂ ↦ ‖w ⟨(), 0⟩‖ / ‖w ⟨(), 1⟩‖) z := by
  refine ⟨(Nat.card_pos_iff.mp (OrbitDegree.full Unit _ samplePoint samplePoint_blockNonzero)).2,
    fun c z hc _ ↦ ?_⟩
  simp only [norm_mul]
  exact mul_div_mul_left _ _ (norm_ne_zero_iff.mpr (hc ()))
end GroundTheory.Heights₂.Heights


