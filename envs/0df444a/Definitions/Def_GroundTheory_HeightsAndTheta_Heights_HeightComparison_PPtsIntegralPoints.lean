-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_PPtsIntegralPoints
-- name    : GroundTheory_HeightsAndTheta_Heights_HeightComparison_PPtsIntegralPoints
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T16:50:58.757298+00:00
-- url     : https://prove2.me/theorems/f41efadd-f356-450a-8928-9b6ea2acc90a
-- title:
--   PPts Integral Points
-- statement:
--   Definitions and structural lemmas for PPts Integral Points, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/PPtsIntegralPoints.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightPtsIntegralPoints
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitCurve
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeB
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_OrbitCurve_full_3c2dbdc5d679
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_OrbitCurve_isMultiHomogIdeal_orbitIdeal_5ad0b5ef0050
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
open ReciprocityTheory.ChartRestriction.G MeasureTheory
namespace PtsIntegralPoints
set_option linter.unusedSectionVars false
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
def HomogStatement : Prop :=
  ∀ (K : Type) [Fintype K] [Nonempty K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (P : Ideal (Geo.MRing ι)) (g : ((Σ k, ι k) → ℂ) → ℝ),
    Geo.IsMultiHomogIdeal P → Finite (projPts P) →
    (∀ (c : K → ℂ) (z : (Σ k, ι k) → ℂ), (∀ k, c k ≠ 0) → z ∈ Geo.mcPts P →
      g (fun p ↦ c p.1 * z p) = g z) →
    Geo.ptsIntegral P (Fin.elim0 : Fin 0 → ((Σ k, ι k) → ℂ) → ℝ) g =
      ∑ᶠ q : projPts P, g (Quot.out q : Geo.mcPts P)
example : Geo.IsMultiHomogIdeal (ι := blockIdx (fun _ : Unit ↦ 1)) (orbitIdeal samplePoint) ∧
    Finite (projPts (ι := blockIdx (fun _ : Unit ↦ 1)) (orbitIdeal samplePoint)) ∧
    ∀ (c : Unit → ℂ) (z : Coord (fun _ : Unit ↦ 1) → ℂ), (∀ k, c k ≠ 0) →
      z ∈ Geo.mcPts (ι := blockIdx (fun _ : Unit ↦ 1)) (orbitIdeal samplePoint) →
      (fun w : Coord (fun _ : Unit ↦ 1) → ℂ ↦ ‖w ⟨(), 0⟩‖ / ‖w ⟨(), 1⟩‖) (fun p ↦ c p.1 * z p) =
        (fun w : Coord (fun _ : Unit ↦ 1) → ℂ ↦ ‖w ⟨(), 0⟩‖ / ‖w ⟨(), 1⟩‖) z := by
  refine ⟨OrbitCurve.isMultiHomogIdeal_orbitIdeal samplePoint,
    (Nat.card_pos_iff.mp (OrbitDegree.full Unit _ samplePoint samplePoint_blockNonzero)).2,
    fun c z hc _ ↦ ?_⟩
  simp only [norm_mul]
  exact mul_div_mul_left _ _ (norm_ne_zero_iff.mpr (hc ()))
section Dependence
open MvPolynomial
noncomputable def affPtIdeal : Ideal (Geo.MRing (fun _ : Unit ↦ Fin 2)) :=
  Ideal.span {X ⟨(), 0⟩ - 2, X ⟨(), 1⟩ - 1}
noncomputable def affPt : (Σ _ : Unit, Fin 2) → ℂ := fun p ↦ if p.2 = 0 then 2 else 1
noncomputable def affProj (s : ℂ) : (((k : Unit) → Fin 2) → ℂ) →ₗ[ℂ] (Fin (0 + 1) → ℂ) :=
  s • LinearMap.pi fun _ ↦ LinearMap.proj fun _ ↦ 0
end Dependence
end PtsIntegralPoints
end GroundTheory.Heights₂.Heights


