-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitArchSum
-- name    : GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitArchSum
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:21:55.29795+00:00
-- url     : https://prove2.me/theorems/6e9aeca4-4fb0-4a26-90a6-97323ca1180a
-- title:
--   Height Orbit Arch Sum
-- statement:
--   Definitions and structural lemmas for Height Orbit Arch Sum, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/HeightOrbitArchSum.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightObjects
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
open ReciprocityTheory.ChartRestriction.G NumberField
def OrbitArchSum.Statement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] [Nonempty ι] (n : ι → ℕ)
    (A : HermLine n) (x : Cone n (AlgebraicClosure ℚ)) (s : MvPolynomial (Coord n) ℤ),
    BlockNonzero x → Geo.IsSectionOn (orbitIdeal x) A.toGeo s →
    Geo.arInt (orbitIdeal x) s A.toGeo (Fin.elim0 : Fin 0 → Geo.HermLine (blockIdx n)) =
      (Geo.degC (ι := blockIdx n) (orbitIdeal x) : ℝ) / Module.finrank ℚ (coordField x) *
        ∑ σ : coordField x →+* ℂ,
          Real.log (‖evalCone (fun k i ↦ σ (coordVec x k i)) s‖ /
            A.metric (fun k i ↦ σ (coordVec x k i)))
example : BlockNonzero samplePoint ∧
    Geo.IsSectionOn (orbitIdeal samplePoint) (HermLine.standard _).toGeo
      (chartMonomial (fun _ ↦ 0) 1) :=
  ⟨samplePoint_blockNonzero,
    isSectionOn_chartMonomial _ _ _ (fun _ ↦ by simp [samplePoint]) 1 (fun _ ↦ rfl)⟩
end GroundTheory.Heights₂.Heights


