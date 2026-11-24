-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitDivVertical
-- name    : GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitDivVertical
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:23:55.640312+00:00
-- url     : https://prove2.me/theorems/a9ec7bec-c3e6-4b4f-b18b-f1ff903998cf
-- title:
--   Height Orbit Div Vertical
-- statement:
--   Definitions and structural lemmas for Height Orbit Div Vertical, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/HeightOrbitDivVertical.lean

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
def OrbitDivVertical.Statement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] [Nonempty ι] (n : ι → ℕ)
    (A : HermLine n) (x : Cone n (AlgebraicClosure ℚ)) (s : MvPolynomial (Coord n) ℤ),
    BlockNonzero x → Geo.IsSectionOn (orbitIdeal x) A.toGeo s →
    ∀ V ∈ Geo.divSupp (orbitIdeal x) s, ¬ Geo.IsHorizontal (ι := blockIdx n) V
example : BlockNonzero samplePoint ∧
    Geo.IsSectionOn (orbitIdeal samplePoint) (HermLine.standard _).toGeo
      (chartMonomial (fun _ ↦ 0) 1) :=
  ⟨samplePoint_blockNonzero,
    isSectionOn_chartMonomial _ _ _ (fun _ ↦ by simp [samplePoint]) 1 (fun _ ↦ rfl)⟩
end GroundTheory.Heights₂.Heights


