-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitCenterMemIff
-- name    : GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitCenterMemIff
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:21:06.012528+00:00
-- url     : https://prove2.me/theorems/f1150157-a60f-41d9-9984-cf3a73b22c76
-- title:
--   Height Orbit Center Mem Iff
-- statement:
--   Definitions and structural lemmas for Height Orbit Center Mem Iff, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/HeightOrbitCenterMemIff.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitCenter
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
def OrbitCenterMemIff.Statement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (n : ι → ℕ) (x : Cone n (AlgebraicClosure ℚ)),
    BlockNonzero x → ∀ (v : FinitePlace (coordField x)) (F : MvPolynomial (Coord n) ℤ)
      (d : ι → ℕ), Geo.IsMultiHomog (ι := blockIdx n) F d →
      (F ∈ orbitCenter x v ↔ v (evalCone (coordVec x) F) < ∏ k, (⨆ i, v (coordVec x k i)) ^ d k)
example : BlockNonzero samplePoint ∧
    Geo.IsMultiHomog (ι := blockIdx (fun _ : Unit ↦ 1)) (chartMonomial (fun _ ↦ 0) 1) 1 :=
  ⟨samplePoint_blockNonzero, (geoMultiHomog_iff _ _).mpr (isWeightedHomogeneous_chartMonomial _ _)⟩
end GroundTheory.Heights₂.Heights


