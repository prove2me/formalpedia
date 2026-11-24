-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitChartTerm
-- name    : GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitChartTerm
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:55:35.445948+00:00
-- url     : https://prove2.me/theorems/6ef789c1-f741-45ca-9534-608b068dd80b
-- title:
--   Height Orbit Chart Term
-- statement:
--   Definitions and structural lemmas for Height Orbit Chart Term, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/HeightOrbitChartTerm.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitChart
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ratioField_le_coordField_177461042b61
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
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G
def OrbitChartTerm.Statement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (n : ι → ℕ)
    (A : HermLine n) (x : Cone n (AlgebraicClosure ℚ)) (s : MvPolynomial (Coord n) ℤ),
    Geo.IsSectionOn (orbitIdeal x) A.toGeo s → ∀ c : (k : ι) → Fin (n k + 1),
      (∀ k, x k (c k) ≠ 0) →
        chartEval x c s ≠ 0 ∧ ∀ v : FinitePlace (coordField x),
          (∀ k, (X ⟨k, c k⟩ : MvPolynomial (Coord n) ℤ) ∉ orbitCenter x v) →
            finiteTerm A v (coordVec x) - Real.log (v (evalCone (coordVec x) s)) =
              -Real.log (v (IntermediateField.inclusion (ratioField_le_coordField x)
                (chartEval x c s)))
example : BlockNonzero samplePoint ∧
    Geo.IsSectionOn (orbitIdeal samplePoint) (HermLine.standard _).toGeo
      (chartMonomial (fun _ ↦ 0) 1) ∧ ∀ k, samplePoint k ((fun _ ↦ 0) k) ≠ 0 :=
  ⟨samplePoint_blockNonzero,
    isSectionOn_chartMonomial _ _ _ (fun _ ↦ by simp [samplePoint]) 1 (fun _ ↦ rfl),
    fun _ ↦ by simp [samplePoint]⟩
end GroundTheory.Heights₂.Heights


