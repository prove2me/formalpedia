-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitChartResidue
-- name    : GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitChartResidue
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:24:58.567835+00:00
-- url     : https://prove2.me/theorems/4df31b22-fdba-418d-ba0f-0e965c0768d4
-- title:
--   Height Orbit Chart Residue
-- statement:
--   Definitions and structural lemmas for Height Orbit Chart Residue, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/HeightOrbitChartResidue.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitChart
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
def OrbitChartResidue.Statement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] [Nonempty ι] (n : ι → ℕ)
    (A : HermLine n) (x : Cone n (AlgebraicClosure ℚ)) (s : MvPolynomial (Coord n) ℤ),
    BlockNonzero x → Geo.IsSectionOn (orbitIdeal x) A.toGeo s →
    ∀ V ∈ Geo.divSupp (orbitIdeal x) s, ∀ c : (k : ι) → Fin (n k + 1),
      (∀ k, (X ⟨k, c k⟩ : MvPolynomial (Coord n) ℤ) ∉ V) →
        (Geo.geoNum (ι := blockIdx n) 0 V Fin.elim0 : ℝ) * Real.log (Geo.charOf V) =
          Real.log (Nat.card (chartRing x c ⧸ chartPoint x c V))
example : BlockNonzero samplePoint ∧
    Geo.IsSectionOn (orbitIdeal samplePoint) (HermLine.standard _).toGeo
      (chartMonomial (fun _ ↦ 0) 1) ∧ ∀ k, samplePoint k ((fun _ ↦ 0) k) ≠ 0 :=
  ⟨samplePoint_blockNonzero,
    isSectionOn_chartMonomial _ _ _ (fun _ ↦ by simp [samplePoint]) 1 (fun _ ↦ rfl),
    fun _ ↦ by simp [samplePoint]⟩
end GroundTheory.Heights₂.Heights


