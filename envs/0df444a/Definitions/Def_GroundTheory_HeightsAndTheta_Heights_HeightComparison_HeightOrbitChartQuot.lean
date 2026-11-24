-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitChartQuot
-- name    : GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitChartQuot
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:24:47.97463+00:00
-- url     : https://prove2.me/theorems/59c962e4-9df2-4fb9-9df4-255abfaa7f69
-- title:
--   Height Orbit Chart Quot
-- statement:
--   Definitions and structural lemmas for Height Orbit Chart Quot, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/HeightOrbitChartQuot.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitChart
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
def OrbitChartQuot.Statement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (n : ι → ℕ) (x : Cone n (AlgebraicClosure ℚ))
    (c : (k : ι) → Fin (n k + 1)), (∀ k, x k (c k) ≠ 0) →
    ∀ V : Ideal (MvPolynomial (Coord n) ℤ), orbitIdeal x ≤ V →
      Nonempty ((chartRing x c ⧸ chartPoint x c V) ≃+*
        (MvPolynomial (Coord n) ℤ ⧸
          (V ⊔ Ideal.span (Set.range fun k ↦ (X ⟨k, c k⟩ : MvPolynomial (Coord n) ℤ) - 1))))
example : (∀ k, samplePoint k ((fun _ ↦ 0) k) ≠ 0) ∧
    orbitIdeal samplePoint ≤ orbitIdeal samplePoint :=
  ⟨fun _ ↦ by simp [samplePoint], le_rfl⟩
end GroundTheory.Heights₂.Heights


