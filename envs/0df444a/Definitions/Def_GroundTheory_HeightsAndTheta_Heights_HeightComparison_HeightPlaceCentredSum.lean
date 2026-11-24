-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightPlaceCentredSum
-- name    : GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightPlaceCentredSum
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:45:40.12991+00:00
-- url     : https://prove2.me/theorems/2934d43e-9231-409d-9c1d-55af5bcca820
-- title:
--   Height Place Centred Sum
-- statement:
--   Definitions and structural lemmas for Height Place Centred Sum, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/HeightPlaceCentredSum.lean

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
def PlaceCentredSum.Statement : Prop :=
  ∀ (L K : Type) [Field L] [NumberField L] [Field K] [NumberField K] [Algebra L K]
    (O : Subalgebra ℤ L) (m : Ideal O) (t : L),
    ∑ᶠ v ∈ {v : FinitePlace K | AbsCentredAt O m fun u ↦ v (algebraMap L K u)},
        -Real.log (v (algebraMap L K t)) =
      Module.finrank L K *
        ∑ᶠ w ∈ {w : FinitePlace L | AbsCentredAt O m fun u ↦ w u}, -Real.log (w t)
example : NumberField ℚ ∧ NumberField (CyclotomicField 4 ℚ) := ⟨inferInstance, inferInstance⟩
end GroundTheory.Heights₂.Heights


