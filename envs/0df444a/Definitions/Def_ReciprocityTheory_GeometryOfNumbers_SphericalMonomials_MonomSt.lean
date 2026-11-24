-- Prove2me | Definitions.Def_ReciprocityTheory_GeometryOfNumbers_SphericalMonomials_MonomSt
-- name    : ReciprocityTheory_GeometryOfNumbers_SphericalMonomials_MonomSt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:30:42.044058+00:00
-- url     : https://prove2.me/theorems/b9f5899d-5a49-4aa9-ae9f-218fc91d7714
-- title:
--   Monom St
-- statement:
--   Definitions and structural lemmas for Monom St, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/SphericalMonomials/MonomSt.lean

import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_SphericalMonomials_MonomStA
import Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_sphMonom_measurable_normalize

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.GeometryOfNumbersTheory
open MeasureTheory
instance isProbabilityMeasure_sphProb (N : ℕ) : IsProbabilityMeasure (sphProb N) := by
  unfold sphProb
  exact Measure.isProbabilityMeasure_map sphMonom_measurable_normalize.aemeasurable
end ReciprocityTheory.GeometryOfNumbersTheory


