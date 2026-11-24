-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PDiagForms
-- name    : GroundTheory_HeightsAndTheta_Heights_Intersections_PDiagForms
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:19:24.934736+00:00
-- url     : https://prove2.me/theorems/fce84585-9d6e-4a6a-a419-6516dc97924c
-- title:
--   PDiag Forms
-- statement:
--   Definitions and structural lemmas for PDiag Forms, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PDiagForms.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsDiagDiv
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PRFormula
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI
noncomputable section
namespace DiagonalForms
section Local
variable {Ω : Type*} [Field Ω]
end Local
section Bundle
variable {Ω : Type*} [Field Ω] {ι : Type*} {E : Type*} [AddCommGroup E] [Module Ω E] {x : ι → Ω}
end Bundle
section Forms
variable {Ω : Type*} [Field Ω] {E : Type*} [AddCommGroup E] [Module Ω E]
end Forms
section Chart
variable {Ω : Type} [Field Ω] {ι κ : Type} {E : Type} [AddCommGroup E] [Module Ω E] {x : ι → Ω}
end Chart
section Homog
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
end Homog
section Coord
variable {Ω : Type} [Field Ω] {ι ν κ : Type} [Fintype ι] [Fintype ν] [Fintype κ] {E : Type} [AddCommGroup E]
  [Module Ω E] {Φ : Type} [Field Φ] [Algebra Ω Φ]
end Coord
end DiagonalForms
end
end GroundTheory.Heights₂.Heights.Inter


