-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_ModuliSurvey_IsQProjOverOfIsProjOver
-- name    : Development_AbelianVarietyTheory_Counterexamples_ModuliSurvey_IsQProjOverOfIsProjOver
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:15:48.120484+00:00
-- url     : https://prove2.me/theorems/e89052fe-9d91-4e24-a693-b2abf194adc8
-- title:
--   Is QProj Over Of Is Proj Over
-- statement:
--   Definitions and structural lemmas for Is QProj Over Of Is Proj Over, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/ModuliSurvey/IsQProjOverOfIsProjOver.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsCompletedStrictHens
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_AbProj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.SchemeWords
open AlgebraicGeometry CategoryTheory IsLocalRing ReciprocityTheory.ChartRestriction.G.Geo.Tor
section Proj
variable {R : Type} [CommRing R] {X : Scheme.{0}} {f : X ⟶ Sp R}
end Proj
section Hens
variable {A R : Type} [CommRing A] [IsLocalRing A] [CommRing R] [IsLocalRing R]
  [Algebra A R] [IsLocalHom (algebraMap A R)]
end Hens
end GlobalTheory.SchemeWords


