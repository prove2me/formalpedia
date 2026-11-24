-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_LiftFormNotMemBlowUpOf
-- name    : GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_LiftFormNotMemBlowUpOf
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:33:48.51112+00:00
-- url     : https://prove2.me/theorems/ab34b1f5-e54b-404c-8e03-80efbbd0a63d
-- title:
--   Lift Form Not Mem Blow Up Of
-- statement:
--   Definitions and structural lemmas for Lift Form Not Mem Blow Up Of, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/LiftFormNotMemBlowUpOf.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ImportsBisAlt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
universe u
noncomputable section
section Helpers
set_option linter.unusedSectionVars false
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} {R : Type*} [CommRing R]
variable {J : Type}
def blowUpCof (s m : MRing ι R) (e : K → ℕ) (u₀ v₀ : MRing ι R) : BlowUpIdx ι → MRing ι R
  | none => u₀ * s
  | some none => v₀ * m
  | some (some i) => v₀ * powMonomial e i
end Helpers
end
end GroundTheory.Heights₂.Heights.NumbersDVR


