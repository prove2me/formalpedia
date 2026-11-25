-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PValuativeCentre
-- name    : GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PValuativeCentre
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T06:35:22.892736+00:00
-- url     : https://prove2.me/theorems/5fbd022c-5eb6-5ba4-abb3-12bc9d232673
-- title:
--   PValuative Centre
-- statement:
--   Definitions and structural lemmas for PValuative Centre, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PValuativeCentre.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsValuativeCentre
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PMChartDehomog
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.FieldNumbers
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u
section Graded
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} {F : Type*} [Field F]
  {κ : Type*} [CommRing κ]
def blockSpecial (ρ : MRing ι F →+* κ) : MRing ι F →+* MvPolynomial K κ :=
  eval₂Hom (C.comp (ρ.comp C)) fun v => C (ρ (X v)) * X v.1
end Graded
end
end GroundTheory.Heights₂.Heights.FieldNumbers


