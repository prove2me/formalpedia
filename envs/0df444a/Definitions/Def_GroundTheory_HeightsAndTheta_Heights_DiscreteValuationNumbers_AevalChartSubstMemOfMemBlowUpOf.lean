-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_AevalChartSubstMemOfMemBlowUpOf
-- name    : GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_AevalChartSubstMemOfMemBlowUpOf
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:35:57.384092+00:00
-- url     : https://prove2.me/theorems/508c258f-b3db-4655-82a8-6d34a572fc3d
-- title:
--   Aeval Chart Subst Mem Of Mem Blow Up Of
-- statement:
--   Definitions and structural lemmas for Aeval Chart Subst Mem Of Mem Blow Up Of, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/AevalChartSubstMemOfMemBlowUpOf.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_LiftFormNotMemBlowUpOf
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDivCycleMul
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
section Chart
variable {K : Type*} {ι : K → Type} {J : Type} {R : Type*} [CommRing R]
def chartSubst (a : J → MRing ι R) : (Σ o, extIdx ι J o) → Polynomial (MRing ι R)
  | ⟨none, j⟩ => Polynomial.C (a j) * Polynomial.X
  | ⟨some k, i⟩ => Polynomial.C (X ⟨k, i⟩)
end Chart
end
end GroundTheory.Heights₂.Heights.NumbersDVR


