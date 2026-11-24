-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PFlagLineDegree
-- name    : GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PFlagLineDegree
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:50:05.341163+00:00
-- url     : https://prove2.me/theorems/e6a1f865-5ae5-4bba-8e91-00b64f64b893
-- title:
--   PFlag Line Degree
-- statement:
--   Definitions and structural lemmas for PFlag Line Degree, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PFlagLineDegree.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsFlagLineDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PSplitRelDeg
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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
namespace FlagLineDegreeProof
def substVar {K : Type*} {ι : K → Type} {M : ℕ} {F : Type*} [CommRing F] (A : Fin M → MRing ι F) :
    (Σ o, bundleIdx ι M o) → MRing ι F
  | ⟨none, l⟩ => A l
  | ⟨some k, i⟩ => X ⟨k, i⟩
end FlagLineDegreeProof
end
end GroundTheory.Heights₂.Heights.NumbersDVR


