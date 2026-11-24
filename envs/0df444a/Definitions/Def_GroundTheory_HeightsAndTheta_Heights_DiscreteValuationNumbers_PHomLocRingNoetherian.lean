-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PHomLocRingNoetherian
-- name    : GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PHomLocRingNoetherian
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:41:01.140739+00:00
-- url     : https://prove2.me/theorems/88b33072-63e4-4aab-a677-edc21e51da0e
-- title:
--   PHom Loc Ring Noetherian
-- statement:
--   Definitions and structural lemmas for PHom Loc Ring Noetherian, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PHomLocRingNoetherian.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsHomLocRingLocal
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
noncomputable section
universe u
namespace HomLocRingNoetherian
variable {R : Type u} [CommRing R] {K : Type} [DecidableEq K] {ι : K → Type}
variable (P : Ideal (MRing ι R)) [P.IsPrime]
abbrev img : MRing ι R →+* FractionRing (MRing ι R ⧸ P) :=
  (algebraMap (MRing ι R ⧸ P) (FractionRing (MRing ι R ⧸ P))).comp (Ideal.Quotient.mk P)
variable {P}
end HomLocRingNoetherian
end
end GroundTheory.Heights₂.Heights.NumbersDVR


