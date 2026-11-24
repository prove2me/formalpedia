-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PHilbertIncrement
-- name    : GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PHilbertIncrement
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:58:25.691815+00:00
-- url     : https://prove2.me/theorems/7340fd06-90d8-4170-b92a-d55e3584eaba
-- title:
--   PHilbert Increment
-- statement:
--   Definitions and structural lemmas for PHilbert Increment, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PHilbertIncrement.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsHilbert
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_ColonSpanSingletonEqOfNotMem
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PHilbExactDivide
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u
namespace HilbertIncrement
variable {K : Type} [DecidableEq K] {ι : K → Type} {F : Type u} [Field F]
def quotPiece (J : Ideal (MRing ι F)) (m : K → ℤ) : Submodule F (MRing ι F ⧸ J) :=
  (ringPiece m).map (Ideal.Quotient.mkₐ F J).toLinearMap
end HilbertIncrement
end
end GroundTheory.Heights₂.Heights.HilbertSamuel


