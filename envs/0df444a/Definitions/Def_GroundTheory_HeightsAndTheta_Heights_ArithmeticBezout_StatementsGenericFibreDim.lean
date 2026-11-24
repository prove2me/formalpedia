-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsGenericFibreDim
-- name    : GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsGenericFibreDim
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:59:16.709914+00:00
-- url     : https://prove2.me/theorems/b79776ff-bc34-4b92-a225-f470485ed196
-- title:
--   Statements Generic Fibre Dim
-- statement:
--   Definitions and structural lemmas for Statements Generic Fibre Dim, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/StatementsGenericFibreDim.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LinFormOneZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
namespace GroundTheory.Heights₂.Heights
namespace ObjectsChow
open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsArithVar)
def GenericFibreDim.Statement : Prop :=
  ∀ (n d : ℕ) (P : Ideal (MRing (PBlk n))), IsArithVar P d →
    ringKrullDim (MvPolynomial (Fin n) ℚ ⧸ genericIdeal P) = ((d : ℕ) : WithBot ℕ∞)
end ObjectsChow
end GroundTheory.Heights₂.Heights


