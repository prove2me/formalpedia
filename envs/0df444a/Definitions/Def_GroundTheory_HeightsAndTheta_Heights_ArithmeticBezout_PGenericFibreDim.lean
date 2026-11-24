-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PGenericFibreDim
-- name    : GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PGenericFibreDim
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:02:59.601803+00:00
-- url     : https://prove2.me/theorems/a763148e-c99d-494b-9826-48392e3b1919
-- title:
--   PGeneric Fibre Dim
-- statement:
--   Definitions and structural lemmas for PGeneric Fibre Dim, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PGenericFibreDim.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsGenericFibreDim
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IntToRat
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
namespace GenericFibreDim
def blkEquiv (n : ℕ) : Fin n ≃ (Σ _ : Unit, PBlk n ()) where
  toFun i := ⟨(), i⟩
  invFun x := x.2
  left_inv _ := rfl
  right_inv x := by rcases x with ⟨⟨⟩, i⟩; rfl
def blkRingEquiv (n : ℕ) : MvPolynomial (Fin n) ℤ ≃+* MRing (PBlk n) :=
  (renameEquiv ℤ (blkEquiv n)).toRingEquiv
end GenericFibreDim
end ObjectsChow
end GroundTheory.Heights₂.Heights


