-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ValuesMemOfLocal
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_ValuesMemOfLocal
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T02:01:20.403482+00:00
-- url     : https://prove2.me/theorems/430a3f1f-0dcc-450b-9077-68c64bd1d2e4
-- title:
--   Values Mem Of Local
-- statement:
--   Definitions and structural lemmas for Values Mem Of Local, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ValuesMemOfLocal.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MaximalIdealEqJointEigen
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPolynomial
namespace GlobalTheory.ExpCover
def transOp {L G W : Type} [CommRing L] [Mul G] [AddCommGroup W] [Module L W] (a : L) (t : Finset G) : (G → W) →ₗ[L] (G → W) where
  toFun v g := a • ∑ s ∈ t, v (g * s)
  map_add' v v' := by funext g; simp [Finset.sum_add_distrib, smul_add]
  map_smul' c v := by funext g; simp [Finset.smul_sum, smul_comm c]
end GlobalTheory.ExpCover


