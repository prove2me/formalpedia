-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_ConductorsKronecker_ChCond
-- name    : Development_AutomorphicArithmetic_ConductorsKronecker_ChCond
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T02:04:37.835512+00:00
-- url     : https://prove2.me/theorems/c91d7133-f7e5-456a-8ec4-80ab1ec2fd71
-- title:
--   Ch Cond
-- statement:
--   Definitions and structural lemmas for Ch Cond, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/ConductorsKronecker/ChCond.lean

import Definitions.Def_Development_AutomorphicArithmetic_PrimitiveCosets_CoreAtH
import Definitions.Def_Development_AutomorphicArithmetic_PrimitiveCosets_ToEBij
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv


set_option autoImplicit false
open UpperTheory.Comparison₂ Deduction.CH Formalism Formalism.HC Formalism.D5 Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LHost NumberField Ideal
section
variable {A : Type} [AddCommGroup A] [Fintype A] [DecidableEq A]
end
def UpperTheory.GL.jac (l : ℕ) : ℕ →* ℤ where
  toFun a := jacobiSym (a : ℤ) l
  map_one' := by simp
  map_mul' a b := by rw [Nat.cast_mul, jacobiSym.mul_left]


