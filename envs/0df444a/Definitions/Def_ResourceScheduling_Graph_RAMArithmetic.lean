-- Prove2me | Definitions.Def_ResourceScheduling_Graph_RAMArithmetic
-- name    : ResourceScheduling_Graph_RAMArithmetic
-- status  : Definition
-- author  : @arexychen
-- created : 2026-10-02T14:36:11.249228+00:00
-- url     : https://prove2.me/theorems/99f82ad9-0408-467b-88c5-c388b16583cf
-- title:
--   ResourceScheduling Graph RAMArithmetic
-- statement:
--   Concrete stack programs for truncated natural subtraction and multiplication by repeated word copying.
-- source:
--   New auxiliary formalization for the ResourceScheduling Q2 reduction. The target is the unchanged CookPvsNP one-tape machine model, following Cook, The P versus NP problem, Clay Mathematics Institute (2000), Appendix. This explicit finite-column stack compiler and its simulation lemmas are new contributions, not numbered claims from Cook or the scheduling source paper.

import Definitions.Def_ResourceScheduling_Graph_RAMOps
import Definitions.Def_CookPvsNP_StackRepeat

set_option autoImplicit false
namespace ResourceScheduling.Graph
open CookPvsNP

def ramSub {V : Type} [DecidableEq V] (i j dst : V) : StackProg (RAMWire V) Letter :=
  (copyProg (ramReg i) (ramTmp 0) (ramTmp 2)).seq <|
  (copyProg (ramReg j) (ramTmp 1) (ramTmp 2)).seq <|
  (consumeProg (ramTmp 1) (fun k => decide (k = ramTmp 0))).seq <|
  (ramZero dst).seq <| transferProg (ramTmp 0) (fun k => decide (k = ramReg dst))

def ramMulPorts {V : Type} [DecidableEq V] (j dst : V) (h : j ≠ dst) : Fin 4 ↪ RAMWire V where
  toFun := ![ramReg j, ramReg dst, ramTmp 0, ramTmp 1]
  inj' := by intro a b he; fin_cases a <;> fin_cases b <;>
    simp [ramReg, ramTmp, h, Ne.symm h] at he ⊢

def ramMul {V : Type} [DecidableEq V] (i j dst : V) (h : j ≠ dst) :=
  (copyProg (ramReg i) (ramTmp 0) (ramTmp 1)).seq <|
  (ramZero dst).seq <| repeatCopyProg (ramMulPorts j dst h)

end ResourceScheduling.Graph


