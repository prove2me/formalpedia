-- Prove2me | Definitions.Def_ResourceScheduling_Graph_RAMOps
-- name    : ResourceScheduling_Graph_RAMOps
-- status  : Definition
-- author  : @arexychen
-- created : 2026-10-02T14:16:26.690967+00:00
-- url     : https://prove2.me/theorems/05a548aa-e7bc-46c4-af54-0c44438c4174
-- title:
--   ResourceScheduling Graph RAMOps
-- statement:
--   Concrete stack implementations of elementary register operations, unary emission, and indexed adjacency-bit reading.
-- source:
--   New auxiliary formalization for the ResourceScheduling Q2 reduction. The target is the unchanged CookPvsNP one-tape machine model, following Cook, The P versus NP problem, Clay Mathematics Institute (2000), Appendix. This explicit finite-column stack compiler and its simulation lemmas are new contributions, not numbered claims from Cook or the scheduling source paper.

import Definitions.Def_ResourceScheduling_Graph_RAM
import Definitions.Def_ResourceScheduling_Graph_StackEmit
import Definitions.Def_CookPvsNP_StackLookup
import Definitions.Def_CookPvsNP_StackCompare

set_option autoImplicit false
namespace ResourceScheduling.Graph
open CookPvsNP

def ramSkip {V : Type} : StackProg (RAMWire V) Letter := .act (fun _ _ => .keep)
def ramZero {V : Type} [DecidableEq V] (v : V) : StackProg (RAMWire V) Letter := clearProg (ramReg v)
def ramInc {V : Type} [DecidableEq V] (v : V) := pushProg (ramReg v) Letter.one
def ramDec {V : Type} [DecidableEq V] (v : V) : StackProg (RAMWire V) Letter := popProg (ramReg v)
def ramAppend {V : Type} [DecidableEq V] (src : RAMWire V) (v : V) : StackProg (RAMWire V) Letter :=
  copyProg src (ramReg v) (ramTmp 0)
def ramAssign {V : Type} [DecidableEq V] (src : RAMWire V) (v : V) :=
  (ramZero v).seq (ramAppend src v)

def ramEmitPorts {V : Type} (v : V) : Fin 4 ↪ RAMWire V where
  toFun := ![ramReg v, ramOutput, ramTmp 0, ramTmp 1]
  inj' := by intro i j h; fin_cases i <;> fin_cases j <;>
    simp [ramReg, ramOutput, ramTmp] at h ⊢

def ramEmit {V : Type} [DecidableEq V] (v : V) := emitUnaryProg (ramEmitPorts v)

def ramLookupPorts {V : Type} (i : V) : Fin 6 ↪ RAMWire V where
  toFun := ![ramInput, ramReg i, ramTmp 0, ramTmp 1, ramTmp 2, ramTmp 3]
  inj' := by intro a b h; fin_cases a <;> fin_cases b <;>
    simp [ramReg, ramInput, ramTmp] at h ⊢

def ramReadBit {V : Type} [DecidableEq V] (i dst : V) :=
  (lookupProg (ramLookupPorts i) Letter.sep).seq <|
  (ramZero dst).seq <| StackProg.act fun h k =>
    if k = ramTmp 0 then .pop else
    if k = ramReg dst ∧ h (ramTmp 0) = some Letter.one then .push Letter.one else .keep

end ResourceScheduling.Graph


