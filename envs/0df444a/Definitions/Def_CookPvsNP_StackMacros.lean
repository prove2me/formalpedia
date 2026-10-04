-- Prove2me | Definitions.Def_CookPvsNP_StackMacros
-- name    : CookPvsNP_StackMacros
-- status  : Definition
-- author  : @arexychen
-- created : 2026-10-02T12:35:38.797375+00:00
-- url     : https://prove2.me/theorems/2a98e2cd-1a32-47b6-aff9-276a4970f31e
-- title:
--   CookPvsNP StackMacros
-- statement:
--   Concrete transfer, copy, clear, push, pop, and simultaneous-consumption stack programs, with their specified store transformations.
-- source:
--   New auxiliary formalization for the ResourceScheduling Q2 reduction. The target is the unchanged CookPvsNP one-tape machine model, following Cook, The P versus NP problem, Clay Mathematics Institute (2000), Appendix. This explicit finite-column stack compiler and its simulation lemmas are new contributions, not numbered claims from Cook or the scheduling source paper.

import Definitions.Def_CookPvsNP_StackProgram

set_option autoImplicit false
namespace CookPvsNP

def transferAct {K A : Type} [DecidableEq K] (src : K) (targets : K → Bool)
    (h : K → Option A) (k : K) : StackAct A :=
  if k = src then .pop else if targets k then
    match h src with | some a => .push a | none => .keep
  else .keep

/-- Transfer a stack, reversing it onto any selected target stacks. -/
def transferProg {K A : Type} [DecidableEq K] (src : K) (targets : K → Bool) : StackProg K A :=
  .loop (fun h => (h src).isSome) (.act (transferAct src targets))

def transferStore {K A : Type} [DecidableEq K] (src : K) (targets : K → Bool)
    (s : K → List A) (k : K) : List A :=
  if k = src then [] else if targets k then (s src).reverse ++ s k else s k

def copyProg {K A : Type} [DecidableEq K] (src dst scratch : K) : StackProg K A :=
  .seq (transferProg src (fun k => decide (k = scratch)))
    (transferProg scratch (fun k => decide (k = src ∨ k = dst)))

def clearProg {K A : Type} [DecidableEq K] (src : K) : StackProg K A :=
  transferProg src (fun _ => false)

def popProg {K A : Type} [DecidableEq K] (src : K) : StackProg K A :=
  .act (fun _ k => if k = src then .pop else .keep)

def pushProg {K A : Type} [DecidableEq K] (dst : K) (a : A) : StackProg K A :=
  .act (fun _ k => if k = dst then .push a else .keep)

def consumeAct {K A : Type} [DecidableEq K] (src : K) (targets : K → Bool)
    (_h : K → Option A) (k : K) : StackAct A :=
  if k = src ∨ targets k = true then .pop else .keep

def consumeProg {K A : Type} [DecidableEq K] (src : K) (targets : K → Bool) : StackProg K A :=
  .loop (fun h => (h src).isSome) (.act (consumeAct src targets))

def consumeStore {K A : Type} [DecidableEq K] (src : K) (targets : K → Bool)
    (s : K → List A) (k : K) : List A :=
  if k = src then [] else if targets k then (s k).drop (s src).length else s k

end CookPvsNP


