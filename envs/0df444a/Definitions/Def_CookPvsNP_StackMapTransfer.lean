-- Prove2me | Definitions.Def_CookPvsNP_StackMapTransfer
-- name    : CookPvsNP_StackMapTransfer
-- status  : Definition
-- author  : @arexychen
-- created : 2026-10-02T13:35:49.918893+00:00
-- url     : https://prove2.me/theorems/92dd8765-0aef-4d47-bda2-70a102c6245b
-- title:
--   CookPvsNP StackMapTransfer
-- statement:
--   A transfer program applying a fixed finite-alphabet letter map to every moved symbol.
-- source:
--   New auxiliary formalization for the ResourceScheduling Q2 reduction. The target is the unchanged CookPvsNP one-tape machine model, following Cook, The P versus NP problem, Clay Mathematics Institute (2000), Appendix. This explicit finite-column stack compiler and its simulation lemmas are new contributions, not numbered claims from Cook or the scheduling source paper.

import Definitions.Def_CookPvsNP_StackMacros

set_option autoImplicit false
namespace CookPvsNP

def mapTransferAct {K A : Type} [DecidableEq K] (src : K) (targets : K → Bool)
    (f : A → A) (h : K → Option A) (k : K) : StackAct A :=
  if k = src then .pop else if targets k then
    match h src with | some a => .push (f a) | none => .keep
  else .keep

def mapTransferProg {K A : Type} [DecidableEq K] (src : K) (targets : K → Bool)
    (f : A → A) : StackProg K A :=
  .loop (fun h => (h src).isSome) (.act (mapTransferAct src targets f))

def mapTransferStore {K A : Type} [DecidableEq K] (src : K) (targets : K → Bool)
    (f : A → A) (s : K → List A) (k : K) : List A :=
  if k = src then [] else if targets k then (s src).reverse.map f ++ s k else s k

end CookPvsNP


