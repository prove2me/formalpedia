-- Prove2me | Definitions.Def_CookPvsNP_StackRepresentation
-- name    : CookPvsNP_StackRepresentation
-- status  : Definition
-- author  : @arexychen
-- created : 2026-10-02T11:34:30.980759+00:00
-- url     : https://prove2.me/theorems/b2bf49e3-d688-4c73-8ced-b50cc1a3f899
-- title:
--   Padded stack representation and simulation budget
-- statement:
--   A column list represents each stack by its nonblank symbols followed by blank padding. All stacks fit in the common width. The simulation budget is m(2W+m+1) for m instructions from width W. The initial source store puts the input in one designated stack.
-- source:
--   New auxiliary formalization for the ResourceScheduling Q2 reduction. The target is the unchanged CookPvsNP one-tape machine model, following Cook, The P versus NP problem, Clay Mathematics Institute (2000), Appendix. This explicit finite-column stack compiler and its simulation lemmas are new contributions, not numbered claims from Cook or the scheduling source paper.

import Definitions.Def_CookPvsNP_StackCompiler

set_option autoImplicit false
namespace CookPvsNP

def stackPad {A : Type} (s : List A) (n : ℕ) : List (Option A) :=
  s.map some ++ List.replicate (n - s.length) none

/-- No holes occur within any stack, and every stack fits in the common width. -/
def StackRep {K A : Type} (r : List (StackCol K A)) (s : K → List A) : Prop :=
  ∀ k, (s k).length ≤ r.length ∧ r.map (fun x => x k) = stackPad (s k) r.length

def stackTime (width steps : ℕ) : ℕ := steps * (2 * width + steps + 1)

def StackMachine.init {K A Q : Type} [DecidableEq K] (P : StackMachine K A Q)
    (ki : K) (w : List A) : StackCfg K A Q :=
  ⟨P.initial, fun k => if k = ki then w else []⟩

end CookPvsNP


