-- Prove2me | Definitions.Def_CookPvsNP_StackModel
-- name    : CookPvsNP_StackModel
-- status  : Definition
-- author  : @arexychen
-- created : 2026-10-02T10:45:30.813038+00:00
-- url     : https://prove2.me/theorems/fbbb40cb-c98a-4169-b011-b347b09b03b0
-- title:
--   Finite stack machine and column sweep functions
-- statement:
--   A source instruction reads the finite tuple of stack tops, updates finite control, and keeps, pushes, or pops each stack. The accompanying column functions describe the right and left sweeps. These are definitions, without any assumed compiler theorem.
-- source:
--   New auxiliary formalization for the ResourceScheduling Q2 reduction. The target is the unchanged CookPvsNP one-tape machine model, following Cook, The P versus NP problem, Clay Mathematics Institute (2000), Appendix. This explicit finite-column stack compiler and its simulation lemmas are new contributions, not numbered claims from Cook or the scheduling source paper.

import Definitions.Def_CookPvsNP_defs

set_option autoImplicit false
namespace CookPvsNP

/-- One constant-cost operation on a stack. -/
inductive StackAct (A : Type) where
  | keep
  | push (a : A)
  | pop
  deriving DecidableEq, Fintype

def StackAct.apply {A : Type} : StackAct A → List A → List A
  | .keep, s => s
  | .push a, s => a :: s
  | .pop, s => s.tail

/-- Fixed finite control and a fixed finite family of stacks. A step reads only their tops. -/
structure StackMachine (K A Q : Type) where
  initial : Q
  done : Q → Bool
  next : Q → (K → Option A) → Q × (K → StackAct A)

structure StackCfg (K A Q : Type) where
  state : Q
  store : K → List A

def StackMachine.step {K A Q : Type} (P : StackMachine K A Q)
    (c : StackCfg K A Q) : StackCfg K A Q :=
  if P.done c.state then c else
    let d := P.next c.state (fun k => (c.store k).head?)
    ⟨d.1, fun k => (d.2 k).apply (c.store k)⟩

abbrev StackCol (K A : Type) := K → Option A

def stackZero {K A : Type} : StackCol K A := fun _ => none

/-- A column encoding with explicit blank padding; the width is shared by all stacks. -/
def stackRows {K A : Type} (s : K → List A) (n : ℕ) : List (StackCol K A) :=
  (List.range n).map fun i k => (s k)[i]?

def stackPushCarry {K A : Type} (a : K → StackAct A) : StackCol K A := fun k =>
  match a k with | .push x => some x | _ => none

def stackPushCell {K A : Type} (a : K → StackAct A)
    (carry x : StackCol K A) : StackCol K A := fun k =>
  match a k with | .push _ => carry k | _ => x k

def stackPushNext {K A : Type} (a : K → StackAct A)
    (x : StackCol K A) : StackCol K A := fun k =>
  match a k with | .push _ => x k | _ => none

def stackPopCell {K A : Type} (a : K → StackAct A)
    (carry x : StackCol K A) : StackCol K A := fun k =>
  match a k with | .pop => carry k | _ => x k

def stackPopNext {K A : Type} (a : K → StackAct A)
    (x : StackCol K A) : StackCol K A := fun k =>
  match a k with | .pop => x k | _ => none

/-- The right sweep writes one extra column when it reaches the blank tape. -/
def stackForward {K A : Type} (a : K → StackAct A) :
    StackCol K A → List (StackCol K A) → List (StackCol K A)
  | c, [] => [c]
  | c, x :: xs => stackPushCell a c x :: stackForward a (stackPushNext a x) xs

/-- The left sweep, specified in left-to-right column order. -/
def stackBackward {K A : Type} (a : K → StackAct A) :
    List (StackCol K A) → List (StackCol K A)
  | [] => []
  | x :: xs => stackPopCell a (xs.headD stackZero) x :: stackBackward a xs

def stackRight {K A : Type} (a : K → StackAct A) :
    StackCol K A → List (StackCol K A) → StackCol K A × List (StackCol K A)
  | c, [] => (c, [])
  | c, x :: xs =>
    let z := stackRight a (stackPushNext a x) xs
    (z.1, stackPushCell a c x :: z.2)

def stackLeft {K A : Type} (a : K → StackAct A) :
    StackCol K A → List (StackCol K A) → StackCol K A × List (StackCol K A)
  | c, [] => (c, [])
  | c, x :: xs =>
    let z := stackLeft a x xs
    (z.1, stackPopCell a c x :: z.2)

end CookPvsNP


