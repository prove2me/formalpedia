-- Prove2me | Definitions.Def_CookPvsNP_StackProgram
-- name    : CookPvsNP_StackProgram
-- status  : Definition
-- author  : @arexychen
-- created : 2026-10-02T12:12:30.79011+00:00
-- url     : https://prove2.me/theorems/cc95191e-e53e-4076-a16e-145eea8099f0
-- title:
--   CookPvsNP StackProgram
-- statement:
--   Structured finite-stack programs with sequence, branch, and loop; finite labels, their machine, exact source executions, and traces.
-- source:
--   New auxiliary formalization for the ResourceScheduling Q2 reduction. The target is the unchanged CookPvsNP one-tape machine model, following Cook, The P versus NP problem, Clay Mathematics Institute (2000), Appendix. This explicit finite-column stack compiler and its simulation lemmas are new contributions, not numbered claims from Cook or the scheduling source paper.

import Definitions.Def_CookPvsNP_StackRepresentation

set_option autoImplicit false
namespace CookPvsNP

/-- Structured finite stack programs; tests and actions inspect only the finite tuple of tops. -/
inductive StackProg (K A : Type) where
  | act (f : (K → Option A) → K → StackAct A)
  | seq (p q : StackProg K A)
  | branch (test : (K → Option A) → Bool) (p q : StackProg K A)
  | loop (test : (K → Option A) → Bool) (body : StackProg K A)

namespace StackProg
variable {K A : Type}

def Label : StackProg K A → Type
  | .act _ => Bool
  | .seq p q => p.Label ⊕ q.Label
  | .branch _ p q => Option (p.Label ⊕ q.Label)
  | .loop _ p => Option (Option p.Label)

noncomputable instance (p : StackProg K A) : Fintype p.Label := by
  induction p with
  | act _ => exact inferInstanceAs (Fintype Bool)
  | seq p q hp hq => exact @instFintypeSum p.Label q.Label hp hq
  | branch _ p q hp hq => exact @instFintypeOption _ (@instFintypeSum _ _ hp hq)
  | loop _ p hp => exact @instFintypeOption _ (@instFintypeOption _ hp)

noncomputable instance (p : StackProg K A) : DecidableEq p.Label := Classical.decEq _

def entry : (p : StackProg K A) → p.Label
  | .act _ => false
  | .seq p _ => .inl p.entry
  | .branch _ _ _ => none
  | .loop _ _ => none

def done : (p : StackProg K A) → p.Label → Bool
  | .act _ => fun q => q
  | .seq p q => fun l => match l with
    | .inl _ => false
    | .inr l => q.done l
  | .branch _ p q => fun l => match l with
    | none => false
    | some (.inl l) => p.done l
    | some (.inr l) => q.done l
  | .loop _ _ => fun l => match l with
    | some none => true
    | _ => false

def next : (p : StackProg K A) → p.Label → (K → Option A) → p.Label × (K → StackAct A)
  | .act f, _, h => (true, f h)
  | .seq p q, .inl l, h =>
    if p.done l then (.inr q.entry, fun _ => .keep) else
      let z := p.next l h
      (.inl z.1, z.2)
  | .seq _ q, .inr l, h =>
    let z := q.next l h
    (.inr z.1, z.2)
  | .branch test p q, none, h =>
    (if test h then some (.inl p.entry) else some (.inr q.entry), fun _ => .keep)
  | .branch _ p _, some (.inl l), h =>
    let z := p.next l h
    (some (.inl z.1), z.2)
  | .branch _ _ q, some (.inr l), h =>
    let z := q.next l h
    (some (.inr z.1), z.2)
  | .loop test p, none, h =>
    (if test h then some (some p.entry) else some none, fun _ => .keep)
  | .loop _ _, some none, _ => (some none, fun _ => .keep)
  | .loop _ p, some (some l), h =>
    if p.done l then (none, fun _ => .keep) else
      let z := p.next l h
      (some (some z.1), z.2)

def machine (p : StackProg K A) : StackMachine K A p.Label := ⟨p.entry, p.done, p.next⟩

def applyAct (f : (K → Option A) → K → StackAct A) (s : K → List A) : K → List A :=
  fun k => (f (fun j => (s j).head?) k).apply (s k)

/-- Source executions count every atom, guard, and transfer between structured subprograms. -/
inductive Exec : StackProg K A → (K → List A) → (K → List A) → ℕ → Prop
  | act (f) (s) : Exec (.act f) s (applyAct f s) 1
  | seq {p q s t u n m} : Exec p s t n → Exec q t u m → Exec (.seq p q) s u (n + 1 + m)
  | branchTrue {test p q s t n} : test (fun k => (s k).head?) = true →
      Exec p s t n → Exec (.branch test p q) s t (1 + n)
  | branchFalse {test p q s t n} : test (fun k => (s k).head?) = false →
      Exec q s t n → Exec (.branch test p q) s t (1 + n)
  | loopFalse {test p s} : test (fun k => (s k).head?) = false → Exec (.loop test p) s s 1
  | loopTrue {test p s t u n m} : test (fun k => (s k).head?) = true →
      Exec p s t n → Exec (.loop test p) t u m → Exec (.loop test p) s u (1 + n + 1 + m)

end StackProg

/-- A finite source trace containing no transition out of a halting source configuration. -/
inductive StackTrace {K A Q : Type} (P : StackMachine K A Q) :
    ℕ → StackCfg K A Q → StackCfg K A Q → Prop
  | refl (c) : StackTrace P 0 c c
  | cons {n c d} : P.done c.state = false → StackTrace P n (P.step c) d →
      StackTrace P (n + 1) c d

end CookPvsNP


