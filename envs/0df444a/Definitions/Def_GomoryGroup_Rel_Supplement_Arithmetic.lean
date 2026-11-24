-- Prove2me | Definitions.Def_GomoryGroup_Rel_Supplement_Arithmetic
-- name    : GomoryGroup_Rel_Supplement_Arithmetic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T01:19:13.052916+00:00
-- url     : https://prove2.me/theorems/5458ca98-2615-4199-8b0f-b2638ccf8e1b
-- title:
--   p. 262 — charged arithmetic traces, separate from table access
-- statement:
--   An **arithmetic trace** records the operations used by the computation of THEOREM 3. Real addition, subtraction and comparison, and group addition and subtraction, each contribute one event. Incrementing a stored witness coordinate and copying one output coordinate are also charged once. A computation returns its result and its chronological trace; its cost is
--   $$\operatorname{steps}(R)=|\operatorname{trace}(R)|.$$
--
--   Sequential composition concatenates traces. Table reads/writes, equality of group labels, finite enumeration, allocation and loop/index bookkeeping do not contribute arithmetic events. The actual tabulation procedure permits no input answer table and performs real/group arithmetic only through the named primitives. This interface is reusable for arithmetic-operation counts over finite groups.
--
--   **Formalization Note** This is an arithmetic-operation model, not a bit-complexity or total-running-time model. In particular it distinguishes the two lookups from the arithmetic operations in the source's p. 264 recurrence tally.
-- source:
--   Gomory, On the relation between integer and noninteger solutions to linear programs, Proc. Natl. Acad. Sci. USA 53 (1965), p. 262, arithmetic steps following THEOREM 3; p. 264, recursion tally following (8)

import Mathlib

set_option autoImplicit false

namespace GomoryGroup.Rel.Supplement

/-- Arithmetic events, distinct from table reads/writes and loop/index bookkeeping.
Witness increments and output-coordinate copies are charged as well. -/
inductive ArithmeticStep where
  | realAdd | realSub | realCompare | groupAdd | groupSub | witnessSucc | outputCopy
  deriving DecidableEq, Repr

/-- A computation result with its chronological arithmetic-event trace. -/
structure ArithmeticRun (α : Type) where
  result : α
  trace : List ArithmeticStep

namespace ArithmeticRun

def pure {α : Type} (x : α) : ArithmeticRun α := ⟨x, []⟩

def bind {α β : Type} (x : ArithmeticRun α) (f : α → ArithmeticRun β) : ArithmeticRun β :=
  let y := f x.result
  ⟨y.result, x.trace ++ y.trace⟩

instance : Monad ArithmeticRun where
  pure := pure
  bind := bind

def steps {α : Type} (x : ArithmeticRun α) : ℕ := x.trace.length

noncomputable def addReal (x y : ℝ) : ArithmeticRun ℝ := ⟨x + y, [.realAdd]⟩
noncomputable def subReal (x y : ℝ) : ArithmeticRun ℝ := ⟨x - y, [.realSub]⟩
noncomputable def lessReal (x y : ℝ) : ArithmeticRun Bool :=
  ⟨decide (x < y), [.realCompare]⟩

def addGroup {G : Type} [Add G] (x y : G) : ArithmeticRun G := ⟨x + y, [.groupAdd]⟩
def subGroup {G : Type} [Sub G] (x y : G) : ArithmeticRun G := ⟨x - y, [.groupSub]⟩
def succWitness (x : ℕ) : ArithmeticRun ℕ := ⟨x + 1, [.witnessSucc]⟩
def copyOutput (x : ℕ) : ArithmeticRun ℕ := ⟨x, [.outputCopy]⟩

end ArithmeticRun

end GomoryGroup.Rel.Supplement


