-- Prove2me | Definitions.Def_IntegerMatrixMortality_FixedImage_ArithmeticProgram
-- name    : IntegerMatrixMortality_FixedImage_ArithmeticProgram
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T14:28:25.037592+00:00
-- url     : https://prove2.me/theorems/3310f632-4764-478d-9ee3-d1ab89e5558e
-- title:
--   Finite partial-map arithmetic programs and the six instructions
-- statement:
--   An arithmetic program is a finite directed multigraph with a finite set of natural state labels and a finite list of edges. Each edge q→r has an actual partial function f:ℕ⇀ℕ. Its operational rule is
--
--   $$(q,n)\longrightarrow(r,k)\iff f(n)=k\text{ on that edge's domain}.$$
--
--   Reachability is the reflexive transitive closure, so a zero-step path is allowed. The six instruction types are Inc(n)=n+1; Test(d,A), the identity on n mod d∈A; Div₂(2a+1)=a; Div₃(3a+2)=a; Con₂(5a+4)=2a+1; and Con₃(5a+4)=3a+2. A test is well formed when d≥1 and A⊆{0,…,d−1}. Division and contraction return no value outside their stated congruence classes.
--
--   These general graph and instruction definitions can be reused independently of the fixed source machine.
-- source:
--   Thanin Quartz, Ivan O. Shevchenko, Hans De Sterck, Jun Liu, STOC 2027 submission #1062 (October 2026), Definition 4.2, PDF p. 7 / printed p. 5; Table 1, PDF p. 8 / printed p. 6

import Mathlib

set_option autoImplicit false

namespace IntegerMatrixMortality.FixedImage
/-- A finite directed multigraph with actual partial counter maps (Definition 4.2). -/
structure ArithmeticEdge where
  source : ℕ
  target : ℕ
  update : ℕ → Option ℕ

structure ArithmeticProgram where
  states : Finset ℕ
  edges : List ArithmeticEdge

abbrev ProgramConfig := ℕ × ℕ

def programStep (P : ArithmeticProgram) (x y : ProgramConfig) : Prop :=
  x.1 ∈ P.states ∧ y.1 ∈ P.states ∧ ∃ e ∈ P.edges,
    e.source = x.1 ∧ e.target = y.1 ∧ e.update x.2 = some y.2

def programReach (P : ArithmeticProgram) := Relation.ReflTransGen (programStep P)

inductive ArithmeticInstruction where
  | inc
  | test (d : ℕ) (allowed : Finset ℕ)
  | div2 | div3 | con2 | con3
  deriving DecidableEq

def instructionUpdate : ArithmeticInstruction → ℕ → Option ℕ
  | .inc, n => some (n+1)
  | .test d A, n => if n % d ∈ A then some n else none
  | .div2, n => if n % 2 = 1 then some (n / 2) else none
  | .div3, n => if n % 3 = 2 then some (n / 3) else none
  | .con2, n => if n % 5 = 4 then some (2 * (n / 5) + 1) else none
  | .con3, n => if n % 5 = 4 then some (3 * (n / 5) + 2) else none

def WellFormedInstruction : ArithmeticInstruction → Prop
  | .test d A => 1 ≤ d ∧ ∀ a ∈ A, a < d
  | _ => True

structure InstructionEdge where
  source : ℕ
  target : ℕ
  instruction : ArithmeticInstruction

end IntegerMatrixMortality.FixedImage


