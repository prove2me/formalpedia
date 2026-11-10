-- Prove2me | Definitions.Def_IntegerMatrixMortality_FixedImage_TwoCounterMachine
-- name    : IntegerMatrixMortality_FixedImage_TwoCounterMachine
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T14:28:22.915808+00:00
-- url     : https://prove2.me/theorems/e2a2922f-ad28-4553-8f5f-c8f863384cdc
-- title:
--   Two-counter machines with arbitrary jump destinations
-- statement:
--   A machine instruction increments one selected natural counter and jumps, or tests that counter, taking a specified zero branch unchanged and a specified positive branch after decrementing. The other counter is unchanged. Both branch destinations are arbitrary states. A halt instruction has no successor. A configuration is (q,c₀,c₁). For a machine M, the halting predicate used by this paper is
--
--   $$\operatorname{Halts}_M(q,c_0,c_1)\iff\exists u,v\in\mathbb N,\quad(q,c_0,c_1)\longrightarrow_M^*(278,u,v).$$
--
--   The distinguished state is 278 throughout this development. Only the concrete machines below are used with this designated-halt predicate. This interface preserves the source's jumps and nonzero input convention.
-- source:
--   Thanin Quartz, Ivan O. Shevchenko, Hans De Sterck, Jun Liu, STOC 2027 submission #1062 (October 2026), §4.1, PDF p. 6 / printed p. 4

import Mathlib

set_option autoImplicit false

namespace IntegerMatrixMortality.FixedImage
inductive Counter where
  | zero | one
  deriving DecidableEq, Repr

inductive MachineInstruction where
  | inc (counter : Counter) (next : ℕ)
  | dec (counter : Counter) (positive zeroDest : ℕ)
  | halt
  deriving DecidableEq, Repr

abbrev MachineConfig := ℕ × ℕ × ℕ
abbrev TwoCounterMachine := ℕ → MachineInstruction

def machineNext (M : TwoCounterMachine) (x : MachineConfig) : Option MachineConfig :=
  match M x.1 with
  | .halt => none
  | .inc .zero r => some (r, x.2.1 + 1, x.2.2)
  | .inc .one r => some (r, x.2.1, x.2.2 + 1)
  | .dec .zero r s => if x.2.1 = 0 then some (s, x.2.1, x.2.2)
      else some (r, x.2.1 - 1, x.2.2)
  | .dec .one r s => if x.2.2 = 0 then some (s, x.2.1, x.2.2)
      else some (r, x.2.1, x.2.2 - 1)

def machineHalts (M : TwoCounterMachine) (x : MachineConfig) : Prop :=
  ∃ u v : ℕ, Relation.ReflTransGen (fun a b => machineNext M a = some b) x (278, u, v)

end IntegerMatrixMortality.FixedImage


