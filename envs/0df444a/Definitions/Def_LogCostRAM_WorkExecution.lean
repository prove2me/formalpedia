-- Prove2me | Definitions.Def_LogCostRAM_WorkExecution
-- name    : LogCostRAM_WorkExecution
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-27T03:59:04.921948+00:00
-- url     : https://prove2.me/theorems/7f648e1d-a4cd-52f8-9819-04193d4fa9df
-- title:
--   Exact log-cost execution of structured RAM routines
-- statement:
--   Exact log-cost accounting for structured RAM routines.
--
--   For tapes $\tau$, a bound $J$ on the bit length of every static field and jump label of a compiled routine, a structured routine $c$ and stores $s,t$, the judgement $\mathrm{WExec}(\tau,J,c,s,t,k)$ states that running $c$ from $s$ ends in $t$ and that the total cost charged by the published machine is at most $k$. Each primitive operation is charged exactly what `Program.step` charges: one plus the bit lengths of the addresses used and of the values read or written. A conditional jump on cells $a,b$ is charged
--   $$1+|a|+|b|+|s(a)|+|s(b)|+J,$$
--   and unconditional jumps read cell $0$ twice.
--
--   This refines the step-counting judgement `Exec`, which converts steps to cost through one global word width. The exact judgement is needed when a routine manipulates words whose sizes vary widely, for instance when simulating an arbitrary program whose memory may contain very long words.
--
--   **Formalization Note** `Op.cost` mirrors the work increments of `TargetedSamplers.Program.step`; `staticWidth` is the largest bit length of an instruction field of a program.
-- source:
--   Engineering definition supporting the formalization of T. Koana and S. Kumabe, Breaking the 2^n barrier for directed hamiltonicity (STOC 2027 submission #811), Theorem 1 and Section 2 (PDF pp. 2-5), on the log-cost RAM of Def_TargetedSamplers_Machine.

import Definitions.Def_LogCostRAM_StructuredExecution

set_option autoImplicit false

namespace TargetedSamplers.Structured.Work

/-!
# Exact log-cost accounting for structured RAM routines

`Exec` (in `Def_LogCostRAM_StructuredExecution`) counts primitive steps and converts them to
log-cost through one global word-width bound. `WExec τ J c s t k` instead charges every executed
primitive instruction exactly the cost charged by `TargetedSamplers.Program.step`: one plus the
bit lengths of the addresses used and of the values read or written. The jump labels produced by
`Cmd.compile` are only bounded: `J` is an upper bound on the bit length of every jump label (and
of every static operand) of the compiled program. Unconditional jumps are `jle 0 0 target`, so
they read cell `0` twice. `k` is an upper bound on the accumulated cost.
-/

/-- The exact cost charged by `Program.step` for a primitive operation at store `s`. -/
def Op.cost (τ : Tapes) (s : Store) : Op → ℕ
  | .const d c => 1 + d.size + c.size
  | .add d a b => 1 + d.size + a.size + b.size + (s.mem a).size + (s.mem b).size +
      (s.mem a + s.mem b).size
  | .sub d a b => 1 + d.size + a.size + b.size + (s.mem a).size + (s.mem b).size +
      (s.mem a - s.mem b).size
  | .load d a => 1 + d.size + a.size + (s.mem a).size + (s.mem (s.mem a)).size
  | .store a b => 1 + a.size + b.size + (s.mem a).size + (s.mem b).size
  | .input d a => 1 + d.size + a.size + (s.mem a).size + (bitVal τ.input[s.mem a]?).size
  | .coin d a => 1 + d.size + a.size + (s.mem a).size + (bitVal τ.coins[s.mem a]?).size
  | .output a => 1 + a.size + (s.mem a).size

/-- Upper bound on the cost of a conditional jump `jle a b target` with `target.size ≤ J`. -/
def jumpCost (J : ℕ) (s : Store) (a b : ℕ) : ℕ :=
  1 + a.size + b.size + (s.mem a).size + (s.mem b).size + J

/-- Big-step execution with an upper bound `k` on the exact log-cost. -/
inductive WExec (τ : Tapes) (J : ℕ) : Cmd → Store → Store → ℕ → Prop
  | skip (s) : WExec τ J .skip s s 0
  | op (s p) : WExec τ J (.op p) s (p.eval τ s) (Op.cost τ s p)
  | seq {x y s m t u v} : WExec τ J x s m u → WExec τ J y m t v → WExec τ J (.seq x y) s t (u+v)
  | yes {a b y n s t k} : s.mem a ≤ s.mem b → WExec τ J y s t k →
      WExec τ J (.branch a b y n) s t (jumpCost J s a b + k)
  | no {a b y n s t k} : ¬s.mem a ≤ s.mem b → WExec τ J n s t k →
      WExec τ J (.branch a b y n) s t (jumpCost J s a b + k + jumpCost J t 0 0)
  | done {a b body s} : s.mem a ≤ s.mem b → WExec τ J (.whileGt a b body) s s (jumpCost J s a b)
  | again {a b body s m t k j} : ¬s.mem a ≤ s.mem b → WExec τ J body s m k →
      WExec τ J (.whileGt a b body) m t j →
      WExec τ J (.whileGt a b body) s t (jumpCost J s a b + k + jumpCost J m 0 0 + j)
  | mono {c s t k k'} : WExec τ J c s t k → k ≤ k' → WExec τ J c s t k'

/-- The static numbers of an operation: its cell operands and its literal. -/
def Op.fields : Op → List ℕ
  | .const d c => [d, c]
  | .add d a b => [d, a, b]
  | .sub d a b => [d, a, b]
  | .load d a => [d, a]
  | .store a b => [a, b]
  | .input d a => [d, a]
  | .coin d a => [d, a]
  | .output a => [a]

/-- Every static number of a routine (operation fields and comparison cells) has bit length at
most `J`. -/
def Cmd.FieldsFit (J : ℕ) : Cmd → Prop
  | .skip => True
  | .op p => ∀ x ∈ Op.fields p, x.size ≤ J
  | .seq x y => Cmd.FieldsFit J x ∧ Cmd.FieldsFit J y
  | .branch a b yes no => a.size ≤ J ∧ b.size ≤ J ∧ Cmd.FieldsFit J yes ∧ Cmd.FieldsFit J no
  | .whileGt a b body => a.size ≤ J ∧ b.size ≤ J ∧ Cmd.FieldsFit J body

end TargetedSamplers.Structured.Work

namespace TargetedSamplers.Structured.Work

/-- Bit length of the numerical fields of an instruction. -/
def fieldWidth : Instr → ℕ
  | .const a b | .load a b | .store a b | .readInput a b | .readCoin a b => max a.size b.size
  | .add a b c | .monus a b c | .jle a b c | .query a b c => max a.size (max b.size c.size)
  | .output a | .inputLength a | .readWitness a => a.size
  | .outputBot | .halt => 0

/-- The largest bit length of a numerical field of a finite program (at least `2`). -/
def staticWidth : Program → ℕ
  | [] => 2
  | i :: p => max (fieldWidth i) (staticWidth p)

end TargetedSamplers.Structured.Work


