-- Prove2me | Definitions.Def_QAlgorithms_Defs_IdealArithmetic
-- name    : QAlgorithms_Defs_IdealArithmetic
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T19:14:10.555174+00:00
-- url     : https://prove2.me/theorems/a2b1dc9b-279e-4aa7-b50c-d598cae55820
-- title:
--   IdealArithmetic
-- statement:
--   IdealArithmetic
-- source:
--   Source references and exact conventions are recorded in each declaration docstring. algorithms\QAlgorithms\Defs\IdealArithmetic.lean

import Definitions.Def_QAlgorithms_Defs_SingleQubitCert
noncomputable section

open scoped Matrix ComplexConjugate ENNReal ComplexOrder

namespace QAlgorithms

/-- Operational helper ArithmeticInstruction for the source construction. Source: arxiv-2601.18773v1 PDF p.7; arxiv-2601.18773v1 PDF p.8; arxiv-2601.18773v1 PDF p.9; arxiv-2601.18773v1 PDF p.10. -/
inductive ArithmeticInstruction where
  | constant (dst : ℕ) (value : ℝ)
  | read (dst src : ℕ)
  | add (dst a b : ℕ)
  | mul (dst a b : ℕ)
  | div (dst a b : ℕ)
  | sqrt (dst a : ℕ)
  | acos (dst a : ℕ)

/-- Operational helper ArithmeticInstruction.eval for the source construction. Source: arxiv-2601.18773v1 PDF p.7; arxiv-2601.18773v1 PDF p.8; arxiv-2601.18773v1 PDF p.9; arxiv-2601.18773v1 PDF p.10. -/
def ArithmeticInstruction.eval (mem : ℕ → ℝ) : ArithmeticInstruction → Option (ℕ → ℝ)
  | .constant dst v => some (Function.update mem dst v)
  | .read dst src => some (Function.update mem dst (mem src))
  | .add dst a b => some (Function.update mem dst (mem a + mem b))
  | .mul dst a b => some (Function.update mem dst (mem a * mem b))
  | .div dst a b => if mem b = 0 then none else some (Function.update mem dst (mem a / mem b))
  | .sqrt dst a => if mem a < 0 then none else some (Function.update mem dst (Real.sqrt (mem a)))
  | .acos dst a => if |mem a| ≤ 1 then some (Function.update mem dst (Real.arccos (mem a))) else none

/-- Count concrete elementary arithmetic and memory accesses at unit cost as in Lemma 4, actual exact quantum gates/preparations, and the single supplied decoding query. Source: arxiv-2601.18773v1 PDF p.7; arxiv-2601.18773v1 PDF p.8; arxiv-2601.18773v1 PDF p.9; arxiv-2601.18773v1 PDF p.10. -/
inductive ArithmeticProgram where
  | done
  | step (op : ArithmeticInstruction) (rest : ArithmeticProgram)
  | loop (count : ℕ) (body rest : ArithmeticProgram)

/-- Execute the finite arithmetic/memory instruction list and loop controls on the known coefficient inputs. Source: arxiv-2601.18773v1 PDF p.7; arxiv-2601.18773v1 PDF p.8. -/
def ArithmeticProgram.eval : ArithmeticProgram → (ℕ → ℝ) → Option (ℕ → ℝ)
  | .done, mem => some mem
  | .step op rest, mem => (op.eval mem).bind rest.eval
  | .loop count body rest, mem =>
      ((List.range count).foldl
        (fun st _ => st.bind body.eval) (some mem)).bind rest.eval

/-- Count arithmetic/memory operations along the same evaluation, including loop iterations. Source: arxiv-2601.18773v1 PDF p.7; arxiv-2601.18773v1 PDF p.8. -/
def ArithmeticProgram.cost : ArithmeticProgram → (ℕ → ℝ) → ℕ
  | .done, _ => 0
  | .step op rest, mem => 1 + ((op.eval mem).map rest.cost).getD 0
  | .loop count body rest, mem =>
      let execution := (List.range count).foldl
        (fun st _ => match st.1 with
          | none => st
          | some m => (body.eval m, st.2 + body.cost m)) (some mem, 0)
      execution.2 + (execution.1.map rest.cost).getD 0

/-- Sanity test. Source: arxiv-2601.18773v1 PDF p.7; arxiv-2601.18773v1 PDF p.8; arxiv-2601.18773v1 PDF p.9; arxiv-2601.18773v1 PDF p.10. -/
example (mem : ℕ → ℝ) : ArithmeticProgram.done.eval mem = some mem ∧
    ArithmeticProgram.done.cost mem = 0 := ⟨rfl, rfl⟩

/-- Sanity test. Source: arxiv-2601.18773v1 PDF p.7; arxiv-2601.18773v1 PDF p.8; arxiv-2601.18773v1 PDF p.9; arxiv-2601.18773v1 PDF p.10. -/
example (mem : ℕ → ℝ) : (ArithmeticProgram.step (.read 0 1) .done).cost mem = 1 := rfl

/-- Sanity test. Source: arxiv-2601.18773v1 PDF p.7; arxiv-2601.18773v1 PDF p.8; arxiv-2601.18773v1 PDF p.9; arxiv-2601.18773v1 PDF p.10. -/
example (mem : ℕ → ℝ) (h : mem 2 = 0) :
    (ArithmeticProgram.step (.div 0 1 2) .done).eval mem = none := by
  simp [ArithmeticProgram.eval, ArithmeticInstruction.eval, h]

end QAlgorithms


