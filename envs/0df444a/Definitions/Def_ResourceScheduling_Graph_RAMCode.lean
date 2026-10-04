-- Prove2me | Definitions.Def_ResourceScheduling_Graph_RAMCode
-- name    : ResourceScheduling_Graph_RAMCode
-- status  : Definition
-- author  : @arexychen
-- created : 2026-10-02T15:09:02.867105+00:00
-- url     : https://prove2.me/theorems/a9a66aa5-4670-47d8-a4af-dac15bbbc7e0
-- title:
--   ResourceScheduling Graph RAMCode
-- statement:
--   A structured register language, its semantics, its finite-stack compiler, exact cost expressions, and a syntactic loop-counter discipline.
-- source:
--   New auxiliary formalization for the ResourceScheduling Q2 reduction. The target is the unchanged CookPvsNP one-tape machine model, following Cook, The P versus NP problem, Clay Mathematics Institute (2000), Appendix. This explicit finite-column stack compiler and its simulation lemmas are new contributions, not numbered claims from Cook or the scheduling source paper.

import Definitions.Def_ResourceScheduling_Graph_RAMArithmetic
import Definitions.Def_ResourceScheduling_Graph_RAMParse

set_option autoImplicit false
namespace ResourceScheduling.Graph
open CookPvsNP

/-- A structured register language. Loop counters are decremented before the body. -/
inductive RAMCode (V : Type) where
  | skip
  | zero (v : V)
  | inc (v : V)
  | dec (v : V)
  | copy (i dst : V) (h : i ≠ dst)
  | add (i dst : V) (h : i ≠ dst)
  | length (dst : V)
  | sub (i j dst : V)
  | mul (i j dst : V) (h : j ≠ dst)
  | bit (i dst : V)
  | emit (v : V)
  | parse (t good : V) (h : t ≠ good)
  | seq (p q : RAMCode V)
  | branch (v : V) (p q : RAMCode V)
  | loop (v : V) (p : RAMCode V)

namespace RAMCode

def eval {V : Type} [DecidableEq V] : RAMCode V → RAMState V → RAMState V
  | .skip, s => s
  | .zero v, s => s.set v 0
  | .inc v, s => s.set v (s.val v + 1)
  | .dec v, s => s.set v (s.val v - 1)
  | .copy i v _, s => s.set v (s.val i)
  | .add i v _, s => s.set v (s.val i + s.val v)
  | .length v, s => s.set v s.word.length
  | .sub i j v, s => s.set v (s.val i - s.val j)
  | .mul i j v _, s => s.set v (s.val i * s.val j)
  | .bit i v, s => s.set v (if s.word.getD (s.val i) .sep = .one then 1 else 0)
  | .emit v, s => { s with out := .sep :: (List.replicate (s.val v) .one ++ s.out) }
  | .parse t good _, s => ramParseState t good s
  | .seq p q, s => q.eval (p.eval s)
  | .branch v p q, s => if 0 < s.val v then p.eval s else q.eval s
  | .loop v p, s => ((fun s => p.eval (s.set v (s.val v - 1)))^[s.val v]) s

def code {V : Type} [DecidableEq V] : RAMCode V → StackProg (RAMWire V) Letter
  | .skip => ramSkip
  | .zero v => ramZero v
  | .inc v => ramInc v
  | .dec v => ramDec v
  | .copy i v _ => ramAssign (ramReg i) v
  | .add i v _ => ramAppend (ramReg i) v
  | .length v => ramAssign ramInput v
  | .sub i j v => ramSub i j v
  | .mul i j v h => ramMul i j v h
  | .bit i v => ramReadBit i v
  | .emit v => ramEmit v
  | .parse t good _ => ramParse t good
  | .seq p q => p.code.seq q.code
  | .branch v p q => .branch (fun h => (h (ramReg v)).isSome) p.code q.code
  | .loop v p => .loop (fun h => (h (ramReg v)).isSome) ((ramDec v).seq p.code)

def cost {V : Type} [DecidableEq V] : RAMCode V → RAMState V → ℕ
  | .skip, _ => 1
  | .zero v, s => 3 * s.val v + 1
  | .inc _, _ => 1
  | .dec _, _ => 1
  | .copy i v _, s => 3 * s.val v + 6 * s.val i + 5
  | .add i _ _, s => 6 * s.val i + 3
  | .length v, s => 3 * s.val v + 6 * s.word.length + 5
  | .sub i j v, s => 9 * s.val i + 9 * s.val j + 3 * s.val v + 13
  | .mul i j v _, s => (6 * s.val j + 13) * s.val i + 3 * s.val v + 7
  | .bit i v, s => 9 * s.word.length + 9 * s.val i + 3 * s.val v + 17
  | .emit v, s => 9 * s.val v + 7
  | .parse t good _, s => 3 * s.val t + 3 * s.val good + 3 * s.word.length + 7
  | .seq p q, s => p.cost s + 1 + q.cost (p.eval s)
  | .branch _ p q, s => 1 + max (p.cost s) (q.cost s)
  | .loop v p, s => stackLoopCost (fun s => p.eval (s.set v (s.val v - 1)))
      (fun s => 1 + 1 + p.cost (s.set v (s.val v - 1))) (s.val v) s

def writes {V : Type} [DecidableEq V] : RAMCode V → V → Bool
  | .skip, _ | .emit _, _ => false
  | .zero v, j | .inc v, j | .dec v, j | .copy _ v _, j | .add _ v _, j |
    .length v, j | .sub _ _ v, j | .mul _ _ v _, j | .bit _ v, j => decide (j = v)
  | .parse t good _, j => decide (j = t ∨ j = good)
  | .seq p q, j | .branch _ p q, j => p.writes j || q.writes j
  | .loop v p, j => decide (j = v) || p.writes j

def Valid {V : Type} [DecidableEq V] : RAMCode V → Prop
  | .seq p q | .branch _ p q => p.Valid ∧ q.Valid
  | .loop v p => p.Valid ∧ p.writes v = false
  | _ => True

end RAMCode
end ResourceScheduling.Graph


