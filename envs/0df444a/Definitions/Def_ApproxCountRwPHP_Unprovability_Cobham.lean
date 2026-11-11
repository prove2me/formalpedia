-- Prove2me | Definitions.Def_ApproxCountRwPHP_Unprovability_Cobham
-- name    : ApproxCountRwPHP_Unprovability_Cobham
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T21:55:59.733845+00:00
-- url     : https://prove2.me/theorems/33b4e13e-6136-41e9-8058-0f145b2d6cd7
-- title:
--   Bounded oracle program codes
-- statement:
--   Program codes have a fixed arity. They contain string primitives, oracle calls, projections, composition, and limited recursion on notation. Every recursion node includes a previously constructed bounding code independent of the recursive answer. Its standard evaluator truncates the proposed result to this bound at the initial stage and at every step.
--
--   $$F(wb,\bar x)=\operatorname{take}_{|B(wb,\bar x)|} H(w,b,F(w,\bar x),\bar x).$$
--
--   The basis includes empty strings, bit append, predecessor, concatenation and the repetition operation from Li's string presentation, as well as fixed polynomial-time helpers. The extra truncation makes every syntactically admitted code total and polynomially bounded, including inadequate proposed bounds. Adequately bounded source programs retain their values. This is a concrete program syntax, with no assumed-correctness field.
--
--   The fixed polynomial-time helpers include the canonical-numeral test used to distinguish numerical domains from arbitrary binary strings.
-- source:
--   Oliver Korten, Jiatu Li, Igor Oliveira, Hanlin Ren, STOC 2027 submission #1023 (October 2026), §2.2 (basis: Li25, §2.1.1, printed 18 / PDF 28, https://eccc.weizmann.ac.il/report/2025/086/download/), printed p. 13–14, PDF p. 15–16; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1023.pdf#page=15–16

import Definitions.Def_ApproxCountRwPHP_Unprovability_Strings

namespace ApproxCountRwPHP.Unprovability

/-! A Cobham-style basis for the language described in §2.2, PDF 15–16.
The string basis follows Li25, §2.1.1, printed 18 / PDF 28 (including
its repetition operation #): https://eccc.weizmann.ac.il/report/2025/086/download/.
Composition and limited recursion on notation are syntax constructors. The
recursion bound is itself an earlier code, independent of the recursive answer.
The rightmost-bit recursion scans a word from its most significant bit.
The smash operation has length `|x|*|y|+1`, not numeric multiplication of lengths
as its output value. All the additional primitives below run in polynomial time.
This implements the bounded-recursion presentation, not unbounded recursion. -/
inductive Primitive : ℕ → Type
  | empty : Primitive 0
  | append (b : Bool) : Primitive 1
  | pred : Primitive 1
  | concat : Primitive 2
  | repeat : Primitive 2
  | smash : Primitive 2
  | cond : Primitive 3
  | length : Primitive 1
  | less : Primitive 2
  | equal : Primitive 2
  | isNumeral : Primitive 1
  | pow2length : Primitive 1
  | onesLength : Primitive 1

def Primitive.eval : {n : ℕ} → Primitive n → (Fin n → BitString) → BitString
  | _, .empty, _ => []
  | _, .append b, xs => xs 0 ++ [b]
  | _, .pred, xs => (xs 0).take ((xs 0).length - 1)
  | _, .concat, xs => xs 0 ++ xs 1
  | _, .repeat, xs => (List.replicate (xs 1).length (xs 0)).flatten
  | _, .smash, xs => true :: List.replicate ((xs 0).length * (xs 1).length) false
  | _, .cond, xs => if (xs 0).isEmpty then xs 1 else xs 2
  | _, .length, xs => numeral (xs 0).length
  | _, .less, xs => truth (number (xs 0) < number (xs 1))
  | _, .equal, xs => truth (xs 0 == xs 1)
  | _, .isNumeral, xs => truth (ApproxCountRwPHP.Unprovability.isNumeral (xs 0))
  | _, .pow2length, xs => true :: List.replicate (xs 0).length false
  | _, .onesLength, xs => unary (xs 0).length

/-- `O` is the family of primitive oracle symbols, indexed by arity. -/
inductive CobhamCode (O : ℕ → Type) : ℕ → Type
  | primitive {n} (p : Primitive n) : CobhamCode O n
  | oracle {n} (o : O n) : CobhamCode O n
  | projection (n : ℕ) (i : Fin n) : CobhamCode O n
  | compose {n k} (f : CobhamCode O k) (gs : Fin k → CobhamCode O n) : CobhamCode O n
  | recursion {n} (base : CobhamCode O n) (step : CobhamCode O (n + 3))
      (bound : CobhamCode O (n + 1)) : CobhamCode O (n + 1)

/-- Total standard semantics. The bound is applied at the base and every step,
so even codes with an inadequate proposed bound remain polynomially bounded. -/
def CobhamCode.eval {O : ℕ → Type} (oracle : ∀ n, O n → (Fin n → BitString) → BitString) :
    {n : ℕ} → CobhamCode O n → (Fin n → BitString) → BitString
  | _, .primitive p, xs => p.eval xs
  | _, .oracle o, xs => oracle _ o xs
  | _, .projection _ i, xs => xs i
  | _, .compose f gs, xs => f.eval oracle (fun i => (gs i).eval oracle xs)
  | _, .recursion base step bound, xs =>
      let params := fun i => xs i.succ
      let initial := boundString (base.eval oracle params) (bound.eval oracle (Fin.cons [] params))
      ((xs 0).foldl (fun state bit =>
        let wordPrefix := state.1 ++ [bit]
        let value := step.eval oracle (Fin.cons state.1 (Fin.cons [bit] (Fin.cons state.2 params)))
        (wordPrefix, boundString value (bound.eval oracle (Fin.cons wordPrefix params))))
        ([], initial)).2

end ApproxCountRwPHP.Unprovability


