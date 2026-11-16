-- Prove2me | Definitions.Def_NCFactorClosure607_Circuits_Supplement_CoeffAlgorithm
-- name    : NCFactorClosure607_Circuits_Supplement_CoeffAlgorithm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T20:07:40.38559+00:00
-- url     : https://prove2.me/theorems/753550b1-ff58-4994-bc8f-04a70a44f7d1
-- title:
--   The coefficient algorithm of Lemma 7.1: substring dynamic program with counted field operations
-- statement:
--   For a circuit $C$ and a word $w=w_0\cdots w_{d-1}$, $\mathrm{coeffAlgo}(C,w)$ returns a field element and a count of field operations.
--
--   1. If $w=\varepsilon$, it evaluates $C$ at $X=0$ (constants are kept, variables become $0$), one operation per addition or multiplication gate.
--   2. If $d\ge1$, it processes the gates in order and computes at every gate the coefficient of every substring $w[a:b]=w_a\cdots w_{b-1}$, $0\le a\le b\le d$, empty substrings included: at a constant $c$, $[w[a:b]]=c$ if $a=b$ and $0$ otherwise; at a variable $x$, $1$ if $b=a+1$ and $w_a=x$, else $0$; at an addition gate the entrywise sum; at a multiplication gate
--   $$[w[a:b]](PQ)=\sum_{t=a}^{b}[w[a:t]]P\,[w[t:b]]Q .$$
--   The answer is the entry $(0,d)$ at the output gate.
--
--   Every field addition and multiplication is counted. This is the procedure whose correctness and cost Lemma 7.1 asserts.
--
--   Each addition or multiplication gate stores its computed interval entries in a finite list. Later gate lookups reuse those field values without recomputing their arithmetic.
-- source:
--   V. Arvind, Pushkar S Joglekar, Factor Closure in Noncommutative Algebraic Complexity, STOC 2027 submission #607 (October 2026), p.17, Lemma 7.1 and its proof; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/607.pdf

import Mathlib
import Definitions.Def_NCFactorClosure607_Circuits_Circuit
import Definitions.Def_NCFactorClosure607_Circuits_Supplement_FormulaExtraction

/-!
# Computing one coefficient of a circuit, with a count of field operations

Arvind–Joglekar, *Factor Closure in Noncommutative Algebraic Complexity*,
STOC 2027 submission #607, Lemma 7.1 and its proof, p.17.

For a word `w = w_0 ⋯ w_{d-1}` with `d ≥ 1`, the algorithm processes the gates of the circuit in
order and computes at every gate the coefficient of every substring `w[a : b] = w_a ⋯ w_{b-1}`
(`0 ≤ a ≤ b ≤ d`, empty substrings included): input gates directly, addition gates entrywise,
and multiplication gates by
`[w[a : b]](PQ) = Σ_{t=a}^{b} [w[a : t]]P · [w[t : b]]Q`. The answer is the entry `(0, d)` of the
output gate. For the empty word the algorithm evaluates the circuit at `X = 0`. Every field
addition and multiplication is counted (the dot products use the counted primitive `dot` of the
formula construction).
-/

namespace NCFactorClosure607.Circuits.Supplement

open NCFactorClosure607.Circuits FormulaExtraction

namespace CoeffAlgorithm

variable {F : Type*} [Field F] {X : Type*} [DecidableEq X]

/-- One gate evaluated at `X = 0`, from the values of the earlier gates, with its count. -/
def gateAtZero (vals : List F) : Gate F X → F × ℕ
  | .const a => (a, 0)
  | .var _ => (0, 0)
  | .add i j => (vals.getD i 0 + vals.getD j 0, 1)
  | .mul i j => (vals.getD i 0 * vals.getD j 0, 1)

/-- Evaluation of the circuit at `X = 0` (the empty-word coefficient), with its count. -/
def evalAtZero (C : Circuit F X) : F × ℕ :=
  let r := C.gates.foldl
    (fun (st : List F × ℕ) g => let v := gateAtZero st.1 g; (st.1 ++ [v.1], st.2 + v.2))
    ([], 0)
  (r.1.getLastD 0, r.2)

/-- The intervals `(a, b)`, `0 ≤ a ≤ b ≤ d`. -/
def intervals (d : ℕ) : List (ℕ × ℕ) :=
  (List.range (d + 1)).flatMap fun b => (List.range (b + 1)).map fun a => (a, b)

/-- The product rule on the interval `(a, b)`: `Σ_{t=a}^{b} P(a, t) Q(t, b)` as a counted dot
product of length `b - a + 1`. -/
def cutSum (P Q : ℕ → ℕ → F) (a b : ℕ) : F × ℕ :=
  dot (b - a + 1) (fun r => P a (a + r.val)) (fun r => Q (a + r.val) b)

/-- Evaluate every interval entry once and store its value. Looking up an entry of the
returned table performs no field arithmetic, so shared circuit gates stay shared. -/
def storeTable (d : ℕ) (entry : ℕ → ℕ → F × ℕ) : (ℕ → ℕ → F) × ℕ :=
  let entries := (intervals d).map fun ab => (ab, entry ab.1 ab.2)
  let values := entries.map fun e => (e.1, e.2.1)
  (fun a b => ((values.find? fun e => e.1 = (a, b)).map Prod.snd).getD 0,
    (entries.map fun e => e.2.2).sum)

/-- One gate of the substring dynamic program for the word `w` of length `d`: the table
`(a, b) ↦ [w[a : b]] (gate)` from the tables `tabs` of the earlier gates, with its count. -/
def gateTable (w : List X) (tabs : List (ℕ → ℕ → F)) : Gate F X → (ℕ → ℕ → F) × ℕ
  | .const c => (fun a b => if a = b then c else 0, 0)
  | .var x => (fun a b => if b = a + 1 ∧ w[a]? = some x then 1 else 0, 0)
  | .add i j =>
      storeTable w.length fun a b =>
        ((tabs.getD i fun _ _ => 0) a b + (tabs.getD j fun _ _ => 0) a b, 1)
  | .mul i j =>
      storeTable w.length fun a b =>
        cutSum (tabs.getD i fun _ _ => 0) (tabs.getD j fun _ _ => 0) a b

/-- The substring tables of all gates in order, with the total count. -/
def tables (w : List X) (C : Circuit F X) : List (ℕ → ℕ → F) × ℕ :=
  C.gates.foldl
    (fun (st : List (ℕ → ℕ → F) × ℕ) g => let r := gateTable w st.1 g; (st.1 ++ [r.1], st.2 + r.2))
    ([], 0)

end CoeffAlgorithm

open CoeffAlgorithm

/-- The coefficient algorithm of Lemma 7.1 (p.17) on the circuit `C` and the word `w`: returns
the computed value of `[w]C` and the number of field operations performed. For `w = ε`
it evaluates `C` at `X = 0`; otherwise it runs the substring dynamic program and returns the
entry `(0, |w|)` of the output gate. -/
def coeffAlgo {F : Type*} [Field F] {X : Type*} [DecidableEq X] (C : Circuit F X)
    (w : List X) : F × ℕ :=
  if w = [] then evalAtZero C
  else
    let r := tables w C
    ((r.1.getLastD fun _ _ => 0) 0 w.length, r.2)

end NCFactorClosure607.Circuits.Supplement


