-- Prove2me | Definitions.Def_MDPComplexity_CircuitValue_Circuit
-- name    : MDPComplexity_CircuitValue_Circuit
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T05:22:32.372454+00:00
-- url     : https://prove2.me/theorems/eb08bba5-b314-4eb2-b2cc-5ecdf2eda371
-- title:
--   §2 (p. 444): Boolean circuit as a sequence of triples (a_i, b_i, c_i) and its value
-- statement:
--   A **circuit** (Papadimitriou–Tsitsiklis, §2) is a finite sequence of triples $C=((a_i,b_i,c_i),\ i=1,\dots,k)$. Each $a_i$ is one of the operations **false**, **true**, **and**, **or**. A triple with $a_i\in\{\text{false},\text{true}\}$ is an **input**; a triple with $a_i\in\{\text{and},\text{or}\}$ is a **gate**, and for a gate $b_i,c_i$ are indices of earlier triples: $1\le b_i,c_i<i$.
--
--   The **value** of a triple is defined recursively: an input has value true or false according to $a_i$; a gate has value
--   $$
--   \operatorname{val}(i)=\operatorname{val}(b_i)\ a_i\ \operatorname{val}(c_i),
--   $$
--   the Boolean operation $a_i$ applied to the values of triples $b_i$ and $c_i$. The **value of the circuit** is the value of its last triple, triple $k$ (which requires $k\ge1$).
--
--   The circuit value problem (CVP), "given a circuit $C$, is its value true?", is the basic P-complete problem from which Theorem 1 reduces.
--
--   **Formalization Note** Triples are indexed by `Fin k`: the paper's triple $i$ is Lean index $i-1$, and the condition $b_i,c_i<i$ is preserved by the shift. The paper sets $b_i=c_i=0$ for an input; $0$ is not a triple index, so in Lean the fields $b_i,c_i$ of an input are arbitrary and unused. The recursion is well founded because gates read earlier triples. The paper calls triple $k$ "the last gate"; the definition does not require it to be a gate (if it is an input, the circuit's value is that input's value).
-- source:
--   Papadimitriou and Tsitsiklis, The Complexity of Markov Decision Processes, Math. Oper. Res. 12(3) (1987), p. 444, §2, Complexity (circuit value problem)

import Mathlib

namespace MDPComplexity.CircuitValue

/-- The four operations of a triple (p. 444): `false`, `true`, `and`, `or`. -/
inductive Op
  | ff
  | tt
  | and
  | or
  deriving DecidableEq

/-- A circuit `C = ((a_i, b_i, c_i), i = 1, …, k)` (p. 444). Triples are indexed by `Fin k`
(the paper's triple `i` is Lean index `i - 1`). A gate (`and`/`or`) reads two earlier triples:
`b i < i` and `c i < i`. For an input (`ff`/`tt`) the fields `b i`, `c i` are not used (the paper
sets them to `0`, which is not a triple index). -/
structure Circuit (k : ℕ) where
  a : Fin k → Op
  b : Fin k → Fin k
  c : Fin k → Fin k
  b_lt : ∀ i, (a i = Op.and ∨ a i = Op.or) → b i < i
  c_lt : ∀ i, (a i = Op.and ∨ a i = Op.or) → c i < i

/-- The value of triple `i` (p. 444): an input has its constant value; a gate applies its
Boolean operation to the values of triples `b i` and `c i`. -/
def Circuit.val {k : ℕ} (C : Circuit k) (i : Fin k) : Bool :=
  match h : C.a i with
  | Op.ff => false
  | Op.tt => true
  | Op.and => C.val (C.b i) && C.val (C.c i)
  | Op.or => C.val (C.b i) || C.val (C.c i)
termination_by i.val
decreasing_by
  · exact C.b_lt i (Or.inl h)
  · exact C.c_lt i (Or.inl h)
  · exact C.b_lt i (Or.inr h)
  · exact C.c_lt i (Or.inr h)

/-- The last triple, the paper's triple `k` (Lean index `k - 1`); needs `k ≥ 1`. -/
def Circuit.lastIdx (k : ℕ) [NeZero k] : Fin k :=
  ⟨k - 1, Nat.sub_lt (Nat.pos_of_ne_zero (NeZero.ne k)) Nat.one_pos⟩

/-- The value of the circuit: the value of its last triple (p. 444). -/
def Circuit.value {k : ℕ} [NeZero k] (C : Circuit k) : Bool :=
  C.val (Circuit.lastIdx k)

end MDPComplexity.CircuitValue


