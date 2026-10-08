-- Prove2me | Definitions.Def_MDPComplexity_CircuitValue_Reduction
-- name    : MDPComplexity_CircuitValue_Reduction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T05:38:18.181991+00:00
-- url     : https://prove2.me/theorems/0b9cc7d3-df02-4d65-9003-733dcbac9587
-- title:
--   Proof of Theorem 1 (p. 445): the stationary Markov decision process M = (S, c, p) built from a circuit
-- statement:
--   Given a circuit $C=((a_i,b_i,c_i),\ i=1,\dots,k)$, the proof of Theorem 1 of Papadimitriou–Tsitsiklis builds a stationary Markov decision process $M=(S,c,p)$:
--
--   1. $S$ has one state $i$ for each triple of $C$, plus an extra state $q$.
--   2. An **input** state $i$ has a single decision $0$, with $p(i,q,0)=1$ and cost $c(i,0)=1$ if $a_i=\text{false}$, $c(i,0)=0$ if $a_i=\text{true}$.
--   3. The state $q$ has a single decision $0$, with $p(q,q,0)=1$ and cost $0$.
--   4. An **or** gate $i$ has two decisions $0,1$, both of cost $0$, with $p(i,b_i,0)=1$ and $p(i,c_i,1)=1$: the decision chooses whether the next state is $b_i$ or $c_i$.
--   5. An **and** gate $i$ has a single decision $0$ of cost $0$, and the next state is $b_i$ or $c_i$ with probability $1/2$ each.
--
--   All costs other than those of false inputs are $0$, and nothing depends on time. In the reduction the initial state is $k$, the last triple, and the horizon is $k$.
--
--   This process is the instance in the reduction from the circuit value problem to the finite-horizon Markov decision problem.
--
--   **Formalization Note** States are `Option (Fin k)`, with `none` the extra state $q$ and `some i` triple $i+1$ of the paper. The decisions at a state are `Fin 1` or, at an or gate, `Fin 2`, labelled $0,1$ as in the paper. The and-gate transition is $p(i,s',0)=\tfrac12\mathbf 1[s'=b_i]+\tfrac12\mathbf 1[s'=c_i]$, so that when $b_i=c_i$ (allowed by the paper) the move to $b_i$ has probability $1$ and the row still sums to $1$; read literally, $p(i,b_i,0)=p(i,c_i,0)=1/2$ would give a row summing to $1/2$ in that case. The file proves that every row is a probability vector, as the model requires.
-- source:
--   Papadimitriou and Tsitsiklis, The Complexity of Markov Decision Processes, Math. Oper. Res. 12(3) (1987), p. 445, §3, proof of Theorem 1

import Mathlib
import Definitions.Def_MDPComplexity_CircuitValue_Model
import Definitions.Def_MDPComplexity_CircuitValue_Circuit

namespace MDPComplexity.CircuitValue

open Finset BigOperators

variable {k : ℕ}

/-- Number of decisions at a state of the process of the proof of Theorem 1 (p. 445):
two (`0`, `1`) at an `or` gate, one (`0`) at every other state (inputs, `and` gates, `q`).
States are `Option (Fin k)`: `some i` is triple `i`, `none` is the extra state `q`. -/
def Circuit.numDec (C : Circuit k) : Option (Fin k) → ℕ
  | none => 1
  | some i => if C.a i = Op.or then 2 else 1

/-- Transition probability `p(s, s', d)` of the process (p. 445), for decision number `d`:
an input moves to `q`; `q` stays at `q`; an `or` gate moves to `b_i` under decision `0` and to
`c_i` under decision `1`; an `and` gate moves to `b_i` and to `c_i` with probability `1/2` each
(written as a sum of the two indicators, so that `b_i = c_i` gives probability `1`). -/
noncomputable def Circuit.trans (C : Circuit k) : Option (Fin k) → ℕ → Option (Fin k) → ℝ
  | none, _, s' => if s' = none then 1 else 0
  | some i, d, s' =>
    match C.a i with
    | Op.ff => if s' = none then 1 else 0
    | Op.tt => if s' = none then 1 else 0
    | Op.or =>
      if d = 0 then (if s' = some (C.b i) then 1 else 0)
      else (if s' = some (C.c i) then 1 else 0)
    | Op.and =>
      (if s' = some (C.b i) then 1 / 2 else 0) + (if s' = some (C.c i) then 1 / 2 else 0)

/-- Cost of any decision at a state (p. 445): `1` at a `false` input, `0` everywhere else. -/
noncomputable def Circuit.cost (C : Circuit k) : Option (Fin k) → ℝ
  | none => 0
  | some i => if C.a i = Op.ff then 1 else 0

theorem Circuit.numDec_pos (C : Circuit k) (s : Option (Fin k)) : 0 < C.numDec s := by
  cases s with
  | none => simp [Circuit.numDec]
  | some i => simp only [Circuit.numDec]; split_ifs <;> norm_num

theorem Circuit.trans_nonneg (C : Circuit k) (s : Option (Fin k)) (d : ℕ)
    (s' : Option (Fin k)) : 0 ≤ C.trans s d s' := by
  cases s with
  | none => simp only [Circuit.trans]; split_ifs <;> norm_num
  | some i =>
    simp only [Circuit.trans]
    cases C.a i <;> simp only <;> split_ifs <;> norm_num

theorem Circuit.trans_sum_one (C : Circuit k) (s : Option (Fin k)) (d : ℕ) :
    ∑ s', C.trans s d s' = 1 := by
  cases s with
  | none => simp [Circuit.trans]
  | some i =>
    simp only [Circuit.trans]
    cases C.a i
    · simp
    · simp
    · rw [Finset.sum_add_distrib]; simp; norm_num
    · split_ifs <;> simp

/-- The stationary Markov decision process `M = (S, c, p)` built from the circuit `C` in the
proof of Theorem 1 (p. 445). States: one per triple plus `q` (`none`). Decisions at `s`:
`Fin (C.numDec s)`. Costs and transitions do not depend on time. -/
noncomputable def Circuit.toMDP (C : Circuit k) : MDP (Option (Fin k)) where
  D s := Fin (C.numDec s)
  instFintype _ := inferInstance
  instNonempty s := ⟨⟨0, C.numDec_pos s⟩⟩
  c s _ _ := C.cost s
  p s d _ s' := C.trans s d.val s'
  p_nonneg s d _ s' := C.trans_nonneg s d.val s'
  p_sum_one s d _ := C.trans_sum_one s d.val

end MDPComplexity.CircuitValue


