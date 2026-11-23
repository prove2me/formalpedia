-- Prove2me | Definitions.Def_OnlineMaxWeightMatch_Approx_Supplement_MaxSSAT
-- name    : OnlineMaxWeightMatch_Approx_Supplement_MaxSSAT
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T08:18:03.545547+00:00
-- url     : https://prove2.me/theorems/6025a730-2379-44a0-9fc7-c9a238c69013
-- title:
--   Definition 2.2, pp. 4–5 — MAX-SSAT: 3CNF formulas, adaptive strategies and $OPT_{on}(\phi)$
-- statement:
--   A **MAX-SSAT instance** (Definition 2.2) is a CNF formula $\phi$ over an ordered list of Boolean variables $(x_1,\dots,x_n)$, given as a list of clauses $C_1,\dots,C_m$, each a list of literals $x_i$ or $\bar x_i$; repeated clauses count separately. The formula is a **3CNF** formula when every clause has one, two or three literals, all over $x_1,\dots,x_n$.
--
--   The variables $x_1,x_3,\dots$ are **deterministic** and $x_2,x_4,\dots$ are **random**. The variables are assigned in order: we choose the value of a deterministic variable, and nature sets each random variable to True or False uniformly at random, independently. A **strategy** $\sigma$ chooses the value of each deterministic variable $x_i$ as a function of the values nature gave the random variables $x_j$ with $j<i$. Its value $A_\sigma(\phi)$ is the expected number of clauses of $\phi$ satisfied by the final assignment, and
--   $$OPT_{on}(\phi)=\max_\sigma A_\sigma(\phi).$$
--
--   Two properties of a formula are used in §3:
--
--   1. **no negated random variable**: no clause contains a literal $\bar x_i$ with $i$ even;
--   2. **occurrence bound $k$**: every variable appears in at most $k$ clauses of $\phi$.
--
--   The encoding writes $n$, $m$, and then each clause as its length followed by its literals (index in binary, then a sign bit).
--
--   **Formalization Note** Lean indexes variables from $0$: Lean variable $v$ is the paper's $x_{v+1}$, so the random variables are the odd Lean indices. A strategy receives the values of the earlier random variables (earlier deterministic values are functions of these); randomized strategies are mixtures of deterministic ones and do not raise the maximum, which is taken as a supremum over the finite set of strategies.
-- source:
--   Papadimitriou, Pollner, Saberi & Wajc, Online Stochastic Max-Weight Bipartite Matching: Beyond Prophet Inequalities, arXiv:2102.10261v3, pp. 4–5, Definition 2.2; p. 5, Lemma 2.3 properties 1–2; p. 6, Lemma 3.1 properties (1)–(2)

import Mathlib
import Definitions.Def_OptimalQueuingComplexity_Restless_encNat

namespace OnlineMaxWeightMatch.Approx.Supplement

open OptimalQueuingComplexity.Restless

/-- A **MAX-SSAT instance** (Definition 2.2, pp. 4–5): a CNF formula over the ordered variables
`x_1, …, x_n`. Lean variable `v : ℕ` is the paper's `x_{v+1}`; a literal is a pair
`(v, s)`, the positive literal `x_{v+1}` when `s = true` and its negation when `s = false`;
a clause is a list of literals and the formula is the list of its clauses, duplicates kept. -/
structure SSATFormula where
  /-- the number `n` of variables -/
  n : ℕ
  /-- the clauses, in order, each a list of literals -/
  clauses : List (List (ℕ × Bool))

/-- The paper's random variables are `x_2, x_4, …`, i.e. Lean variables `v` with `v` odd;
the deterministic ones `x_1, x_3, …` are the Lean variables with `v` even. -/
def IsRandomVar (v : ℕ) : Prop := v % 2 = 1

instance (v : ℕ) : Decidable (IsRandomVar v) := inferInstanceAs (Decidable (v % 2 = 1))

/-- `φ` is a **3CNF formula**: every clause has one, two or three literals, all over the
variables `x_1, …, x_n`. -/
def SSATFormula.IsThreeCNF (φ : SSATFormula) : Prop :=
  ∀ C ∈ φ.clauses, 1 ≤ C.length ∧ C.length ≤ 3 ∧ ∀ l ∈ C, l.1 < φ.n

/-- Property (1) of Lemmas 2.3 and 3.1: no random variable appears negated in any clause. -/
def SSATFormula.NoNegatedRandom (φ : SSATFormula) : Prop :=
  ∀ C ∈ φ.clauses, ∀ l ∈ C, IsRandomVar l.1 → l.2 = true

/-- Property (2) of Lemma 3.1: each variable appears in at most `k` clauses of `φ`
(the number of clauses containing a literal over it, duplicates counted). -/
def SSATFormula.OccursAtMost (φ : SSATFormula) (k : ℕ) : Prop :=
  ∀ v : ℕ, (φ.clauses.filter fun C => C.any fun l => l.1 == v).length ≤ k

/-- A **deterministic adaptive strategy** for MAX-SSAT: the value chosen for a deterministic
variable `i` is a function of the values nature chose for the random variables before `i`
(their values are passed for every `j < i`; the entries at deterministic `j` are masked to
`false`). Values of earlier deterministic variables are functions of these, so this is the
class of all online algorithms; randomized ones are mixtures and do not raise the optimum. -/
def SSATPolicy (n : ℕ) : Type :=
  (i : Fin n) → ({j : Fin n // j < i} → Bool) → Bool

/-- The truth assignment produced by strategy `σ` when nature's coin flips are `r`: random
variables take their coin value, deterministic ones the strategy's choice. Variables outside
`x_1, …, x_n` (never used by a 3CNF formula) are set to `false`. -/
def SSATPolicy.assign {n : ℕ} (σ : SSATPolicy n) (r : Fin n → Bool) (v : ℕ) : Bool :=
  if h : v < n then
    if IsRandomVar v then r ⟨v, h⟩
    else σ ⟨v, h⟩ (fun j => if IsRandomVar j.1.1 then r j.1 else false)
  else false

/-- A clause is satisfied by `x` if one of its literals `(v, s)` has `x v = s`. -/
def clauseSat (x : ℕ → Bool) (C : List (ℕ × Bool)) : Bool :=
  C.any fun l => x l.1 == l.2

/-- The number of clauses of `φ` satisfied by `x`, duplicates counted. -/
def SSATFormula.numSat (φ : SSATFormula) (x : ℕ → Bool) : ℕ :=
  φ.clauses.countP (clauseSat x)

/-- `A(φ)` for the strategy `σ`: the expected number of satisfied clauses when every random
variable is an independent fair coin (uniform average over all coin vectors `r`; the coins at
deterministic positions are ignored by `assign`). -/
noncomputable def ssatValue (φ : SSATFormula) (σ : SSATPolicy φ.n) : ℝ :=
  (∑ r : Fin φ.n → Bool, (φ.numSat (σ.assign r) : ℝ)) / 2 ^ φ.n

/-- `OPT_on(φ)`: the maximum expected number of satisfied clauses, the supremum of
`ssatValue φ σ` over all strategies (a finite, nonempty set). -/
noncomputable def ssatOpt (φ : SSATFormula) : ℝ :=
  ⨆ σ : SSATPolicy φ.n, ssatValue φ σ

/-- Binary code of a formula: `n`, the number of clauses, then each clause as its length
followed by its literals (variable in binary, then the sign bit). -/
def encSSAT (φ : SSATFormula) : List Bool :=
  encNat φ.n ++ encNat φ.clauses.length ++
    φ.clauses.flatMap fun C => encNat C.length ++ C.flatMap fun l => encNat l.1 ++ [l.2]

end OnlineMaxWeightMatch.Approx.Supplement


