-- Prove2me | Definitions.Def_JohnsonApprox_SubsetSum_Ak
-- name    : JohnsonApprox_SubsetSum_Ak
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T15:16:54.024387+00:00
-- url     : https://prove2.me/theorems/82590927-b967-4fb5-b081-f9bebf603959
-- title:
--   Algorithm A_k for SUBSET-SUM and its choosable outputs (Section 3)
-- statement:
--   This defines, for each natural number $k$, the approximation algorithm $A_k$ of Johnson (1974) for SUBSET-SUM, together with the set of outputs it may return. Given an input $\langle T, s, b\rangle$, the paper's algorithm reads:
--
--   > 1. Let SUB be that subset of {x ∈ T: s(x) > b/(k + 1)} whose measure is closest to, without exceeding b. Let SUM be this measure, and set LEFT = T − SUB.
--   > 2. If for all x ∈ LEFT, s(x) + SUM > b, halt and return SUB.
--   > 3. Let y be an element of LEFT for which s(y) + SUM is closest to, without exceeding, b.
--   > 4. Set LEFT = LEFT − {y}. SUB = SUB ∪ {y}, SUM = SUM + s(y).
--   > 5. Go to 2.
--
--   Call $x$ **big** if $s(x) > b/(k+1)$ (strict inequality) and write $X^{\mathrm{BIG}} = \{x \in X : s(x) > b/(k+1)\}$ for the big part of a set $X$.
--
--   1. **Step 1.** A set $S$ is an admissible Step 1 choice if $S$ consists of big elements, $m(S) \le b$, and $m(S') \le m(S)$ for every set $S'$ of big elements with $m(S') \le b$. Any such maximizer may be chosen.
--   2. **State.** The algorithm's state is the triple $(\mathrm{SUB}, \mathrm{LEFT}, \mathrm{SUM})$; after Step 1 with choice $S$ it is $(S,\ T \setminus S,\ m(S))$.
--   3. **Halting (Step 2).** A state halts when $s(x) + \mathrm{SUM} > b$ for every $x \in \mathrm{LEFT}$.
--   4. **One iteration (Steps 2–4).** From a non-halting state, choose any $y \in \mathrm{LEFT}$ with $s(y) + \mathrm{SUM} \le b$ such that $s(z) + \mathrm{SUM} \le s(y) + \mathrm{SUM}$ for every $z \in \mathrm{LEFT}$ with $s(z) + \mathrm{SUM} \le b$; the next state is $(\mathrm{SUB} \cup \{y\},\ \mathrm{LEFT} \setminus \{y\},\ \mathrm{SUM} + s(y))$.
--   5. **Choosable outputs.** A set $T_1$ is **choosable by $A_k$** on the input if, for some admissible Step 1 choice, some finite sequence of admissible iterations reaches a halting state whose $\mathrm{SUB}$ equals $T_1$.
--
--   As the paper says (p. 258), "since the algorithms we will study are not always completely determined, more than one solution may be choosable for a given input"; the performance $A_k(u)$ is the worst (minimum) measure over choosable outputs, and all results about $A_k$ are statements about every choosable output.
--
--   **Formalization Note** The algorithm is a nondeterministic run relation, not a function: both "that subset … whose measure is closest to" (Step 1) and "an element … for which" (Step 3) are existential choices among all ties. `Choosable k u T₁` is `∃ S, IsStep1Choice k u S ∧ ∃ σ, ReflTransGen (Step u) (initState u S) σ ∧ Halts u σ ∧ σ.SUB = T₁`. The threshold is $b/(k+1)$ computed in $\mathbb{Q}$ with $k$ cast from $\mathbb{N}$. The definition is stated for every $k \in \mathbb{N}$; the paper's range $k \ge 1$ is a hypothesis of each theorem.
-- source:
--   Johnson, Approximation algorithms for combinatorial problems, J. Comput. System Sci. 9 (1974), p. 258, Section 2 (choosable solutions), and p. 260, Section 3 (algorithm A_k)

import Mathlib
import Definitions.Def_JohnsonApprox_SubsetSum_Problem

namespace JohnsonApprox.SubsetSum

variable {α : Type}

/-- The big elements `{x ∈ T : s(x) > b/(k + 1)}` of the input (strict inequality). -/
def bigElems (k : ℕ) (u : Input α) : Finset α :=
  u.T.filter (fun x => u.b / ((k : ℚ) + 1) < u.s x)

/-- The big part `X^BIG = {x ∈ X : s(x) > b/(k + 1)}` of a set `X`. -/
def bigPart (k : ℕ) (u : Input α) (X : Finset α) : Finset α :=
  X.filter (fun x => u.b / ((k : ℚ) + 1) < u.s x)

/-- Step 1 of `A_k`: `S` is a subset of the big elements "whose measure is closest to, without
exceeding `b`", i.e. of maximum measure among the subsets of big elements with measure `≤ b`.
Every such maximizer may be chosen (ties are allowed). -/
def IsStep1Choice (k : ℕ) (u : Input α) (S : Finset α) : Prop :=
  S ⊆ bigElems k u ∧ measure u S ≤ u.b ∧
    ∀ S' ⊆ bigElems k u, measure u S' ≤ u.b → measure u S' ≤ measure u S

/-- The state of algorithm `A_k`: the paper's variables `SUB`, `LEFT` and `SUM`. -/
structure State (α : Type) where
  SUB : Finset α
  LEFT : Finset α
  SUM : ℚ

/-- The state after Step 1 with the chosen set `S`: `SUB = S`, `SUM = m(S)`, `LEFT = T − SUB`. -/
def initState [DecidableEq α] (u : Input α) (S : Finset α) : State α :=
  ⟨S, u.T \ S, measure u S⟩

/-- The halting test of Step 2: for all `x ∈ LEFT`, `s(x) + SUM > b`. -/
def Halts (u : Input α) (σ : State α) : Prop :=
  ∀ x ∈ σ.LEFT, u.b < u.s x + σ.SUM

/-- One pass through Steps 2–4 of `A_k`: Step 2 does not halt, Step 3 picks any `y ∈ LEFT` for
which `s(y) + SUM` is closest to, without exceeding, `b` (ties allowed), and Step 4 moves `y`
from `LEFT` to `SUB` and adds `s(y)` to `SUM`. -/
def Step [DecidableEq α] (u : Input α) (σ σ' : State α) : Prop :=
  ¬ Halts u σ ∧
    ∃ y ∈ σ.LEFT, u.s y + σ.SUM ≤ u.b ∧
      (∀ z ∈ σ.LEFT, u.s z + σ.SUM ≤ u.b → u.s z + σ.SUM ≤ u.s y + σ.SUM) ∧
      σ' = ⟨σ.SUB ∪ {y}, σ.LEFT.erase y, σ.SUM + u.s y⟩

/-- `T₁` is choosable by `A_k` on input `u`: for some admissible Step 1 choice, some finite
sequence of admissible iterations of Steps 2–4 reaches a state at which Step 2 halts, and the
returned set `SUB` is `T₁`. -/
def Choosable [DecidableEq α] (k : ℕ) (u : Input α) (T₁ : Finset α) : Prop :=
  ∃ S, IsStep1Choice k u S ∧
    ∃ σ, Relation.ReflTransGen (Step u) (initState u S) σ ∧ Halts u σ ∧ σ.SUB = T₁

end JohnsonApprox.SubsetSum


