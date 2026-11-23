-- Prove2me | Definitions.Def_MusicStreaming_Axioms_Supplement_Bankruptcy
-- name    : MusicStreaming_Axioms_Supplement_Bankruptcy
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T05:24:51.237818+00:00
-- url     : https://prove2.me/theorems/33a09258-3aa6-4a0e-a1e8-9dae7dcd9ca9
-- title:
--   §5, p. 15 — bankruptcy problems and rules, the proportional rule P and the constrained equal awards rule CEA
-- statement:
--   A **bankruptcy problem** is a triple $(N,c,E)$: a finite set $N$ of agents, a claims vector $c=(c_i)_{i\in N}$ and an amount $E$ to be divided. It is *valid* when $c\in\mathbb R^N_+$, $E\in\mathbb R_+$ and $\sum_{i\in N}c_i\ge E$. A **rule** assigns a vector $R(N,c,E)$ to every bankruptcy problem; it is a *bankruptcy rule* when on every valid problem $0\le R_i(N,c,E)\le c_i$ for each $i\in N$ and $\sum_{i\in N}R_i(N,c,E)=E$. Agents are drawn from an arbitrary type, so the same notion serves for artists and for issues.
--
--   The **proportional rule** and the **constrained equal awards rule** are, for each $i\in N$,
--
--   $$P_i(N,c,E)=\frac{c_i}{\sum_{i'\in N}c_{i'}}\,E,\qquad CEA_i(N,c,E)=\min\{\lambda,c_i\}\ \text{ where }\lambda\ge0\text{ satisfies }\sum_{i\in N}\min\{\lambda,c_i\}=E.$$
--
--   On a valid problem a cutoff $\lambda$ exists, and although it need not be unique (for instance when $E=\sum_i c_i$), the awards $\min\{\lambda,c_i\}$, $i\in N$, are the same for every solution. These two rules are the building blocks of the two-stage rules of §5.
--
--   **Formalization Note** A problem is a structure with a `Finset` of agents, a claims function and a real amount; only the claims of agents in $N$ matter. $CEA$ uses one chosen solution $\lambda\ge0$ of the budget equation; when the equation has no nonnegative solution (invalid data) the rule returns $0$. In $P$, Lean's convention $x/0=0$ gives the zero vector when $\sum_{i'}c_{i'}=0$, which on a valid problem forces $E=0$, so the awards agree with the intended ones.
-- source:
--   Bergantiños, Moreno-Ternero, Revenue sharing at music streaming platforms, arXiv:2310.11861v1, p. 15, §5 (bankruptcy problem, proportional rule, constrained equal awards rule)

import Mathlib

namespace MusicStreaming.Axioms.Supplement

/-- A bankruptcy problem `(N, c, E)` (§5, p. 15): a finite set `N` of agents, a claims vector
`c` (only its values on `N` matter) and an amount `E` to be divided. Agents are drawn from an
arbitrary type `α`, so the same notion serves for artists and for issues (users). -/
structure BankruptcyProblem (α : Type*) where
  /-- the agents -/
  N : Finset α
  /-- the claims vector -/
  c : α → ℝ
  /-- the amount to be divided -/
  E : ℝ

variable {α : Type*}

/-- The data of a bankruptcy problem as on p. 15: `c ∈ ℝ^N_+`, `E ∈ ℝ_+`, and
`∑_{i ∈ N} c_i ≥ E`. -/
def BankruptcyProblem.IsValid (B : BankruptcyProblem α) : Prop :=
  (∀ i ∈ B.N, 0 ≤ B.c i) ∧ 0 ≤ B.E ∧ B.E ≤ ∑ i ∈ B.N, B.c i

/-- A rule assigns a real vector to every bankruptcy problem (p. 15). -/
abbrev BankruptcyRule (α : Type*) := BankruptcyProblem α → α → ℝ

/-- The requirements on a bankruptcy rule (p. 15): on every valid problem,
`0 ≤ R_i(N, c, E) ≤ c_i` for each `i ∈ N` and `∑_{i ∈ N} R_i(N, c, E) = E`. -/
def IsBankruptcyRule (R : BankruptcyRule α) : Prop :=
  ∀ B : BankruptcyProblem α, B.IsValid →
    (∀ i ∈ B.N, 0 ≤ R B i ∧ R B i ≤ B.c i) ∧ ∑ i ∈ B.N, R B i = B.E

/-- The proportional rule (p. 15): `P_i(N, c, E) = c_i / (∑_{i' ∈ N} c_{i'}) · E`.
(If `∑ c = 0`, Lean's `x / 0 = 0` gives the zero vector; on a valid problem `E = 0` then.) -/
noncomputable def proportional : BankruptcyRule α :=
  fun B i => B.c i / (∑ i' ∈ B.N, B.c i') * B.E

/-- The cutoffs of the constrained equal awards rule (p. 15): the numbers `λ ≥ 0` with
`∑_{i ∈ N} min{λ, c_i} = E`. -/
def ceaCutoffs (B : BankruptcyProblem α) : Set ℝ :=
  {l | 0 ≤ l ∧ ∑ i ∈ B.N, min l (B.c i) = B.E}

/-- The constrained equal awards rule (p. 15): `CEA_i(N, c, E) = min{λ, c_i}` where `λ`
satisfies `∑_{i ∈ N} min{λ, c_i} = E`. The cutoff `λ` is one chosen solution of the budget
equation; on a valid problem a solution exists and the awards `min{λ, c_i}` (`i ∈ N`) do not
depend on which solution is chosen. When no solution exists (invalid data) the rule returns `0`. -/
noncomputable def cea : BankruptcyRule α := by
  classical
  exact fun B i =>
    if h : (ceaCutoffs B).Nonempty then min h.choose (B.c i) else 0

end MusicStreaming.Axioms.Supplement


