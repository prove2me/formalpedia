-- Prove2me | Definitions.Def_SFMQueryLower_EmptyMin_OracleStrategy
-- name    : SFMQueryLower_EmptyMin_OracleStrategy
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:20:57.479512+00:00
-- url     : https://prove2.me/theorems/331b1544-fb1d-4ec7-9374-93fb3015ef9a
-- title:
--   Causal oracle strategies and their executions
-- statement:
--   Let $\mathcal Q$, $\mathcal R$, and $\mathcal A$ be query, reply, and output sets. A deterministic strategy chooses a query, returns an output, or diverges internally, using only its finite observed history. If it issues $S$, the next history appends $(S,f(S))$, where $f:\mathcal Q\to\mathcal R$ is the fixed oracle. Answers and divergence are absorbing.
--
--   For any predicate $p$ on queries, its actual query count is
--   $$Q_p(B,f)=\sum_{t\ge0}\mathbf1\{\text{an issue }S\text{ occurs at }t\text{ and }p(S)\}.$$
--   The value is in $[0,\infty]$. Returning an output and ever querying a set are events defined from this execution. Repeated queries count separately. This interface is independent of submodularity and can be reused for other oracle problems.
--
--   **Formalization Note** Interaction indices start at zero. An explicit divergence action allows internal nontermination with no additional queries. No hidden input, partition or future reply is an argument to the strategy.
-- source:
--   James Fox, Randomized Query Lower Bounds for Submodular Function Minimization, STOC 2027 submission #292 (October 2026), Definition 1.1 and oracle model, printed pp. 1–2 / PDF pp. 2–3

import Mathlib

set_option autoImplicit false
open scoped ENNReal

namespace SFMQueryLower.EmptyMin

/-- Causal oracle actions. `diverge` represents internal nontermination without more queries. -/
inductive OracleAction (Query ReplyOutput : Type) where
  | query : Query → OracleAction Query ReplyOutput
  | answer : ReplyOutput → OracleAction Query ReplyOutput
  | diverge : OracleAction Query ReplyOutput

/-- The only information available to a deterministic strategy is its observed history. -/
abbrev OracleStrategy (Query Reply Output : Type) :=
  List (Query × Reply) → OracleAction Query Output

/-- A state is an active history, a returned answer, or internal divergence (`none`). -/
def execution {Query Reply Output : Type}
    (B : OracleStrategy Query Reply Output) (f : Query → Reply) :
    ℕ → Option (Sum Output (List (Query × Reply)))
  | 0 => some (.inr [])
  | t + 1 =>
    match execution B f t with
    | none => none
    | some (.inl a) => some (.inl a)
    | some (.inr h) =>
      match B h with
      | .query S => some (.inr (h ++ [(S, f S)]))
      | .answer a => some (.inl a)
      | .diverge => none

/-- The query actually issued at the next interaction; repeated queries are separate issues. -/
def issuedQuery {Query Reply Output : Type}
    (B : OracleStrategy Query Reply Output) (f : Query → Reply) (t : ℕ) : Option Query :=
  match execution B f t with
  | some (.inr h) =>
    match B h with
    | .query S => some S
    | _ => none
  | _ => none

/-- Returning requires a finite interaction time. Nontermination returns no answer. -/
def Returns {Query Reply Output : Type}
    (B : OracleStrategy Query Reply Output) (f : Query → Reply) (a : Output) : Prop :=
  ∃ t : ℕ, execution B f t = some (.inl a)

def Queries {Query Reply Output : Type}
    (B : OracleStrategy Query Reply Output) (f : Query → Reply) (S : Query) : Prop :=
  ∃ t : ℕ, issuedQuery B f t = some S

/-- Total count of actual issues satisfying a predicate, including infinite runs. -/
noncomputable def queryCount {Query Reply Output : Type}
    (B : OracleStrategy Query Reply Output) (f : Query → Reply) (p : Query → Prop) : ℝ≥0∞ := by
  classical
  exact ∑' t : ℕ, if ∃ S, issuedQuery B f t = some S ∧ p S then 1 else 0

end SFMQueryLower.EmptyMin


