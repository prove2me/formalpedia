-- Prove2me | Definitions.Def_MDPFinance_Bellman_Policy
-- name    : MDPFinance_Bellman_Policy
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T20:06:49.87898+00:00
-- url     : https://prove2.me/theorems/d2cda698-4ad5-48f6-aaa1-131adfecd27a
-- title:
--   Decision rules and $N$-stage policies
-- statement:
--   A **decision rule at time $n$** (Definition 2.1.5a) is a measurable map $f_n : E \to A$ with
--   $f_n(x) \in D_n(x)$ for every state $x$, i.e. a measurable selection of an admissible action in
--   every state. The set of all decision rules at time $n$ is denoted $F_n$; it is nonempty because
--   $D_n$ is required to contain the graph of some measurable map.
--
--   An **$N$-stage policy** (Definition 2.1.5b) is a sequence $\pi = (f_0, f_1, \dots, f_{N-1})$ with
--   $f_n \in F_n$ for every $n$. A policy prescribes, at every stage and in every state, which
--   admissible action to take, using only the current state (a *Markov* policy, as opposed to a
--   policy that may depend on the full history — see the companion definition of a
--   history-dependent policy).
--
--   **Formalization Note.** A policy is represented as a single measurable function
--   $f : \mathbb{N} \to E \to A$, together with the requirement that $f_n(x) \in D_n(x)$ for
--   $n < N$ and every $x$; measurability of $f_n$ is required for every $n \in \mathbb{N}$, not
--   only $n < N$, which is a harmless strengthening (a genuine decision rule of Definition 2.1.5a is
--   always measurable) needed to keep the total-function encoding well-behaved for $n \ge N$, where
--   the book's own $(f_0,\dots,f_{N-1})$ simply has no $n$-th entry.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 16, Definition 2.1.5

import Mathlib
import Definitions.Def_MDPFinance_Bellman_Model

open MeasureTheory ProbabilityTheory

namespace MDPFinance.Bellman

variable {E A : Type*} [MeasurableSpace E] [MeasurableSpace A] {N : ℕ}

/-- A decision rule at time `n` (Bäuerle–Rieder, Definition 2.1.5a, p. 16, PDF 31): a measurable
`f : E → A` with `f(x) ∈ D_n(x)` for all `x`. -/
def IsDecisionRule (M : MarkovDecisionModel E A N) (n : ℕ) (f : E → A) : Prop :=
  Measurable f ∧ ∀ x, (x, f x) ∈ M.D n

/-- An `N`-stage policy (Bäuerle–Rieder, Definition 2.1.5b, p. 16, PDF 31): a sequence of
decision rules `π = (f_0, …, f_{N-1})`. Formalized as a single `f : ℕ → E → A`, measurable at
every `n` (a harmless strengthening for `n ≥ N`, where the book's `f_n` is simply absent — see
`MODERATION_NOTES.md`), whose restriction to `n < N` is a decision rule of `M`. -/
def Policy (M : MarkovDecisionModel E A N) : Type _ :=
  {f : ℕ → E → A // (∀ n, Measurable (f n)) ∧ ∀ n < N, ∀ x, (x, f n x) ∈ M.D n}

lemma Policy.isDecisionRule {M : MarkovDecisionModel E A N} (π : Policy M) {n : ℕ} (hn : n < N) :
    IsDecisionRule M n (π.1 n) :=
  ⟨π.2.1 n, π.2.2 n hn⟩

end MDPFinance.Bellman


