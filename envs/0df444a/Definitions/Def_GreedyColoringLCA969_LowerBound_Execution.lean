-- Prove2me | Definitions.Def_GreedyColoringLCA969_LowerBound_Execution
-- name    : GreedyColoringLCA969_LowerBound_Execution
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T09:45:42.851074+00:00
-- url     : https://prove2.me/theorems/04b770bf-dd59-4b2d-9748-595d1af2e27d
-- title:
--   One operational run determines both colors and query counts
-- statement:
--   Each question starts from an empty transcript, zero graph-query count, and no returned color. A graph action appends the actual graph reply and increments the counter by one. A bit action appends the requested shared bit; an internal step appends a tick. Neither increments the graph-query counter. A return action stores its positive color, after which the configuration is unchanged.
--
--   If $s_t$ is the configuration after $t$ steps, the returned-color predicate is $\exists t:\operatorname{result}(s_t)=c$. The extended query cost is
--
--   $$q_r(A,R,v)=\begin{cases}\sup_{t\in\mathbb N}\operatorname{queries}(s_t),&\text{the run halts},\\+\infty,&\text{the run never halts}.\end{cases}$$
--
--   For a terminating run this is exactly its actual graph-query count. Global success on $R$ is the event that some greedy coloring $c$ is returned at every vertex under the same tape: $\forall v,\exists t:\operatorname{result}(s_t)=c(v)$. Nontermination is unsuccessful. Thus output, cost and success all derive from one execution, with no graph-dependent advice or default successful color.
--
--   **Formalization Note** Extended counts use nonnegative extended reals; nontermination is assigned infinite cost even when it makes only finitely many graph calls. This extends the convention conservatively on every terminating source execution.
--
--   Differences from the source:
--   - encoding: actual finite execution and its query count → absorbing finite-step configurations and an extended cost equal to infinity on divergence; reason: on every terminating source run the returned label and counter agree exactly; divergence never counts as success
-- source:
--   Zi Song Yeoh, Krzysztof Onak, Dragos-Florian Ristache, STOC 2027 submission #969 (October 2026), Definitions 2.6–2.7, pp.8–9 (PDF 9–10); Section 3, p.10 (PDF 11); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/969.pdf

import Definitions.Def_GreedyColoringLCA969_LowerBound_Algorithm

open scoped ENNReal
open MeasureTheory
open Classical

namespace GreedyColoringLCA969.LowerBound

/-- Transcript, number of graph queries, and optional returned color. -/
abbrev Config := History × ℕ × Option ℕ+

/-- One operational step. Halted configurations are absorbing. Only actual graph queries
increase the query counter; internal steps and random-access bit reads cost zero queries. -/
def step {m : OracleMode} {n : ℕ} (A : Algorithm m) (R : Representation n)
    (r : Tape) (v : Fin n) (s : Config) : Config :=
  match s.2.2 with
  | some _ => s
  | none => match A n v s.1 with
    | .halt c => (s.1, s.2.1, some c)
    | .query q => (s.1 ++ [.inl (oracleReply m R q)], s.2.1 + 1, none)
    | .readBit j => (s.1 ++ [.inr (.inl (r j))], s.2.1, none)
    | .tick => (s.1 ++ [.inr (.inr ())], s.2.1, none)

/-- Fresh execution for each question, with the same rule and shared tape. -/
def run {m : OracleMode} {n : ℕ} (A : Algorithm m) (R : Representation n)
    (r : Tape) (v : Fin n) : ℕ → Config
  | 0 => ([], 0, none)
  | t + 1 => step A R r v (run A R r v t)

/-- Returns c exactly when this execution returns c at a finite time. -/
def Returns {m : OracleMode} {n : ℕ} (A : Algorithm m) (R : Representation n)
    (r : Tape) (v : Fin n) (c : ℕ+) : Prop :=
  ∃ t, (run A R r v t).2.2 = some c

/-- Actual graph-query count, extended to +infinity for a nonterminating execution.
On a terminating run the absorbing counter stabilizes at its exact query count. -/
noncomputable def queryCost {m : OracleMode} {n : ℕ} (A : Algorithm m)
    (R : Representation n) (r : Tape) (v : Fin n) : ℝ≥0∞ :=
  if ∃ t, (run A R r v t).2.2 ≠ none then
    ⨆ t, ((run A R r v t).2.1 : ℝ≥0∞)
  else ⊤

/-- Global success requires every vertex to terminate with a greedy labeling on one tape;
a nontermination can never be hidden behind a default output. -/
def successEvent {m : OracleMode} {n : ℕ} (A : Algorithm m)
    (R : Representation n) : Set Tape :=
  {r | ∃ c : Fin n → ℕ+, IsGreedy R.graph c ∧ ∀ v, Returns A R r v (c v)}

end GreedyColoringLCA969.LowerBound


