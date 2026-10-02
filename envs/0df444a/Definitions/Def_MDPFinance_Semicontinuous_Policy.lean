-- Prove2me | Definitions.Def_MDPFinance_Semicontinuous_Policy
-- name    : MDPFinance_Semicontinuous_Policy
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T20:23:31.241555+00:00
-- url     : https://prove2.me/theorems/5007bb22-1112-48d7-b5e0-8bf1343970f4
-- title:
--   Decision rule at time $n$
-- statement:
--   A **decision rule at time $n$** (Definition 2.1.5a) is a measurable map $f_n : E \to A$ with
--   $f_n(x) \in D_n(x)$ for every state $x$: a measurable selection of an admissible action in
--   every state. The set of all decision rules at time $n$ is denoted $F_n$.
--
--   This mission only needs the single-stage notion, not a full $N$-stage policy $\pi =
--   (f_0,\dots,f_{N-1})$ (chunk `02a-model-bellman-equation` builds the latter): every result here
--   either exhibits a single maximizing decision rule at a fixed stage $n$, or is a statement about
--   the Structure Assumption (SAN), which itself is phrased in terms of decision rules stage by
--   stage, never a full multi-stage policy.
--
--   **Formalization Note.** Restated from `MDPFinance.Bellman.IsDecisionRule` (chunk `02a`); the
--   identical definition, in this chunk's own sub-namespace.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 16, Definition 2.1.5a

import Mathlib
import Definitions.Def_MDPFinance_Semicontinuous_Model

open MeasureTheory ProbabilityTheory

namespace MDPFinance.Semicontinuous

variable {E A : Type*} [MeasurableSpace E] [MeasurableSpace A] {N : ℕ}

/-- A decision rule at time `n` (Bäuerle–Rieder, Definition 2.1.5a, p. 16, PDF 31): a measurable
`f : E → A` with `f(x) ∈ D_n(x)` for all `x`. Restated from `MDPFinance.Bellman.IsDecisionRule`
(chunk `02a`); only this one clause of Def. 2.1.5 is needed in this chunk, since no result here
uses a full multi-stage policy. -/
def IsDecisionRule (M : MarkovDecisionModel E A N) (n : ℕ) (f : E → A) : Prop :=
  Measurable f ∧ ∀ x, (x, f x) ∈ M.D n

end MDPFinance.Semicontinuous


