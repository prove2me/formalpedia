-- Prove2me | Definitions.Def_ParetoIneff_Mech_TaskIndepAnon
-- name    : ParetoIneff_Mech_TaskIndepAnon
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:27:15.261903+00:00
-- url     : https://prove2.me/theorems/9d2b2004-6296-4c0d-b579-234cec1986ad
-- title:
--   Task-independent anonymous mechanism
-- statement:
--   A mechanism $\mathcal M$ is **task-independent and anonymous** if, for every number $m$ of tasks, it has a collection of single-task components $\{\mathcal A_j\}_{j=1,\dots,m}$ in the sense of Definition 1, all of them anonymous in the sense of Definition 2.
--
--   The components may depend on $m$ and may differ from task to task. This is the class in which the paper characterizes the Pareto frontier.
--
--   **Formalization Note** One existential covers both properties, so the anonymous mechanisms are the same ones that witness task-independence.
-- source:
--   Filos-Ratsikas, Giannakopoulos, Lazos, The Pareto frontier of inefficiency in mechanism design, arXiv:1809.03454v7 (24 Feb 2021), https://arxiv.org/abs/1809.03454v7, Definitions 1 and 2, p.6

import Mathlib
import Definitions.Def_ParetoIneff_Mech_IsComponents
import Definitions.Def_ParetoIneff_SingleTaskMech_IsAnonymous

open NNReal

namespace ParetoIneff

/-- `ℳ` is a **task-independent anonymous** mechanism, Definitions 1 and 2, arXiv:1809.03454v7,
p.6: for every number `m` of tasks there is a collection of single-task mechanisms
`{𝒜_j}_{j=1,…,m}` that are components of `ℳ` (Definition 1) and are all anonymous (Definition 2:
"A task-independent mechanism `ℳ` is anonymous, if all its components are anonymous").

**Formalization Note** One existential covers both properties, so anonymity is required of the
components that witness task-independence. The components may depend on `m` and may differ between
tasks (p.6: "the definition does not require the mechanism to necessarily use the same component
for all the tasks"). -/
def Mech.TaskIndepAnon {n : ℕ} (M : Mech n) : Prop :=
  ∀ m : ℕ, ∃ A : Fin m → SingleTaskMech n,
    M.IsComponents m A ∧ ∀ j : Fin m, (A j).IsAnonymous

end ParetoIneff


