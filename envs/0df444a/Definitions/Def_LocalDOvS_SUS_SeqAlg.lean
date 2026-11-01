-- Prove2me | Definitions.Def_LocalDOvS_SUS_SeqAlg
-- name    : LocalDOvS_SUS_SeqAlg
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:24:53.327215+00:00
-- url     : https://prove2.me/theorems/a92378d3-13d9-4ace-a681-af1541734992
-- title:
--   Sequential simulation-optimization algorithm
-- statement:
--   A **sequential algorithm** is a rule that maps the history of the evaluations made so far, the ordered list of pairs (decision, observed output), to its next step.
--
--   This is the class of procedures over which Definition 1 ($(\mathcal O,\mathcal M)$-algorithms) and Definition 2 (expected simulation cost) quantify: the algorithm adapts to what it has observed, but it never sees the objective or the laws.
--
--   **Formalization Note** The rule is deterministic and may depend on the problem parameters $N,\sigma,\epsilon,\delta$ through its construction; measurability and the range of decisions are separate predicates.
-- source:
--   Zhang, Zheng, Lavaei, Stochastic Localization Methods for Convex Discrete Optimization via Simulation, arXiv:2012.02427v2, Definition 1, p.9; Definition 2, p.10

import Mathlib
import Definitions.Def_LocalDOvS_SUS_Step

namespace LocalDOvS.SUS

/-- A (deterministic, sequential) simulation-optimization algorithm (Zhang–Zheng–Lavaei,
arXiv:2012.02427v2, Definition 1, p.9, and Definition 2, p.10): a rule that maps the history of
the evaluations made so far — the list of `(decision, observed output)` pairs, in order — to the
next `Step`.

**Formalization Note.** The algorithm sees only the outputs, never `f` or the laws; it may depend
on the problem parameters `N, σ, ε, δ` through its construction. Measurability and the range of
decisions are separate predicates (`IsMeasurableAlg`, `IsValidAlg`). -/
abbrev SeqAlg : Type := List (ℕ × ℝ) → Step

end LocalDOvS.SUS


