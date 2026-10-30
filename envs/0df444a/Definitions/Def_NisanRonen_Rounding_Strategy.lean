-- Prove2me | Definitions.Def_NisanRonen_Rounding_Strategy
-- name    : NisanRonen_Rounding_Strategy
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:18:13.203627+00:00
-- url     : https://prove2.me/theorems/2abc8f81-9fed-466a-9a03-73d15aded570
-- title:
--   Strategy in a mechanism with verification: declaration and execution
-- statement:
--   In a mechanism with verification an agent's **strategy** has two parts:
--
--   1. a **declaration** $d^i = (d^i_1, \dots, d^i_k)$ of its type (a time for every task);
--   2. an **execution** $e^i$, which specifies for every decision of the mechanism, i.e. every allocation $x$, the time $e^i(x)_j$ in which the agent performs each task $j$ allocated to it.
--
--   The execution may depend on the agent's type as well as on the decision; the dependence on the type is carried by the choice of strategy, which is made per type.
-- source:
--   Nisan, Ronen, Algorithmic Mechanism Design, Games and Economic Behavior 35 (2001) 166–196, doi:10.1006/game.1999.0790, Definition 18, p. 186 (PDF p. 21): "An agent's strategy a^i is composed of two separate parts: a declaration d^i and an execution e^i", "The agent's execution e^i may depend on t^i as well as on k"; Definition 20, p. 187

import Mathlib

namespace NisanRonen.Rounding

/-- **A strategy of an agent in a mechanism with verification** (Nisan, Ronen, Algorithmic Mechanism Design, Games and Economic Behavior 35 (2001),
Definition 18, p. 186: "An agent's strategy a^i is composed of two separate parts: a declaration
d^i and an execution e^i"; "The agent's execution e^i may depend on t^i as well as on k";
Definition 20, p. 187: "A strategy for an agent is composed of two parts: a declaration of its
type and an execution of the tasks allocated to it").

`decl` is the declared type (a time for every task) and `exec x j` is the time in which the
agent performs task `j` when the mechanism's decision is the allocation `x` (only tasks with
`x j = i` are ever performed by agent `i`; the other entries are ignored).

**Formalization Note** The dependence of the execution on the agent's type is carried by the
choice of strategy, which is made per type (see `IsDominant`). -/
structure Strategy (n k : ℕ) where
  /-- the declared type `d^i` -/
  decl : Fin k → ℝ
  /-- the execution `e^i(x)`: actual times as a function of the decision `x` -/
  exec : (Fin k → Fin n) → Fin k → ℝ

end NisanRonen.Rounding


