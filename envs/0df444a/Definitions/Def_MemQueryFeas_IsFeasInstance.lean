-- Prove2me | Definitions.Def_MemQueryFeas_IsFeasInstance
-- name    : MemQueryFeas_IsFeasInstance
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:33:34.2142+00:00
-- url     : https://prove2.me/theorems/22743668-a3c3-4a87-bf54-184ef07f2702
-- title:
--   Feasibility instance of accuracy $\varepsilon$
-- statement:
--   A set $Q\subseteq\mathbb R^d$ is a **feasibility instance of accuracy $\varepsilon$** if
--   1. $Q\subseteq B_d(0,1)$, the closed unit ball;
--   2. $Q$ is convex;
--   3. $Q$ contains a closed Euclidean ball $\{y:\|y-c\|\le\varepsilon\}$ of radius $\varepsilon$.
--
--   The learner's goal is to query a point of $Q$, which it accesses only through a separation oracle.
--
--   **Formalization Note** The ball inside $Q$ is closed; this is the stronger requirement on $Q$.
-- source:
--   Yu–Blanchard, Exponential memory/query-complexity tradeoffs in high-accuracy feasibility problems, preprint (Nov. 3, 2026), Problem setup, p.3 (PDF p.4)

import Mathlib
import Definitions.Def_MemQueryFeas_Vec

namespace MemQueryFeas

/-- **Feasibility instance of accuracy `ε`.** Yu–Blanchard, *Exponential memory/query-complexity tradeoffs in high-accuracy feasibility problems*, preprint (Nov. 3, 2026), Problem setup, p.3 (PDF p.4): "the goal is to
find a point in an unknown convex set `Q ⊆ B_d(0, 1)` … that contains a Euclidean ball of radius `ϵ`".

`IsFeasInstance ε Q`: `Q` is a convex subset of the closed unit ball containing a closed ball of
radius `ε`.

**Formalization Note.** The unit ball `B_d(0,1)` is the closed ball, and the `ε`-ball inside `Q` is
required to be closed: this is the stronger requirement on `Q` (fewer instances), so success
hypotheses quantifying over instances become weaker. A convex `Q` containing a closed ball of
positive radius is nonempty. -/
def IsFeasInstance {d : ℕ} (ε : ℝ) (Q : Set (Vec d)) : Prop :=
  Q ⊆ Metric.closedBall 0 1 ∧ Convex ℝ Q ∧ ∃ c : Vec d, Metric.closedBall c ε ⊆ Q

end MemQueryFeas


