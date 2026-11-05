-- Prove2me | Definitions.Def_BauerleRiederMDP_Stopping_lookAheadSet
-- name    : BauerleRiederMDP_Stopping_lookAheadSet
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:29:37.16744+00:00
-- url     : https://prove2.me/theorems/e58d1879-531d-4706-8234-b07db7b5d9b6
-- title:
--   The one-step stopping set $S_0$
-- statement:
--   For a stationary stopping problem with transition kernel $Q^X$, running reward $c$, stopping reward $g$ and discount factor $\beta\in(0,1]$, the one-step stopping set is
--
--   $$
--   S_0:=\Big\{x\in E\ \Big|\ g(x)\ge c(x)+\beta\int g(x')\,Q^X(dx'\mid x)\Big\}.
--   $$
--
--   It collects the states in which stopping now is at least as good as continuing once and stopping at the next step. It is the stopping region of the One-Step-Look-Ahead Rule.
--
--   **Formalization Note** The integral is $\int g^+-\int g^-$ in the extended reals, so $\int g\,dQ^X=-\infty$ is a genuine value.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), Theorem 10.2.7, p.315

import Mathlib
import Definitions.Def_MDPFinance_OptimalStopping_Stationary

open MeasureTheory
open MDPFinance.OptimalStopping

namespace BauerleRiederMDP.Stopping

/-- The **one-step stopping set** `S_0 := {x ∈ E | g(x) ≥ c(x) + β ∫ g(x') Q^X(dx'|x)}` of
Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), Theorem 10.2.7,
p.315 (PDF 323).

**Formalization Note.** `erealIntegral` is `∫ g⁺ − ∫ g⁻` in `[-∞,∞]`, so `∫ g = -∞` is a genuine
value (the point is then in `S_0`), never the `0` of a Bochner integral. -/
def lookAheadSet {E : Type*} [MeasurableSpace E] (P : StationaryProblem E) : Set E :=
  {x | (P.c x : EReal) + (P.beta : EReal) * erealIntegral (P.QX x) (fun y => (P.g y : EReal))
    ≤ (P.g x : EReal)}

end BauerleRiederMDP.Stopping


