-- Prove2me | Definitions.Def_Underdogs_Quality
-- name    : Underdogs_Quality
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:49:54.644041+00:00
-- url     : https://prove2.me/theorems/e481d13d-69e3-4a97-b783-656ea402b4b0
-- title:
--   Quality of an agent: high or low
-- statement:
--   The two quality levels of an agent in the model of Denrell, Liu and Maslach: **high** quality $H$ and **low** quality $L$. High-quality agents are those whose success probability is larger; the evaluator does not observe the quality and infers it from successes and failures.
--
--   **Formalization Note** `Quality` is a two-constructor type with the discrete σ-algebra, so that it can be a coordinate of the finite sample space $\text{Quality}\times\{S,F\}\times\{S,F\}$.
-- source:
--   Denrell, Liu, Maslach, Underdogs and One-Hit Wonders, Author's Accepted Manuscript (WRAP 165519, May 17, 2022), doi:10.1287/mnsc.2022.4630, §4, p.5 (PDF p.6)

import Mathlib

namespace Underdogs

/-- The two quality levels of an agent: high (`H`) and low (`L`).
Denrell, Liu, Maslach, *Underdogs and One-Hit Wonders: When Is Overcoming Adversity Impressive?*,
Author's Accepted Manuscript (WRAP 165519, May 17, 2022), doi:10.1287/mnsc.2022.4630, §4, p.5 (PDF p.6): "The agent can be of high or low quality".

**Formalization Note** `Quality` carries the discrete σ-algebra (every subset is measurable), so
that it can be a coordinate of the finite sample space of the two-period model. -/
inductive Quality
  | H
  | L
  deriving DecidableEq

instance : Fintype Quality := ⟨{Quality.H, Quality.L}, fun q => by cases q <;> simp⟩

instance : MeasurableSpace Quality := ⊤

instance : MeasurableSingletonClass Quality := ⟨fun _ => trivial⟩

end Underdogs


