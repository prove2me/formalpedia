-- Prove2me | Definitions.Def_ScenarioApproach_Nonconvex_supportSet
-- name    : ScenarioApproach_Nonconvex_supportSet
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-30T18:39:35.690983+00:00
-- url     : https://prove2.me/theorems/91f03313-cbe6-448a-9760-618d8293d585
-- title:
--   Definition 8.8 — support set of a nonconvex scenario program
-- statement:
--   Consider the scenario program (8.12) with cost $f$ over a generic set $\Theta$ and sampled constraints $\Theta_{\delta_1},\dots,\Theta_{\delta_N}$. A subset $\{\Theta_{\delta_{i_1}},\dots,\Theta_{\delta_{i_k}}\}$ of the constraints, identified with the index set $I=\{i_1,\dots,i_k\}$, is a **support set** if the program with only these constraints in place has the same solution as the program with all constraints:
--
--   $$
--   \theta^*=\arg\min_{\theta\in\Theta}\{f(\theta):\ \theta\in\textstyle\bigcap_{i=1}^N\Theta_{\delta_i}\}
--   =\arg\min_{\theta\in\Theta}\{f(\theta):\ \theta\in\textstyle\bigcap_{i\in I}\Theta_{\delta_i}\},
--   $$
--
--   where both minimizers exist and are unique. The full index set is always a support set whenever the full program has a unique solution. A support set need not be minimal or irreducible.
--
--   Support sets replace support constraints in the nonconvex theory: the number of constraints that determine the solution is no longer bounded by the dimension, and the violation of the solution is certified by the cardinality of a support set found a posteriori.
--
--   **Formalization Note** "Has the same solution" is read as: the full program has a unique solution $\theta$, and $\theta$ is also the unique solution of the reduced program. Uniqueness in the reduced program is part of the page's phrase "the solution"; without it the reduced program would not determine $\theta^*$.
-- source:
--   Campi & Garatti, Introduction to the Scenario Approach, SIAM/MOS 2018, DOI 10.1137/1.9781611975444, p. 104, Definition 8.8

import Mathlib
import Definitions.Def_ScenarioApproach_Nonconvex_scenarioProgram

namespace ScenarioApproach.Nonconvex

/-- Definition 8.8 (support set). For the scenario program (8.12) with constraints
`Θ_{δ_{ω 0}}, …, Θ_{δ_{ω (N-1)}}`, the index set `I` is a support set if the program with
all constraints has a (unique) solution `θ`, and the program with only the constraints
indexed by `I` in place has the same solution: `θ` is also its unique solution. -/
def IsSupportSet {Θ Δ : Type*} {N : ℕ} (f : Θ → ℝ) (Θδ : Δ → Set Θ) (ω : Fin N → Δ)
    (I : Finset (Fin N)) : Prop :=
  ∃ θ, IsUniqueSolutionOn f Θδ ω Finset.univ θ ∧ IsUniqueSolutionOn f Θδ ω I θ

end ScenarioApproach.Nonconvex


