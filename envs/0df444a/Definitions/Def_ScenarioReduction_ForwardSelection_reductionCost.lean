-- Prove2me | Definitions.Def_ScenarioReduction_ForwardSelection_reductionCost
-- name    : ScenarioReduction_ForwardSelection_reductionCost
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T14:56:19.010173+00:00
-- url     : https://prove2.me/theorems/7a7b51e9-c043-4762-9da8-acce34da0423
-- title:
--   Reduction cost $D_J=\sum_{i\in J}p_i\min_{j\notin J}c(\omega_i,\omega_j)$ of eq. (8)
-- statement:
--   Let $c=(c_{ij})_{i,j=1}^N$ be a cost matrix, $p_1,\dots,p_N$ scenario probabilities, and $J\subset\{1,\dots,N\}$ a set of scenarios to be deleted whose complement $\{1,\dots,N\}\setminus J$ is nonempty. The **reduction cost** of deleting $J$ is
--   $$
--   D_J=\sum_{i\in J}p_i\,\min_{j\notin J}c_{ij}.
--   $$
--   Each deleted scenario is charged its probability times the cost to the nearest kept scenario. Problem (8) of the paper minimizes $D_J$ over all $J$ of prescribed cardinality $N-n$; by Theorem 2.1, $D_J$ is the optimal transportation distance between the original measure and the best measure supported on the kept scenarios.
--
--   The file also records the elementary fact that the complement of $J\setminus\{v\}$ always contains $v$, so $D_{J\setminus\{v\}}$ is always defined.
--
--   **Formalization Note** The inner minimum is `Finset.inf'` over the complement $J^{\mathrm c}$, and the definition takes a proof that $J^{\mathrm c}$ is nonempty; there is no default value for $J=\{1,\dots,N\}$. The cost matrix is a general `Fin N → Fin N → ℝ`; every theorem of the mission instantiates it with the scenario cost of eq. (3).
-- source:
--   Heitsch, Römisch, Scenario Reduction Algorithms in Stochastic Programming, Comput. Optim. Appl. 24 (2003), p. 190, eq. (8)

import Mathlib

namespace ScenarioReduction.ForwardSelection

/-- The reduction cost of eq. (8), p. 190: for a set `J` of deleted scenarios whose complement is
nonempty, `D_J = ∑_{i ∈ J} pᵢ · min_{j ∉ J} c i j`. The inner minimum is a `Finset.inf'` over the
nonempty complement `Jᶜ`. -/
noncomputable def reductionCost {N : ℕ} (c : Fin N → Fin N → ℝ) (p : Fin N → ℝ)
    (J : Finset (Fin N)) (hJ : Jᶜ.Nonempty) : ℝ :=
  ∑ i ∈ J, p i * Jᶜ.inf' hJ (fun j => c i j)

/-- Removing `v` from any index set leaves `v` in the complement, so the complement is nonempty. -/
theorem compl_erase_nonempty {N : ℕ} (J : Finset (Fin N)) (v : Fin N) :
    ((J.erase v)ᶜ).Nonempty :=
  ⟨v, by simp⟩

end ScenarioReduction.ForwardSelection


