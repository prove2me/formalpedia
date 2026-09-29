-- Prove2me | Definitions.Def_ScenarioReduction_BinaryTree_IStar
-- name    : ScenarioReduction_BinaryTree_IStar
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T15:03:38.382424+00:00
-- url     : https://prove2.me/theorems/d60e9e67-4911-44a2-a55d-fae87f7dac04
-- title:
--   The index set $I_*$ of the proof of Proposition 3.1 (branch pattern at levels $k_0,k_0+1,k_0+2$)
-- statement:
--   Let $K\in\mathbb N$ and $k_0\in\{1,\dots,K-2\}$. For a scenario of the regular binary tree with branch indices $(i_1,\dots,i_K)\in\{1,2\}^K$, consider its branches at the three consecutive levels $k_0,k_0+1,k_0+2$. The set
--
--   $$I_*=\{\,i:\ i_{k_0}\neq i_{k_0+1}\ \text{and}\ i_{k_0+1}=i_{k_0+2}\,\}$$
--
--   collects the scenarios that turn at level $k_0$ one way and at both levels $k_0+1$ and $k_0+2$ the other way. When $\delta^{k_0},\delta^{k_0+1},\delta^{k_0+2}>0$ it coincides with the set the paper writes as
--
--   $$I_*=\{i:\ \operatorname{sign}(\delta^{k_0}_{i_{k_0}})=-\operatorname{sign}(\delta^{k_0+1}_{i_{k_0+1}})=-\operatorname{sign}(\delta^{k_0+2}_{i_{k_0+2}})\}.$$
--
--   Its complement $J_*$ is the set of deleted scenarios whose reduction cost attains the lower bound in Proposition 3.1.
--
--   **Formalization Note** The paper defines $I_*$ through the signs of $\delta^k_{i_k}=(2i_k-3)\delta^k$. If some $\delta^k=0$ for $k\in\{k_0,k_0+1,k_0+2\}$ the printed sign condition degenerates (with $\delta^{k_0}=\delta^{k_0+1}=\delta^{k_0+2}=0$ every index satisfies it and its cardinality is not $N/4$), while the proposition itself remains true. The set is therefore defined by the branch indices, which agrees with the printed definition whenever the three parameters are positive. The branch at level $k$ is `lev σ k` from the scenario definition.
-- source:
--   Heitsch, Römisch, Scenario Reduction Algorithms in Stochastic Programming, Comput. Optim. Appl. 24 (2003), p. 197, proof of Proposition 3.1, definition of I_* and J_*

import Mathlib
import Definitions.Def_ScenarioReduction_BinaryTree_scenario

namespace ScenarioReduction.BinaryTree

/-- The index set `I_*` of the proof of Proposition 3.1 (p. 197), stated by branch indices:
scenarios whose branch at level `k0` differs from the branch at level `k0 + 1`, and whose
branches at levels `k0 + 1` and `k0 + 2` agree. When `δ^{k0}, δ^{k0+1}, δ^{k0+2} > 0` this is
the paper's `{i : sign δ^{k0}_{i_{k0}} = -sign δ^{k0+1}_{i_{k0+1}} = -sign δ^{k0+2}_{i_{k0+2}}}`. -/
def IStar (K k0 : ℕ) : Finset (Fin K → Fin 2) :=
  Finset.univ.filter (fun σ => lev σ k0 ≠ lev σ (k0 + 1) ∧ lev σ (k0 + 1) = lev σ (k0 + 2))

end ScenarioReduction.BinaryTree


