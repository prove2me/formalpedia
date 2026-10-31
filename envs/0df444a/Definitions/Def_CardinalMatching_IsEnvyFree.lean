-- Prove2me | Definitions.Def_CardinalMatching_IsEnvyFree
-- name    : CardinalMatching_IsEnvyFree
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:26:30.961983+00:00
-- url     : https://prove2.me/theorems/4858f82d-3da3-4d0d-a9a9-64717ca9709b
-- title:
--   Envy-free allocation
-- statement:
--   Let $u_{ij}\ge 0$ be the utility of agent $i$ for good $j$ and write $u_i\cdot y = \sum_j u_{ij}y_j$. Given an allocation $x$, agent $i$ **envies** agent $i'$ if
--   $$
--   u_i\cdot x_i < u_i\cdot x_{i'} .
--   $$
--   The allocation $x$ is **envy-free** if no agent envies any other agent, i.e. $u_i\cdot x_{i'}\le u_i\cdot x_i$ for all agents $i, i'$.
--
--   This is ex-ante envy-freeness of the lottery $x$, the fairness notion of the mission's goal problem EF+PO.
--
--   **Formalization Note** The predicate does not itself require $x\in P_{\mathrm{PM}}$; membership is stated separately wherever the paper speaks of an allocation.
-- source:
--   Tröbst, Vazirani, Cardinal-Utility Matching Markets, arXiv:2402.08851v6, Definition 4, p.5

import Mathlib

namespace CardinalMatching

/-- **Envy-freeness** (Tröbst–Vazirani, *Cardinal-Utility Matching Markets*, arXiv:2402.08851v6,
Definition 4, p.5): given an allocation `x`, agent `i` envies agent `i'` if `u_i · x_i < u_i · x_i'`,
where `u_i · y = ∑_j u_ij y_j`; `x` is envy-free if no agent envies any other agent, i.e.
`u_i · x_i' ≤ u_i · x_i` for all agents `i, i'`.

**Formalization Note** Utilities are a real matrix `u : A → G → ℝ`; the predicate does not itself
require `x` to be an allocation (that is `IsFracPerfectMatching`, stated separately wherever the
paper speaks of an allocation). -/
def IsEnvyFree {A G : Type} [Fintype G] (u : A → G → ℝ) (x : A → G → ℝ) : Prop :=
  ∀ i i' : A, ∑ j, u i j * x i' j ≤ ∑ j, u i j * x i j

end CardinalMatching


