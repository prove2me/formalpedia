-- Prove2me | Definitions.Def_FairTeamContracts_IsTeamContract
-- name    : FairTeamContracts_IsTeamContract
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:29:47.017508+00:00
-- url     : https://prove2.me/theorems/7ab61016-d55b-4633-b984-ca377afc3104
-- title:
--   Team contract $(S,\alpha)$ with shares $\alpha_i\in[0,1]$
-- statement:
--   A **team contract** $(S,\alpha)$ consists of a team $S\subseteq N$ chosen by the principal and a linear share $\alpha_i\in[0,1]$ for each agent $i\in S$, paid to $i$ upon success of the project. Agents outside the team are paid nothing and do not exert effort.
--
--   **Formalization Note** The shares are a function $\alpha$ on all agents; only its values on $S$ are read, here and in every notion built on team contracts.
-- source:
--   Chen, Castiglioni, Li, Fair Team Contracts, arXiv:2512.19388 (manuscript sha256 b8a12d9b…), §2 Team Contracts, p.8

import Mathlib

namespace FairTeamContracts

/-- **Team contract** `(S, α)` (Chen, Castiglioni, Li, *Fair Team Contracts*, arXiv:2512.19388
(manuscript sha256 b8a12d9b…), §2 "Team Contracts", p.8): a team `S ⊆ N` and linear shares
`αᵢ ∈ [0, 1]` for the agents `i ∈ S`, paid upon success of the project.

**Formalization Note.** The shares are a function `α : Fin n → ℝ` on all agents; only the values
on `S` are read, here and in every predicate built on it (agents outside the team are paid zero
and exert no effort in the paper). -/
def IsTeamContract {n : ℕ} (S : Finset (Fin n)) (α : Fin n → ℝ) : Prop :=
  ∀ i ∈ S, 0 ≤ α i ∧ α i ≤ 1

end FairTeamContracts


