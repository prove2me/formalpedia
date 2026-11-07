-- Prove2me | Definitions.Def_FairTeamContracts_IsFeasible
-- name    : FairTeamContracts_IsFeasible
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:29:48.392724+00:00
-- url     : https://prove2.me/theorems/649df86a-5cce-4b28-bb96-f1a52e17da52
-- title:
--   Feasible team contract: every team member is incentivized
-- statement:
--   A team contract $(S,\alpha)$ is **feasible** if all agents of the team are incentivized to exert costly effort when the whole team does:
--
--   $$\alpha_i\cdot f(S)-c_i\ \ge\ \alpha_i\cdot f(S\setminus\{i\})\qquad\text{for every }i\in S,$$
--
--   equivalently $\alpha_i\ge c_i/f(i\mid S\setminus\{i\})$ under the paper's conventions $0/0=0$, $c/0=\infty$. The paper assumes this for every team contract it considers.
--
--   **Formalization Note** The condition is stated in the multiplicative form above, with no division.
-- source:
--   Chen, Castiglioni, Li, Fair Team Contracts, arXiv:2512.19388 (manuscript sha256 b8a12d9b…), §2, p.8

import Mathlib

namespace FairTeamContracts

/-- **Feasible team contract** (Chen, Castiglioni, Li, *Fair Team Contracts*, arXiv:2512.19388
(manuscript sha256 b8a12d9b…), §2, p.8): all agents of the team are incentivized to exert costly
effort, i.e. `αᵢ · f(S) − cᵢ ≥ αᵢ · f(S∖{i})` for every `i ∈ S`. The paper assumes this "for all
team contracts (S, α) considered in our paper".

**Formalization Note.** This is the paper's first display on p.8, in multiplicative form. It is
equivalent to the paper's `αᵢ ≥ cᵢ / f(i | S∖{i})` under the paper's conventions `0/0 = 0`,
`c/0 = ∞`, and involves no division. -/
def IsFeasible {n : ℕ} (f : Finset (Fin n) → ℝ) (c : Fin n → ℝ) (S : Finset (Fin n))
    (α : Fin n → ℝ) : Prop :=
  ∀ i ∈ S, α i * f S - c i ≥ α i * f (S.erase i)

end FairTeamContracts


