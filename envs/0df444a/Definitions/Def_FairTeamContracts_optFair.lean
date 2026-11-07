-- Prove2me | Definitions.Def_FairTeamContracts_optFair
-- name    : FairTeamContracts_optFair
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:32:08.021819+00:00
-- url     : https://prove2.me/theorems/9c1c1d86-5d6c-4a7a-81fd-c05f5b1c7f74
-- title:
--   $\mathrm{OPT}$ — optimal revenue of fair team contracts
-- statement:
--   $\mathrm{OPT}$ is the optimal value of the program
--
--   $$\max_{(S,\alpha)}\ \mathrm{Rev}(S,\alpha)\quad\text{s.t. }(S,\alpha)\text{ is fair},$$
--
--   the revenue of an optimal fair team contract $(S^*,\alpha^*)$.
--
--   **Formalization Note** $\mathrm{OPT}$ is the supremum of $\mathrm{Rev}(S,\alpha)$ over all fair team contracts. The set is nonempty (the empty team is fair, with revenue $0$) and bounded above by $1$ when $f$ is a success function, so the supremum is the paper's maximum whenever that exists, which Theorem 3.2 guarantees.
-- source:
--   Chen, Castiglioni, Li, Fair Team Contracts, arXiv:2512.19388 (manuscript sha256 b8a12d9b…), program (Fair Team Contracts), p.9

import Mathlib
import Definitions.Def_FairTeamContracts_IsFair
import Definitions.Def_FairTeamContracts_rev

namespace FairTeamContracts

/-- **OPT, the optimal fair revenue** (Chen, Castiglioni, Li, *Fair Team Contracts*,
arXiv:2512.19388 (manuscript sha256 b8a12d9b…), program "(Fair Team Contracts)", p.9):
`OPT ≜ Rev(S*, α*)` for the optimal fair team contract `(S*, α*)` of
`max_{(S,α)} Rev(S, α)` s.t. `(S, α)` is fair.

**Formalization Note.** OPT is the supremum `sSup` of `Rev(S, α)` over all fair team contracts.
The set is nonempty (the empty team, revenue `0`, is fair) and bounded above by `1` when `f` is a
success function (shares are `≥ 0` and `f ≤ 1`), so this supremum is the paper's maximum whenever
the maximum exists, as it does by Theorem 3.2. -/
noncomputable def optFair {n : ℕ} (f : Finset (Fin n) → ℝ) (c : Fin n → ℝ) : ℝ :=
  sSup {r : ℝ | ∃ (S : Finset (Fin n)) (α : Fin n → ℝ), IsFair f c S α ∧ rev f S α = r}

end FairTeamContracts


