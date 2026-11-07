-- Prove2me | Definitions.Def_FairTeamContracts_optND
-- name    : FairTeamContracts_optND
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:31:46.920415+00:00
-- url     : https://prove2.me/theorems/daf9434f-e852-44f3-a4cd-73e154d910e4
-- title:
--   $\mathrm{OPT}_{nd}$ — optimal revenue of non-discriminatory team contracts
-- statement:
--   $\mathrm{OPT}_{nd}$ is the optimal revenue of non-discriminatory team contracts:
--
--   $$\mathrm{OPT}_{nd}=\max\{\mathrm{Rev}(S,\alpha):(S,\alpha)\text{ a feasible non-discriminatory team contract}\}.$$
--
--   **Formalization Note** $\mathrm{OPT}_{nd}$ is the supremum of $\mathrm{Rev}(S,\alpha)$ over all feasible non-discriminatory team contracts. The set is nonempty (the empty team) and bounded above by $1$ when $f$ is a success function.
-- source:
--   Chen, Castiglioni, Li, Fair Team Contracts, arXiv:2512.19388 (manuscript sha256 b8a12d9b…), Theorem 4.1, p.13

import Mathlib
import Definitions.Def_FairTeamContracts_IsNonDiscr
import Definitions.Def_FairTeamContracts_rev

namespace FairTeamContracts

/-- **OPT_nd, the optimal non-discriminatory revenue** (Chen, Castiglioni, Li, *Fair Team
Contracts*, arXiv:2512.19388 (manuscript sha256 b8a12d9b…), Theorem 4.1, p.13): the optimal
revenue of (feasible) non-discriminatory team contracts.

**Formalization Note.** OPT_nd is the supremum `sSup` of `Rev(S, α)` over all feasible
non-discriminatory team contracts. The set is nonempty (the empty team, revenue `0`) and bounded
above by `1` when `f` is a success function, so this is the paper's optimum (finitely many teams,
and for each team the revenue is maximized at the smallest feasible common share). -/
noncomputable def optND {n : ℕ} (f : Finset (Fin n) → ℝ) (c : Fin n → ℝ) : ℝ :=
  sSup {r : ℝ | ∃ (S : Finset (Fin n)) (α : Fin n → ℝ), IsNonDiscr f c S α ∧ rev f S α = r}

end FairTeamContracts


