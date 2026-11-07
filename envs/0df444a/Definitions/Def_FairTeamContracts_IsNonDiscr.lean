-- Prove2me | Definitions.Def_FairTeamContracts_IsNonDiscr
-- name    : FairTeamContracts_IsNonDiscr
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:30:46.427284+00:00
-- url     : https://prove2.me/theorems/32cb986c-a14a-4829-b082-48e1e4166d40
-- title:
--   Definition 2.7 — non-discriminatory team contract ($\alpha_i=\alpha_j$ on $S$)
-- statement:
--   A team contract $(S,\alpha)$ is **non-discriminatory** if
--
--   $$\alpha_i=\alpha_j\qquad\text{for all }i,j\in S,$$
--
--   i.e. every hired agent receives the same share. Non-discriminatory contracts are fair (Proposition 2.8), and they are the simple class whose revenue loss against fair contracts is measured.
--
--   **Formalization Note** As everywhere in the paper, the contract is also required to be a feasible team contract (shares in $[0,1]$, every member incentivized).
-- source:
--   Chen, Castiglioni, Li, Fair Team Contracts, arXiv:2512.19388 (manuscript sha256 b8a12d9b…), Definition 2.7, p.10

import Mathlib
import Definitions.Def_FairTeamContracts_IsTeamContract
import Definitions.Def_FairTeamContracts_IsFeasible

namespace FairTeamContracts

/-- **Definition 2.7 (Non-discriminatory Team Contracts)** (Chen, Castiglioni, Li, *Fair Team
Contracts*, arXiv:2512.19388 (manuscript sha256 b8a12d9b…), Definition 2.7, p.10). A team
contract `(S, α)` is non-discriminatory if `αᵢ = αⱼ` for all `i, j ∈ S`.

**Formalization Note.** The paper considers only feasible team contracts ("We assume that the
above inequalities hold for all team contracts (S, α) considered in our paper", p.8), so the
predicate bundles `IsTeamContract S α ∧ IsFeasible f c S α` with the equal-shares condition. -/
def IsNonDiscr {n : ℕ} (f : Finset (Fin n) → ℝ) (c : Fin n → ℝ) (S : Finset (Fin n))
    (α : Fin n → ℝ) : Prop :=
  IsTeamContract S α ∧ IsFeasible f c S α ∧ ∀ i ∈ S, ∀ j ∈ S, α i = α j

end FairTeamContracts


