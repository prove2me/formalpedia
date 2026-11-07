-- Prove2me | Definitions.Def_FairTeamContracts_rev
-- name    : FairTeamContracts_rev
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:29:52.02099+00:00
-- url     : https://prove2.me/theorems/2f2aa60f-15a3-44ab-8732-f36247a2f875
-- title:
--   Principal's expected revenue $\mathrm{Rev}(S,\alpha)=(1-\sum_{i\in S}\alpha_i)f(S)$
-- statement:
--   The principal's **expected revenue** from a team contract $(S,\alpha)$ in which the whole team exerts effort is
--
--   $$\mathrm{Rev}(S,\alpha)=\Bigl(1-\sum_{i\in S}\alpha_i\Bigr)\cdot f(S).$$
-- source:
--   Chen, Castiglioni, Li, Fair Team Contracts, arXiv:2512.19388 (manuscript sha256 b8a12d9b…), §2, p.8

import Mathlib

namespace FairTeamContracts

/-- **Principal's expected revenue** `Rev(S, α) = (1 − ∑_{i ∈ S} αᵢ) · f(S)` (Chen, Castiglioni,
Li, *Fair Team Contracts*, arXiv:2512.19388 (manuscript sha256 b8a12d9b…), §2, p.8).

**Formalization Note.** Only the shares of team members enter the sum. -/
def rev {n : ℕ} (f : Finset (Fin n) → ℝ) (S : Finset (Fin n)) (α : Fin n → ℝ) : ℝ :=
  (1 - ∑ i ∈ S, α i) * f S

end FairTeamContracts


