-- Prove2me | Definitions.Def_FairTeamContracts_leastIncentive
-- name    : FairTeamContracts_leastIncentive
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:30:57.182266+00:00
-- url     : https://prove2.me/theorems/f11aa41e-58ca-4223-b1b9-3e024c83caa8
-- title:
--   Definition 3.1 — least $S$-incentive contract with minimum share $\mathcal L$
-- statement:
--   For $\mathcal L\ge0$ and $S\subseteq[n]$, the **least $S$-incentive contract with minimum share $\mathcal L$** is the team contract $(S,\alpha)$ with $\alpha_i=0$ for $i\notin S$ and
--
--   $$\alpha_i=\max\Bigl\{\mathcal L,\ \frac{c_i}{f(i\mid S\setminus\{i\})}\Bigr\}\qquad\text{for }i\in S:$$
--
--   every member is paid at least the floor $\mathcal L$ and at least its own cut-off wage.
--
--   **Formalization Note** The shares are uniquely determined by $(S,\mathcal L)$, so the definition is the share function itself; "$(S,\alpha)$ is a least $S$-incentive contract with minimum share $\mathcal L$" means $\alpha$ equals it. The cut-off wage uses Lean's $x/0=0$ (see `marg`).
-- source:
--   Chen, Castiglioni, Li, Fair Team Contracts, arXiv:2512.19388 (manuscript sha256 b8a12d9b…), Definition 3.1, p.11

import Mathlib
import Definitions.Def_FairTeamContracts_marg

namespace FairTeamContracts

/-- **Definition 3.1 (Minimum-share Structure)** (Chen, Castiglioni, Li, *Fair Team Contracts*,
arXiv:2512.19388 (manuscript sha256 b8a12d9b…), Definition 3.1, p.11). For `𝓛 ≥ 0` and `S ⊆ [n]`,
the least `S`-incentive contract with minimum share `𝓛` has `αᵢ = 0` for `i ∉ S` and
`αᵢ = max{𝓛, cᵢ / f(i | S∖{i})}` for `i ∈ S`.

**Formalization Note.** The paper's "a team contract `(S, α)` is a least `S`-incentive contract with
a minimum share `𝓛`" means `α = leastIncentive f c S 𝓛`; the shares are uniquely determined. The
cut-off wage uses Lean's `x / 0 = 0` (see `cutoff`). -/
noncomputable def leastIncentive {n : ℕ} (f : Finset (Fin n) → ℝ) (c : Fin n → ℝ)
    (S : Finset (Fin n)) (L : ℝ) (i : Fin n) : ℝ :=
  if i ∈ S then max L (cutoff f c S i) else 0

end FairTeamContracts


