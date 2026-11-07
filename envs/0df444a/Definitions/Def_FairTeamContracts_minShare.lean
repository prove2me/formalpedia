-- Prove2me | Definitions.Def_FairTeamContracts_minShare
-- name    : FairTeamContracts_minShare
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:30:59.787909+00:00
-- url     : https://prove2.me/theorems/08fa15b1-ae95-4496-8e20-a378daa15843
-- title:
--   Optimal minimum share $\mathcal L^*_S$, eq. (2)
-- statement:
--   For a team $S$ with $f(S)>0$, the **optimal minimum share** is
--
--   $$\mathcal L^*_S=\max_{i\in S}\Bigl\{\frac{c_i}{f(i\mid S\setminus\{i\})}\cdot\frac{f(S\setminus\{i\})}{f(S)}\Bigr\},$$
--
--   the largest cut-off wage of a team member, discounted by the fraction of $f(S)$ the rest of the team secures without that member. Theorem 3.2 shows that paying every member $\max\{\mathcal L^*_S,r_i(S)\}$ is the cheapest fair way to incentivize $S$.
--
--   **Formalization Note** The maximum over the empty team is $0$. Lean's $x/0=0$ is used: for $f(S)=0$ the value is $0$, which agrees with the paper's $0/0=0$ (a monotone $f\ge0$ then has $f(S\setminus\{i\})=0$); for the cut-off wage see `marg`.
-- source:
--   Chen, Castiglioni, Li, Fair Team Contracts, arXiv:2512.19388 (manuscript sha256 b8a12d9b…), Theorem 3.2, eq. (2), p.11

import Mathlib
import Definitions.Def_FairTeamContracts_marg

namespace FairTeamContracts

/-- **Optimal minimum share** `𝓛*_S`, eq. (2) (Chen, Castiglioni, Li, *Fair Team Contracts*,
arXiv:2512.19388 (manuscript sha256 b8a12d9b…), Theorem 3.2, eq. (2), p.11):
`𝓛*_S = max_{i ∈ S} { cᵢ / f(i | S∖{i}) · f(S∖{i}) / f(S) }`.

**Formalization Note.** This is the left form of (2). The maximum over the empty team is `0`.
Lean's `x / 0 = 0` agrees with the paper's `0/0 = 0` in `f(S∖{i}) / f(S)` (if `f(S) = 0` then
`f(S∖{i}) = 0` for a monotone `f ≥ 0`); for the cut-off wage see `cutoff`. -/
noncomputable def minShare {n : ℕ} (f : Finset (Fin n) → ℝ) (c : Fin n → ℝ)
    (S : Finset (Fin n)) : ℝ :=
  if h : S.Nonempty then S.sup' h (fun i => cutoff f c S i * (f (S.erase i) / f S)) else 0

end FairTeamContracts


