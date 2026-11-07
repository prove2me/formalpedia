-- Prove2me | Definitions.Def_FairTeamContracts_marg
-- name    : FairTeamContracts_marg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:29:47.441346+00:00
-- url     : https://prove2.me/theorems/3e48b292-132c-411e-ad72-7ce22dccefbe
-- title:
--   Marginal contribution $f(i\mid S\setminus\{i\})$ and cut-off wage $c_i/f(i\mid S\setminus\{i\})$
-- statement:
--   For a set function $f$, an agent $i$ and a set $S\ni i$, the **marginal contribution** of $i$ to $S$ is
--
--   $$f(i\mid S\setminus\{i\})\triangleq f(S)-f(S\setminus\{i\}).$$
--
--   For costs $c_i\ge0$, agent $i$'s **cut-off wage** in $S$ is
--
--   $$r_i(S)=\frac{c_i}{f(i\mid S\setminus\{i\})},$$
--
--   the smallest linear share at which $i$ is willing to exert effort when all other members of $S$ do.
--
--   **Formalization Note** The paper sets $0/0=0$ and $c/0=\infty$ for $c>0$; Lean's division gives $c/0=0$. The two differ only when $c_i>0$ and $f(i\mid S\setminus\{i\})=0$, which feasibility excludes for every member of a team contract. The file declares `marg` and `cutoff`.
-- source:
--   Chen, Castiglioni, Li, Fair Team Contracts, arXiv:2512.19388 (manuscript sha256 b8a12d9b…), §2, p.8

import Mathlib

namespace FairTeamContracts

/-- **Marginal contribution** `f(i | S∖{i}) ≜ f(S) − f(S∖{i})` (Chen, Castiglioni, Li,
*Fair Team Contracts*, arXiv:2512.19388 (manuscript sha256 b8a12d9b…), §2, p.8).

**Formalization Note.** `marg f i S` is the paper's `f(i | S∖{i})`; it is read for `i ∈ S`. -/
def marg {n : ℕ} (f : Finset (Fin n) → ℝ) (i : Fin n) (S : Finset (Fin n)) : ℝ :=
  f S - f (S.erase i)

/-- **Cut-off wage** of agent `i` in the set `S`, `cᵢ / f(i | S∖{i})` (Chen, Castiglioni, Li,
*Fair Team Contracts*, arXiv:2512.19388 (manuscript sha256 b8a12d9b…), §2, p.8).

**Formalization Note.** The paper sets `0/0 = 0` and `c/0 = ∞` for `c > 0` (p.8); Lean's real
division gives `c / 0 = 0`. The two differ only when `cᵢ > 0` and `f(i | S∖{i}) = 0`, and that case
is excluded for every `i ∈ S` of a feasible team contract, where `αᵢ · f(i | S∖{i}) ≥ cᵢ`. -/
noncomputable def cutoff {n : ℕ} (f : Finset (Fin n) → ℝ) (c : Fin n → ℝ) (S : Finset (Fin n))
    (i : Fin n) : ℝ :=
  c i / marg f i S

end FairTeamContracts


