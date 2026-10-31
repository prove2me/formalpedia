-- Prove2me | Definitions.Def_SplitPMSGame_unitGame
-- name    : SplitPMSGame_unitGame
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:12:59.869698+00:00
-- url     : https://prove2.me/theorems/7d15d042-4cd0-4118-9ba8-1995356cb494
-- title:
--   Unit-speed $\{0,1\}$ PMS games, $c(z,u)$, symmetric allocations and $(\alpha_i,\beta_i)$ of (8)–(9)
-- statement:
--   A **unit-speed $\{0,1\}$ PMS game** has $z$ unit-speed 0 job players and $u$ unit-speed 1 job players: each owns a machine of speed $1$ and one job of requirement $0$ or $1$ respectively, and coalition costs are given by equation (1). $c(z,u)$ is the cost of the grand coalition. A **symmetric** allocation $(\alpha,\beta)$ allocates $\alpha$ to every 0-player and $\beta$ to every 1-player. For $z,u\ge1$,
--   $$
--   \alpha_1=-\frac{u(u+1)}{2(u+z)(u+z-1)},\qquad \beta_1=\frac{(u+1)(u+2z-1)}{2(u+z)(u+z-1)},
--   $$
--   $$
--   \alpha_2=-\frac{u(u-1)(z-1)}{2z(u+z)(u+z-1)},\qquad \beta_2=\frac{u(u+2z-1)}{2(u+z)(u+z-1)}.
--   $$
--
--   These games are the building blocks of the proof: their symmetric core is the segment between $(\alpha_1,\beta_1)$ and $(\alpha_2,\beta_2)$ (Theorem 2).
--
--   **Formalization Note** The players are `Fin (z + u)`, the first $z$ being the 0-players. The game is defined through the PMS cost (1), not through the closed form $k(k+1)/(2(k+\ell))$ of a coalition with $\ell$ 0-players and $k$ 1-players. $z,u$ are cast to $\mathbb R$ before subtracting.
-- source:
--   Alon, Anily, The Basic Core of a Parallel Machines Scheduling Game, MSOM 25(6) (2023), doi:10.1287/msom.2021.0337, Definition 5, p.2242 (PDF p.11); §5.2 and eq. (8)–(9), p.2243 (PDF p.12)

import Mathlib
import Definitions.Def_SplitPMSGame_pmsCost

namespace SplitPMSGame

/-- **Unit-speed {0, 1} PMS game** (Alon, Anily, *The Basic Core of a Parallel Machines
Scheduling Game*, MSOM 25(6) (2023), Definition 5, p.2242): "a PMS game in which each job player
owns a machine of unit speed and a job whose processing requirement is either zero or one". With
`z` unit-speed 0 job players and `u` unit-speed 1 job players, the players are `Fin (z + u)`, the
first `z` of them being the 0-players; the cost of a coalition is given by equation (1).

**Formalization Note** Defined as the PMS game (`pmsCost`) with one job per player (father map
`id`), unit speeds and requirement `0` for players `k < z`, `1` otherwise; the closed form
`k(k+1)/(2(k+ℓ))` of a coalition with `ℓ` 0-players and `k` 1-players is a consequence, not the
definition. -/
noncomputable def unitGame (z u : ℕ) : Finset (Fin (z + u)) → ℝ :=
  pmsCost (fun k : Fin (z + u) => if (k : ℕ) < z then 0 else 1) id (fun _ => 1)

/-- **`c(z, u)`** (MSOM 2023, §5.2, p.2243): "the cost of a coalition that consists of `z` (`u`)
unit-speed 0 (1) job players in a unit-speed {0, 1} PMS game", i.e. the cost of the grand
coalition of the unit-speed game with `z` 0-players and `u` 1-players. -/
noncomputable def cUnit (z u : ℕ) : ℝ :=
  unitGame z u Finset.univ

/-- **Symmetric cost allocation** `(α, β)` of the unit-speed {0, 1} game (MSOM 2023, §5.2,
p.2243): every unit-speed 0 job player (index `< z`) is allocated `α`, every unit-speed 1 job
player is allocated `β`. -/
def symAlloc (z u : ℕ) (α β : ℝ) : Fin (z + u) → ℝ :=
  fun k => if (k : ℕ) < z then α else β

/-- **`α₁(z, u)`** of equation (8) (MSOM 2023, p.2243): `α₁ = −u(u+1) / (2(u+z)(u+z−1))`, for
`z ≥ 1`, `u ≥ 1`. -/
noncomputable def alpha1 (z u : ℕ) : ℝ :=
  -((u : ℝ) * ((u : ℝ) + 1)) / (2 * ((u : ℝ) + z) * ((u : ℝ) + z - 1))

/-- **`β₁(z, u)`** of equation (8) (MSOM 2023, p.2243):
`β₁ = (u+1)(u+2z−1) / (2(u+z)(u+z−1))`, for `z ≥ 1`, `u ≥ 1`. -/
noncomputable def beta1 (z u : ℕ) : ℝ :=
  (((u : ℝ) + 1) * ((u : ℝ) + 2 * z - 1)) / (2 * ((u : ℝ) + z) * ((u : ℝ) + z - 1))

/-- **`α₂(z, u)`** of equation (9) (MSOM 2023, p.2243):
`α₂ = −u(u−1)(z−1) / (2z(u+z)(u+z−1))`, for `z ≥ 1`, `u ≥ 1`. -/
noncomputable def alpha2 (z u : ℕ) : ℝ :=
  -((u : ℝ) * ((u : ℝ) - 1) * ((z : ℝ) - 1)) / (2 * (z : ℝ) * ((u : ℝ) + z) * ((u : ℝ) + z - 1))

/-- **`β₂(z, u)`** of equation (9) (MSOM 2023, p.2243):
`β₂ = u(u+2z−1) / (2(u+z)(u+z−1))`, for `z ≥ 1`, `u ≥ 1`.

**Formalization Note** `z, u` are natural numbers cast to `ℝ` before any subtraction; the
denominators of (8)–(9) are positive for `z ≥ 1`, `u ≥ 1`, the only range in which the paper
uses them. -/
noncomputable def beta2 (z u : ℕ) : ℝ :=
  ((u : ℝ) * ((u : ℝ) + 2 * z - 1)) / (2 * ((u : ℝ) + z) * ((u : ℝ) + z - 1))

end SplitPMSGame


