-- Prove2me | Definitions.Def_DigitalPrivacy_DataStrategy_SubgameEquilibrium
-- name    : DigitalPrivacy_DataStrategy_SubgameEquilibrium
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:03:14.414996+00:00
-- url     : https://prove2.me/theorems/5bacf7af-7b87-4199-9d6f-855b7218ace1
-- title:
--   Equilibrium $(\bar a,\omega)$ of the users–adversaries subgame
-- statement:
--   Fix the business's data strategy $(\xi,C)$ with $C>0$. A pair $(\bar a,\omega)$ is an **equilibrium of the users–adversaries subgame** if
--
--   1. $\bar a\ge 0$ and $\bar a$ maximizes $a\mapsto U_i(a,\bar a)$ over $a\ge 0$, when users expect average activity $\bar a$ and adversaries' demand $\omega$ (so the homogeneous users' common best reply is the average they expect);
--   2. $\omega=\bar a\,\xi/C$: with access cost $\gamma C$, $\gamma$ uniform on $[0,M]$ and $M\to\infty$, the active adversaries are those with $\gamma C\le\bar a\xi$, and their mass is $\bar a\xi/C$.
--
--   This is the second stage of the game: the business commits to $(\xi,C)$, then users and adversaries move simultaneously.
--
--   **Formalization Note** Utility (1) is strictly concave in $a_i$, so every user's best reply is unique and equilibria are symmetric; the profile is recorded by the pair $(\bar a,\omega)$. The definition is meant for $C>0$, where $\bar a\xi/C$ is defined.
-- source:
--   Fainmesser, Galeotti, Momot, Digital Privacy, author manuscript (April 2022 draft; SSRN 3459274), §2.2–2.4, pp. 7–9 (PDF 8–10), and proof of Proposition 1, App. A.1, p. 28 (PDF 29)

import Mathlib
import Definitions.Def_DigitalPrivacy_DataStrategy_userUtility

namespace DigitalPrivacy.DataStrategy

/-- **Equilibrium of the users–adversaries subgame (symmetric reduced form, `M → ∞`).**
Fainmesser, Galeotti, Momot, *Digital Privacy*, author manuscript (April 2022 draft; SSRN 3459274), §2.2–2.4, pp. 7–9 (PDF 8–10), and the proof of Proposition 1, App. A.1, p. 28 (PDF 29):
users choose `aᵢ ∈ ℝ₊` given correct expectations, and "the induced adversaries' demand for
information is ā(ω)ξ/C which should be consistent with the initial belief ω, hence ω should
solve ω = ā(ω)ξ/C".

`SubgameEquilibrium β ρ ξ C abar ω` holds iff `abar ≥ 0`, `abar` is a best reply of every user
over `aᵢ ≥ 0` to the average activity `abar` and the adversaries' demand `ω` (so that the
homogeneous users' common choice is the average they expect), and `ω = abar·ξ/C`.

**Formalization Note.** Users are homogeneous with strictly concave utility (1), so their best
reply is unique and every equilibrium is symmetric; the profile is therefore described by the
pair `(ā, ω)`. With `γ` uniform on `[0, M]` and `M → ∞` (p. 8), the mass of active adversaries
(those with `γC ≤ āξ`) is `āξ/C`. The definition is meant for `C > 0`; at `C = 0` Lean's
`x / 0 = 0` would make the adversaries' condition read `ω = 0`, and no theorem uses that case. -/
def SubgameEquilibrium (β ρ ξ C abar ω : ℝ) : Prop :=
  0 ≤ abar ∧
    (∀ a : ℝ, 0 ≤ a → userUtility β ρ ξ ω a abar ≤ userUtility β ρ ξ ω abar abar) ∧
    ω = abar * ξ / C

end DigitalPrivacy.DataStrategy


