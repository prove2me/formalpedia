-- Prove2me | Definitions.Def_HarmonicGames_Projection_EpsEquilibrium
-- name    : HarmonicGames_Projection_EpsEquilibrium
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T05:42:31.398565+00:00
-- url     : https://prove2.me/theorems/d8774b90-4359-40ea-9537-4bad57ee7a6a
-- title:
--   $\epsilon$-equilibrium of a finite game, (2)
-- statement:
--   Consider a finite game with players $\mathcal M$, strategy sets $E^m$ and utilities $u^m : E \to \mathbb R$ on the strategy profiles $E = \prod_m E^m$. For a real number $\epsilon$, a strategy profile $p$ is an **$\epsilon$-equilibrium** if no player can gain more than $\epsilon$ by a unilateral deviation:
--
--   $$
--   u^m(p^m, p^{-m}) \ge u^m(q^m, p^{-m}) - \epsilon \qquad \text{for every } q^m \in E^m \text{ and } m \in \mathcal M. \qquad (2)
--   $$
--
--   A pure Nash equilibrium is an $\epsilon$-equilibrium with $\epsilon = 0$. The condition is monotone in $\epsilon$: an $\epsilon$-equilibrium is an $\epsilon'$-equilibrium for every $\epsilon' \ge \epsilon$. This is the approximate equilibrium notion used to compare a game with its closest potential game in Section 6.
--
--   **Formalization Note** The utilities are a plain function `u : ι → (∀ m, E m) → ℝ` with `u m p` $= u^m(p)$; the profile $(q^m, p^{-m})$ is `Function.update p m q`. This is a pure-profile notion, not the well-supported mixed $\epsilon$-Nash equilibrium.
-- source:
--   Candogan, Menache, Ozdaglar, Parrilo, Flows and Decompositions of Games: Harmonic and Potential Games, arXiv:1005.2405v2, p. 5, Section 2.1, (2)

import Mathlib

/-!
The `ϵ`-equilibrium of a finite strategic-form game, (2) of Candogan, Menache, Ozdaglar,
Parrilo (Section 2.1, p. 5).
-/

namespace HarmonicGames.Projection

variable {ι : Type} [DecidableEq ι] {E : ι → Type}

/-- **`ϵ`-equilibrium** (2): the strategy profile `p` is an `ϵ`-equilibrium of the game with
utilities `u` if `u^m(p^m, p^{-m}) ≥ u^m(q^m, p^{-m}) - ϵ` for every player `m` and every
strategy `q^m ∈ E^m`. The profile `(q^m, p^{-m})` is `Function.update p m q`. -/
def IsEpsEquilibrium (u : ι → (∀ m, E m) → ℝ) (ϵ : ℝ) (p : ∀ m, E m) : Prop :=
  ∀ (m : ι) (q : E m), u m (Function.update p m q) - ϵ ≤ u m p

end HarmonicGames.Projection


