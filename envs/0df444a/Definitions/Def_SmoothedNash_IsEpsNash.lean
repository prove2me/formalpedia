-- Prove2me | Definitions.Def_SmoothedNash_IsEpsNash
-- name    : SmoothedNash_IsEpsNash
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:48:39.572205+00:00
-- url     : https://prove2.me/theorems/3b9cd22b-6fa4-4414-b49c-220a761896ab
-- title:
--   $\varepsilon$-Nash equilibrium (pure-deviation form)
-- statement:
--   Let $u$ be a game and $\varepsilon \ge 0$. A mixed strategy profile $x = (x_1, \dots, x_m) \in (\Delta_n)^m$ is an **$\varepsilon$-Nash equilibrium** if no player can gain more than $\varepsilon$ by a unilateral deviation:
--   $$
--   u_i(a, x_{-i}) \le u_i(x) + \varepsilon \qquad \text{for every player } i \in [m] \text{ and every action } a \in [n].
--   $$
--   For $\varepsilon = 0$, $x$ is an exact Nash equilibrium.
--
--   Theorem 2.2 asserts that Algorithm 2 returns such a profile.
--
--   **Formalization Note** This is the pure-deviation form printed in the paper. Being a mixed profile (each $x_i$ a probability vector) is part of the definition, so no non-probability vector qualifies.
-- source:
--   Attias–Dagan–Daskalakis–Yao–Zampetakis, Nash Equilibria, Variational Inequalities, and Fixed Points: Beating Brute Force via Smoothed Analysis, STOC 2027 submission (manuscript sha256 3f9ea37d…77a1ea53), §1.1.2, p.6

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_SmoothedNash_Game
import Definitions.Def_SmoothedNash_devPayoff

namespace SmoothedNash

/-- An **`ε`-Nash equilibrium** (Attias–Dagan–Daskalakis–Yao–Zampetakis, *Nash Equilibria, Variational Inequalities, and Fixed Points: Beating Brute Force via Smoothed Analysis*, STOC 2027 submission manuscript (sha256 3f9ea37d…77a1ea53), §1.1.2, p.6): a mixed strategy profile `x ∈ (Δ_n)^m` such
that for every player `i` and every pure action `a`, `u_i(a, x_{-i}) ≤ u_i(x) + ε`. For `ε = 0` it
is an exact Nash equilibrium.

**Formalization Note** This is the pure-deviation form printed on p.6. Being a mixed profile (each
`x_i` a lottery, `AGT.IsMixedProfile`) is part of the definition. -/
def IsEpsNash {m n : ℕ} (u : Game m n) (ε : ℝ) (x : Fin m → Fin n → ℝ) : Prop :=
  AGT.IsMixedProfile (S := fun _ : Fin m => Fin n) x ∧
    ∀ i a, devPayoff u x i a ≤ AGT.expectedPayoff (S := fun _ : Fin m => Fin n) u x i + ε

end SmoothedNash


