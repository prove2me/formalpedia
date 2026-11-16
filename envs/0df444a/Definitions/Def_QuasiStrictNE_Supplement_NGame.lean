-- Prove2me | Definitions.Def_QuasiStrictNE_Supplement_NGame
-- name    : QuasiStrictNE_Supplement_NGame
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:38:36.132894+00:00
-- url     : https://prove2.me/theorems/c2768937-ff48-4a5c-b7a8-ca01657041b4
-- title:
--   $n$-player game in strategic form with rational payoffs
-- statement:
--   An **$n$-player game in strategic form with rational payoffs** consists of a number $k_i$ of pure actions for each player $i \in \{0,\dots,n-1\}$ and, for every player $i$ and every pure strategy profile $s = (s_0,\dots,s_{n-1})$ with $s_j \in \{0,\dots,k_j-1\}$, a rational payoff $u_i(s) \in \mathbb Q$. The whole payoff table is part of the game.
--
--   This is the input of the decision problem of Theorem 2.
--
--   **Formalization Note** Players and actions are 0-based (`Fin n`, `Fin (k i)`). The requirement that every player has at least one action is imposed where games are inputs, in the languages of Theorem 2.
-- source:
--   Hansen & Nie, On Existence and Computational Complexity of Quasi-strict Equilibria, arXiv:2611.06350 (preprint, sha256 c265dace…), Theorem 2 and its proof, p.19 (action sets $A_i$); p.3

import Mathlib

set_option autoImplicit false

namespace QuasiStrictNE.Supplement

/-- **An `n`-player game in strategic form with rational payoffs** (Hansen & Nie, *On Existence and
Computational Complexity of Quasi-strict Equilibria*, arXiv:2611.06350, §5, Theorem 2, p.19: "an
n-player game in strategic form with rational payoffs"; the action sets `Aᵢ` of the proof, p.19).

The players are `Fin n`. Player `i` has `k i` pure actions, the elements of `Fin (k i)`. A pure
strategy profile is a dependent function `s : (i : Fin n) → Fin (k i)`, and `u i s ∈ ℚ` is player
`i`'s payoff at `s`. The whole payoff table is part of the data (strategic form).

**Formalization Note** Players and actions are 0-based (`Fin n`, `Fin (k i)`). The condition that
every player has at least one action (`1 ≤ k i`) is not part of the structure; it is required where
games are inputs (`QSNEExists`, `QSNEExistsZS`). -/
structure NGame (n : ℕ) where
  /-- number of pure actions of each player -/
  k : Fin n → ℕ
  /-- payoff of each player at each pure strategy profile -/
  u : Fin n → ((i : Fin n) → Fin (k i)) → ℚ

end QuasiStrictNE.Supplement


