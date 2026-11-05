-- Prove2me | Definitions.Def_PureNashHard_Game
-- name    : PureNashHard_Game
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:37:12.835833+00:00
-- url     : https://prove2.me/theorems/447d2116-bd31-4aca-9da2-3dcf054e18fd
-- title:
--   Game $\langle P,\mathrm{Neigh},\mathrm{Act},U\rangle$, global strategies and $u_p(x)$
-- statement:
--   A **game** $G=\langle P,\mathrm{Neigh},\mathrm{Act},U\rangle$ consists of a non-empty set $P$ of players, for each player $p$ a set $\mathrm{Neigh}(p)\subseteq P\setminus\{p\}$ of neighbours and a set $\mathrm{Act}(p)$ of actions, and for each player $p$ a utility function
--   $$
--   u_p:\mathrm{Act}(p)\times\textstyle\prod_{j\in\mathrm{Neigh}(p)}\mathrm{Act}(j)\to R .
--   $$
--   A **global strategy** (profile) $x$ chooses one action for every player. With a small abuse of notation, $u_p(x)$ is the value of $u_p$ on the projection of $x$ to the actions of $p$ and her neighbours.
--
--   The module fixes the data of a game and the conditions of the paper on it (`Game.WellFormed`): at least one player, at least one action per player, and neighbour sets that do not contain the player herself. Every complexity statement of the mission is about such games.
--
--   **Formalization Note** The players are $0,\dots,N-1$ (`Fin N`) and the actions of $p$ are $0,\dots,\mathrm{act}(p)-1$. The neighbours of $p$ are a list without repetitions; its order fixes the order in which the neighbours' actions are passed to $u_p$, which receives the list of action indices of $p$ followed by her neighbours. The structure itself holds data only; the paper's conditions are the separate predicate `Game.WellFormed`.
-- source:
--   Gottlob, Greco, Scarcello, Pure Nash Equilibria: Hard and Easy Games, JAIR 24 (2005), doi:10.1613/jair.1683, §2, p.365 (PDF p.9): the game ⟨P, Neigh, Act, U⟩, global strategies, u_p(x) on the projection

import Mathlib

set_option autoImplicit false

namespace PureNashHard

/-- **Game** ⟨P, Neigh, Act, U⟩ (Gottlob, Greco, Scarcello, *Pure Nash Equilibria: Hard and Easy
Games*, JAIR 24 (2005), §2, p.365): a non-empty set of players `P`, a neighbourhood function
with `Neigh(p) ⊆ P − {p}`, a set of actions `Act(p)` for each player and, for each player `p`,
a utility function `u_p : Act(p) × ×_{j ∈ Neigh(p)} Act(j) → R`.

**Formalization Note**
1. The players are `Fin N` and the actions of `p` are `Fin (act p)`.
2. `neigh p` lists `Neigh(p)` in a fixed order; that order fixes the order in which the
   neighbours' actions are passed to `u_p`.
3. `util p` receives the list of action indices of `p :: neigh p`, in that order: the
   argument `(a_p, a_{j₁}, …, a_{j_k})` of the paper's `u_p`. Its values on lists that are not
   such tuples are never used.
4. The structure holds data only. The conditions of the paper on that data (non-empty player
   set, non-empty action sets, `Neigh(p) ⊆ P − {p}` without repetitions) are
   `Game.WellFormed`. -/
structure Game (R : Type) where
  /-- The number of players; the players are `Fin N`. -/
  N : ℕ
  /-- The number of actions of each player; the actions of `p` are `Fin (act p)`. -/
  act : Fin N → ℕ
  /-- The neighbours of each player, as a list. -/
  neigh : Fin N → List (Fin N)
  /-- The utility of `p`, as a function of the actions of `p :: neigh p`. -/
  util : Fin N → List ℕ → R

/-- The conditions of p.365 on a game: `P` is non-empty, every player has an action, and
`Neigh(p)` is a set of players other than `p` (listed without repetitions). JAIR 24 (2005),
§2, p.365. -/
def Game.WellFormed {R : Type} (G : Game R) : Prop :=
  0 < G.N ∧ (∀ p, 0 < G.act p) ∧ ∀ p, (G.neigh p).Nodup ∧ p ∉ G.neigh p

/-- A **global strategy** (profile) of `G`: one action for every player (JAIR 24 (2005),
p.365, "A combined strategy (also, profile) x is called global if all players contribute to
it"). -/
abbrev Game.Profile {R : Type} (G : Game R) : Type := (p : Fin G.N) → Fin (G.act p)

/-- The projection of a global strategy `x` to the domain of `u_p`: the action indices of `p`
and of her neighbours, in the order `p :: neigh p`. JAIR 24 (2005), p.365. -/
def Game.localActions {R : Type} (G : Game R) (x : G.Profile) (p : Fin G.N) : List ℕ :=
  (p :: G.neigh p).map (fun q => ((x q : Fin (G.act q)) : ℕ))

/-- `u_p(x)`: "the output of the function `u_p` applied to the actions played by `p` and her
neighbors according to the strategy `x`" (JAIR 24 (2005), p.365). -/
def Game.utility {R : Type} (G : Game R) (p : Fin G.N) (x : G.Profile) : R :=
  G.util p (G.localActions x p)

end PureNashHard


