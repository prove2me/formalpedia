-- Prove2me | Definitions.Def_DGPNash_Gadget_AffectsGraph
-- name    : DGPNash_Gadget_AffectsGraph
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T18:08:18.092098+00:00
-- url     : https://prove2.me/theorems/90bd4eb8-5995-4be5-8a0e-27eb74a5e7ce
-- title:
--   Affects graph (Definition 2.2) and legal k-coloring (Definition 4.8)
-- statement:
--   Let $\mathcal{GG}$ be a game with player set $V$, and write $u^v$ for the payoff of player $v$ as a function of the pure strategy profile.
--
--   **Affects graph** (Definition 2.2). The affects graph of $\mathcal{GG}$ is the directed graph $G' = (V, E')$ with an edge $(v_1, v_2) \in E'$, for distinct players $v_1 \ne v_2$, if the payoff to $v_2$ depends on the action of $v_1$, that is, the payoff to $v_2$ is a nonconstant function of the action of $v_1$: there are a pure profile $s$ and two actions $a, b$ of $v_1$ such that changing $v_1$'s action in $s$ from $a$ to $b$, all other actions fixed, changes $u^{v_2}$.
--
--   **Legal coloring** (Definition 4.8). A game with affects graph $G = (V, E)$ can be legally colored with $k$ colors if there is a map $c : V \to \{1, 2, \dots, k\}$ such that
--   1. for every edge $e = (v, u) \in E$, $c(v) \ne c(u)$, and
--   2. for all edges $e_1 = (v, w)$, $e_2 = (u, w) \in E$ with $v \ne u$, $c(v) \ne c(u)$.
--
--   Such a $c$ is a legal $k$-coloring. Adjacent players get different colors, and so do any two players that affect a common player.
--
--   Legal colorings are what the paper's reduction from graphical games to normal-form games needs: each color class becomes one player of the normal-form game.
--
--   **Formalization Note** The edge relation is computed from the payoff functions, never typed in by hand. Self-loops are excluded (a player's payoff depends on its own action, and Definition 2.2 concerns pairs of players). Colors $\{1, \dots, k\}$ are represented by `Fin k` $= \{0, \dots, k-1\}$.
-- source:
--   Daskalakis, Goldberg & Papadimitriou, The Complexity of Computing a Nash Equilibrium, SIAM J. Comput. 39(1):195–259 (2009), p. 200, Definition 2.2; p. 219, Definition 4.8

import Mathlib

namespace DGPNash.Gadget

variable {ι : Type*} [DecidableEq ι]
variable {S : ι → Type*}

/-- The edge relation of the **affects graph** (Definition 2.2, p. 200): for distinct players
`v₁ ≠ v₂`, `Affects u v₁ v₂` holds when the payoff to `v₂` is a nonconstant function of the
action of `v₁`, i.e. there are a pure profile `s` and two actions `a, b` of `v₁` such that changing
`v₁`'s action from `a` to `b` (all other actions fixed) changes `v₂`'s payoff. Self-loops are
excluded. -/
def Affects (u : ι → (∀ i, S i) → ℝ) (v₁ v₂ : ι) : Prop :=
  v₁ ≠ v₂ ∧ ∃ (s : ∀ i, S i) (a b : S v₁),
    u v₂ (Function.update s v₁ a) ≠ u v₂ (Function.update s v₁ b)

/-- A **legal coloring** with `k` colors (Definition 4.8, p. 219) of a directed graph `E` on the
vertex set `ι`: the colors `{1, …, k}` are `Fin k`; adjacent vertices get distinct colors, and two
distinct vertices with a common successor get distinct colors. -/
def IsLegalColoring {k : ℕ} (E : ι → ι → Prop) (c : ι → Fin k) : Prop :=
  (∀ v w, E v w → c v ≠ c w) ∧
    (∀ v v' w, E v w → E v' w → v ≠ v' → c v ≠ c v')

/-- A game can be **legally colored with `k` colors** (Definition 4.8) if its affects graph
(Definition 2.2) has a legal coloring with `k` colors. -/
def IsLegallyColorable (u : ι → (∀ i, S i) → ℝ) (k : ℕ) : Prop :=
  ∃ c : ι → Fin k, IsLegalColoring (Affects u) c

end DGPNash.Gadget


