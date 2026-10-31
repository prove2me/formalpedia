-- Prove2me | Definitions.Def_RandomPIGame_Value
-- name    : RandomPIGame_Value
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T20:25:36.945213+00:00
-- url     : https://prove2.me/theorems/69e7d33e-26b2-42bd-88e2-dafc98edcb80
-- title:
--   Strategies, plays, the payoff $u_\omega$, the value $v_\omega$ and $k$-optimal strategies
-- statement:
--   Let $\omega$ be a game. The play starts at the root. At a node $h$ of $T_\omega$ the game ends if $h$ is an end node; otherwise the active player $\iota_\omega(h)$ chooses a child $j\in\{1,\dots,\xi_\omega(h)\}$ and the node $(h,j)$ is reached. If $h_0=\oslash,h_1,h_2,\dots$ are the nodes visited, finitely or infinitely many, the payoff to Player I is $\inf\{\gamma_\omega(h_0),\gamma_\omega(h_1),\dots\}$. Player I maximizes it and Player II minimizes it.
--
--   A **strategy** of a player assigns a number $\sigma(h)\in\{1,\dots,\xi_\omega(h)\}$ to each node $h$ with $\xi_\omega(h)\ge1$ at which that player is active. A pair $(\sigma_{\mathrm I},\sigma_{\mathrm{II}})$ determines a play and hence a payoff $u_\omega(\sigma_{\mathrm I},\sigma_{\mathrm{II}})$. The **value** is
--   $$
--   v_\omega=\sup_{\sigma_{\mathrm I}}\inf_{\sigma_{\mathrm{II}}}u_\omega(\sigma_{\mathrm I},\sigma_{\mathrm{II}}).
--   $$
--   Player I's strategy $\sigma_{\mathrm I}$ is **$k$-optimal** if $u_\omega(\sigma_{\mathrm I},\sigma_{\mathrm{II}})\ge k$ for each $\sigma_{\mathrm{II}}$; Player II's strategy $\sigma_{\mathrm{II}}$ is $k$-optimal if $u_\omega(\sigma_{\mathrm I},\sigma_{\mathrm{II}})\le k$ for each $\sigma_{\mathrm I}$.
--
--   The value is the object whose distribution the mission determines.
--
--   **Formalization Note** A play is a sequence indexed by $\mathbb N$ that stays at an end node once reached; this does not change the set of capacities visited. Strategy types are nonempty (move to the first child) and every payoff lies in $[0,\gamma_\omega(\oslash)]$, so the real infimum and supremum are genuine. The threshold of `IsOptimalI` and `IsOptimalII` is real so that $v_\omega$ and $v_\omega+\varepsilon$ can be substituted.
-- source:
--   Flesch, Predtetchinski & Suomala, Random perfect information games, arXiv:2104.10528v1, §2, pp.8–9

import Mathlib
import Definitions.Def_RandomPIGame_Primitive
import Definitions.Def_RandomPIGame_Game

open scoped NNReal

namespace RandomPIGame

noncomputable section

namespace Game

/-- A strategy for player `i` in `ω` assigns a number `σ(h) ∈ {1, …, ξ_ω(h)}` to each node
`h ∈ T_ω` with `ι_ω(h) = i` and `ξ_ω(h) ≥ 1`. arXiv:2104.10528v1, §2, p.9.

**Formalization Note.** Every game has a strategy for each player (move to the first child), so the
suprema and infima of `value` range over nonempty types. -/
def Strategy (ω : Game) (i : Player) : Type :=
  (h : {h : ω.T // ω.ι h = i ∧ 1 ≤ ω.ξ h}) → {j : ℕ+ // (j : ℕ) ≤ ω.ξ h.1}

/-- The child recommended at a non-end node `h` by the strategy of the active player `ι_ω(h)`.
arXiv:2104.10528v1, §2, pp.8–9. -/
def move (ω : Game) (σI : ω.Strategy Player.I) (σII : ω.Strategy Player.II) (h : ω.T)
    (hξ : 1 ≤ ω.ξ h) : {j : ℕ+ // (j : ℕ) ≤ ω.ξ h} :=
  match hi : ω.ι h with
  | Player.I => σI ⟨h, hi, hξ⟩
  | Player.II => σII ⟨h, hi, hξ⟩

/-- One stage of play: an end node stays where it is; otherwise the active player moves to the
child recommended by their strategy. arXiv:2104.10528v1, §2, pp.8–9. -/
def next (ω : Game) (σI : ω.Strategy Player.I) (σII : ω.Strategy Player.II) (h : ω.T) : ω.T :=
  if hξ : 1 ≤ ω.ξ h then
    ⟨h.1 ++ [(ω.move σI σII h hξ).1], (ω.snoc_mem_iff h _).2 (ω.move σI σII h hξ).2⟩
  else h

/-- The sequence `h₀ = ⊘, h₁, h₂, …` of nodes visited under `(σ_I, σ_II)`.
arXiv:2104.10528v1, §2, p.8.

**Formalization Note.** A play that reaches an end node stays there. The sequence is indexed by all
of `ℕ`, and stuttering does not change the set of capacities visited. -/
def play (ω : Game) (σI : ω.Strategy Player.I) (σII : ω.Strategy Player.II) (t : ℕ) : ω.T :=
  (ω.next σI σII)^[t] ω.root

/-- The payoff `u_ω(σ_I, σ_II) = inf {γ_ω(h₀), γ_ω(h₁), …}` to Player I.
arXiv:2104.10528v1, §2, pp.8–9.

**Formalization Note.** The infimum is of a nonempty family of reals bounded below by `0`, so it is a
genuine infimum. -/
def payoff (ω : Game) (σI : ω.Strategy Player.I) (σII : ω.Strategy Player.II) : ℝ :=
  ⨅ t : ℕ, (ω.γ (ω.play σI σII t) : ℝ)

/-- The value `v_ω = sup_{σ_I} inf_{σ_II} u_ω(σ_I, σ_II)`. arXiv:2104.10528v1, §2, p.9.

**Formalization Note.** The strategy types are nonempty and `0 ≤ u_ω ≤ γ_ω(⊘)`, so both the real
infimum and the real supremum are genuine. The paper's equality with the inf sup is
`RandomPIGame.section2_value`. -/
def value (ω : Game) : ℝ :=
  ⨆ σI : ω.Strategy Player.I, ⨅ σII : ω.Strategy Player.II, ω.payoff σI σII

/-- Player I's strategy `σ_I` is `k`-optimal in `ω` if `u_ω(σ_I, σ_II) ≥ k` for each Player II's
strategy `σ_II`. arXiv:2104.10528v1, §2, p.9.

**Formalization Note.** `k` is real, so that `v_ω` and `v_ω + ε` can be substituted; these are
nonnegative, as in the paper's `k ≥ 0`. -/
def IsOptimalI (ω : Game) (k : ℝ) (σI : ω.Strategy Player.I) : Prop :=
  ∀ σII : ω.Strategy Player.II, k ≤ ω.payoff σI σII

/-- Player II's strategy `σ_II` is `k`-optimal in `ω` if `u_ω(σ_I, σ_II) ≤ k` for each Player I's
strategy `σ_I`. arXiv:2104.10528v1, §2, p.9. -/
def IsOptimalII (ω : Game) (k : ℝ) (σII : ω.Strategy Player.II) : Prop :=
  ∀ σI : ω.Strategy Player.I, ω.payoff σI σII ≤ k

end Game

end

end RandomPIGame


