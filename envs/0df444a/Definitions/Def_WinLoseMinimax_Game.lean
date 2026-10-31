-- Prove2me | Definitions.Def_WinLoseMinimax_Game
-- name    : WinLoseMinimax_Game
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:24:18.19162+00:00
-- url     : https://prove2.me/theorems/77dd3d56-2481-48ad-8754-3c5dda973a5f
-- title:
--   Definitions 1.1, 1.2, 1.4, 2.8 — win-lose games, mixed payoff, minimax property, totally minimax, LNG, LNG-free
-- statement:
--   A **two-person win-lose game** (Definition 1.1, p.2) is a triple $G=(S,T,\pi)$: $S$ and $T$ are the non-empty, possibly infinite, sets of pure strategies of players 1 and 2, and $\pi:S\times T\to\{0,1\}$ is the payoff; $\pi(s,t)=1$ is a win of player 1 and $\pi(s,t)=0$ a win of player 2.
--
--   A **mixed strategy** on a set $X$ is a probability distribution on $X$ with at most countable support; $\Delta(X)$ is the set of them (p.3). For $p\in\Delta(S)$, $q\in\Delta(T)$,
--
--   $$\pi_{\mathrm{mix}}(p,q)=\mathbb E_{(s,t)\sim p\times q}\,\pi(s,t)=\sum_{s\in S}\sum_{t\in T}p_s\,q_t\,\pi(s,t),$$
--
--   the probability that player 1 wins. The module defines:
--
--   1. the **minimax property** (Definition 1.2, equation (2), p.3): $\sup_{p\in\Delta(S)}\inf_{q\in\Delta(T)}\pi_{\mathrm{mix}}(p,q)=\inf_{q\in\Delta(T)}\sup_{p\in\Delta(S)}\pi_{\mathrm{mix}}(p,q)$;
--   2. a **value with optimal strategies**: $v$ such that some $p^*$ guarantees $\pi_{\mathrm{mix}}(p^*,q)\ge v$ for every $q$ and some $q^*$ guarantees $\pi_{\mathrm{mix}}(p,q^*)\le v$ for every $p$ (the "value" of a finite game, used in Step 2 of the proofs of Theorems 2.2 and 3.1);
--   3. the **subgame** on $S'\subseteq S$, $T'\subseteq T$ with the restricted payoff (Definition 1.4, p.4);
--   4. **totally minimax** (Definition 1.4): every subgame, with $S'$ and $T'$ non-empty, has the minimax property;
--   5. the **larger number game** LNG (Example 1.3, p.3): both players pick a positive integer, $\pi(s,t)=1$ iff $s\ge t$;
--   6. **isomorphism** of games (bijections of the strategy sets preserving the payoff, players keeping their roles) and **LNG-free** (Definition 2.8, p.9): no subgame is isomorphic to LNG.
--
--   These are the objects of the paper's main theorem: a game is totally minimax if and only if it is LNG-free.
--
--   **Formalization Note** Payoffs are `Bool` (`true` = 1). $\Delta(X)$ is Mathlib's `PMF X`, whose support is automatically countable. $\pi_{\mathrm{mix}}$ and all suprema and infima are in $[0,\infty]$ (`ℝ≥0∞`). Subgames are subtypes of `Set`s; non-emptiness of $S'$, $T'$ (a subgame is a game) is imposed in the definition of totally minimax. LNG is indexed by $\mathbb N=\{0,1,\dots\}$, which is isomorphic to the paper's positive integers.
-- source:
--   Holzman, The minimax property in infinite two-person win-lose games, arXiv:2310.19314v1, Definition 1.1 p.2; mixed strategies and π_mix p.3; Definition 1.2 eq. (2) p.3; Example 1.3 p.3; Definition 1.4 p.4; Definition 2.8 p.9; value of a finite game §1 p.2 and proof of Theorem 2.2 Step 2 p.6

import Mathlib

open scoped ENNReal

namespace WinLoseMinimax

universe u v u' v'

/-- **Mixed payoff of a two-person win-lose game.** Holzman, *The minimax property in infinite
two-person win-lose games*, arXiv:2310.19314v1, Definition 1.1, p.2 and §1, p.3.

A game `G = (S, T, π)` has pure strategy sets `S` (player 1) and `T` (player 2) and payoff
`π : S × T → {0, 1}`, where `1` is a win of player 1 and `0` a win of player 2. For mixed
strategies `p ∈ ∆(S)`, `q ∈ ∆(T)` (probability distributions with at most countable support),
`π_mix(p, q) = E_{(s,t) ∼ p × q} π(s, t)`, the probability that player 1 wins under `p × q`.

**Formalization Note.** The payoff is `π : S → T → Bool` (`true` = payoff 1 = player 1 wins).
Mixed strategies are Mathlib's `PMF`: a `PMF` has at most countable support automatically
(`PMF.support_countable`), so `PMF X` is exactly the paper's `∆(X)` for any type `X`. The value
`π_mix(p, q)` is the double sum `∑ₛ ∑ₜ p(s) q(t) [π(s,t) = 1]` in `ℝ≥0∞`; it lies in `[0, 1]`. A pure
strategy `s` is the Dirac `PMF.pure s`. -/
noncomputable def payoff {S : Type u} {T : Type v} (π : S → T → Bool) (p : PMF S) (q : PMF T) :
    ℝ≥0∞ :=
  ∑' s, ∑' t, p s * q t * (if π s t then 1 else 0)

/-- **Minimax property.** Holzman, arXiv:2310.19314v1, Definition 1.2, equation (2), p.3: the game
`G = (S, T, π)` satisfies the minimax property if
`sup_{p ∈ ∆(S)} inf_{q ∈ ∆(T)} π_mix(p, q) = inf_{q ∈ ∆(T)} sup_{p ∈ ∆(S)} π_mix(p, q)`.

**Formalization Note.** The supremum and infimum are `⨆`/`⨅` in the complete lattice `ℝ≥0∞`
over all of `PMF S` / `PMF T` (= `∆(S)`, `∆(T)`); no attainment is asserted. The paper's games
have non-empty `S`, `T`; this definition is applied only to such games (for an empty type the
`⨆` is `0` and the `⨅` is `⊤`). -/
def MinimaxProperty {S : Type u} {T : Type v} (π : S → T → Bool) : Prop :=
  (⨆ p : PMF S, ⨅ q : PMF T, payoff π p q) = ⨅ q : PMF T, ⨆ p : PMF S, payoff π p q

/-- **Value with optimal strategies.** Holzman, arXiv:2310.19314v1, proof of Theorem 2.2, Step 2,
p.6 ("the game `Gₙ` has a value `vₙ`") together with the optimal strategies used in Steps 3 and 4,
p.7: `v` is the value of the game and both players have optimal mixed strategies, i.e. some
`p*` guarantees player 1 at least `v` against every `q`, and some `q*` holds player 1 to at most
`v` against every `p`.

**Formalization Note.** This is the finite-game notion of value of §1, p.2 (the common value of
both sides of equation (1), attained by optimal strategies); it implies `sup inf = inf sup = v`. -/
def HasValue {S : Type u} {T : Type v} (π : S → T → Bool) (v : ℝ≥0∞) : Prop :=
  (∃ p : PMF S, ∀ q : PMF T, v ≤ payoff π p q) ∧ (∃ q : PMF T, ∀ p : PMF S, payoff π p q ≤ v)

/-- **Subgame.** Holzman, arXiv:2310.19314v1, Definition 1.4, p.4: for `S' ⊆ S`, `T' ⊆ T`, the
subgame `G' = (S', T', π')` has `π'` the restriction of `π` to `S' × T'`.

**Formalization Note.** Subsets are `Set`s and the restricted game lives on the subtypes `↥S'`,
`↥T'`. Non-emptiness of `S'`, `T'` (a subgame is a game, Definition 1.1) is imposed where
subgames are quantified over (`TotallyMinimax`). -/
def restrict {S : Type u} {T : Type v} (π : S → T → Bool) (S' : Set S) (T' : Set T) :
    S' → T' → Bool :=
  fun s t => π s t

/-- **Totally minimax.** Holzman, arXiv:2310.19314v1, Definition 1.4, p.4: the game `G` is
totally minimax if every subgame `G'` of `G` satisfies the minimax property.

**Formalization Note.** A subgame is a game, so by Definition 1.1, p.2 ("The sets S, T are
non-empty") both `S'` and `T'` are non-empty; this is required here. (With `S' = T' = ∅`
equation (2) would read `0 = ⊤` in `ℝ≥0∞`.) -/
def TotallyMinimax {S : Type u} {T : Type v} (π : S → T → Bool) : Prop :=
  ∀ (S' : Set S) (T' : Set T), S'.Nonempty → T'.Nonempty → MinimaxProperty (restrict π S' T')

/-- **The larger number game (LNG).** Holzman, arXiv:2310.19314v1, Example 1.3, p.3: each player
chooses a positive integer and the one who chose the larger number wins, ties broken in favor of
player 1: `G = (ℕ, ℕ, π)` with `π(s, t) = 1` if `s ≥ t` and `0` otherwise.

**Formalization Note.** The paper's positive integers `1, 2, 3, …` are indexed by Lean's
`ℕ = {0, 1, 2, …}` via `k ↦ k - 1`; the shift is an isomorphism of games (it preserves `s ≥ t`). -/
def lng : ℕ → ℕ → Bool := fun s t => decide (t ≤ s)

/-- **Isomorphism of games.** Two games `(S, T, π)` and `(S', T', π')` are isomorphic if there are
bijections `e₁ : S → S'`, `e₂ : T → T'` with `π'(e₁ s, e₂ t) = π(s, t)`; players keep their roles
(rows go to rows). Used in Holzman, arXiv:2310.19314v1, Definition 2.8, p.9.

**Formalization Note.** The paper uses "isomorphic" without a definition; this is the standard
notion for games in normal form (relabelling of pure strategies, players and payoffs fixed). -/
def GameIso {S : Type u} {T : Type v} {S' : Type u'} {T' : Type v'} (π : S → T → Bool)
    (π' : S' → T' → Bool) : Prop :=
  ∃ (e₁ : S ≃ S') (e₂ : T ≃ T'), ∀ s t, π' (e₁ s) (e₂ t) = π s t

/-- **LNG-free.** Holzman, arXiv:2310.19314v1, Definition 2.8, p.9: `G` is LNG-free if no subgame
of `G` is isomorphic to the larger number game (LNG). Equivalently (p.9), no submatrix of `M_G`
has, after reordering rows and columns, the full lower-triangular form of Example 1.3: there are
no `s₁, s₂, … ∈ S` and `t₁, t₂, … ∈ T` with `π(sᵢ, tⱼ) = 1 ⇔ i ≥ j`.

**Formalization Note.** Literal encoding: there are no subsets `S' ⊆ S`, `T' ⊆ T` such that the
restricted game is isomorphic (`GameIso`, players keeping their roles) to `lng`. Such `S'`, `T'`
are automatically countably infinite. The tie-breaking rule is the printed one (ties to player
1). -/
def LNGFree {S : Type u} {T : Type v} (π : S → T → Bool) : Prop :=
  ¬ ∃ (S' : Set S) (T' : Set T), GameIso (restrict π S' T') lng

end WinLoseMinimax


