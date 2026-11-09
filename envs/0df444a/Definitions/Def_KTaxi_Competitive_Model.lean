-- Prove2me | Definitions.Def_KTaxi_Competitive_Model
-- name    : KTaxi_Competitive_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:25:24.913231+00:00
-- url     : https://prove2.me/theorems/39f555ca-feda-4357-8fa0-4b51d6aa5613
-- title:
--   The online $k$-taxi game (hard cost) against adaptive online adversaries, and competitiveness
-- statement:
--   Let $(V,d)$ be a metric space and $k\in\mathbb N$. There are $k$ taxis, labelled $1,\dots,k$; a **configuration** assigns a location in $V$ to each label (taxis may share a location). A **request** is an ordered pair $(r,s)\in V\times V$: some taxi must drive to the pickup $r$ and then carry a passenger to the drop-off $s$. In the **hard** version of the problem only the drive to $r$ is charged; the ride from $r$ to $s$ is free.
--
--   1. **Randomized online algorithm.** An algorithm $A$ has a set of internal states, an initial state, and a step rule: given its current state, its current configuration $x$ and the request $(r,s)$, it outputs a probability distribution (with countable support) on pairs (next state, label $a$ of the serving taxi). It sees neither the adversary's configuration nor future requests.
--
--   2. **Adaptive online adversary.** A deterministic rule that, from the history of the algorithm's past outcomes (states and serving taxis), either stops or issues the next request $(r,s)$ together with its own reaction: it moves its taxis from its configuration $y$ to any configuration $z$ and serves with its taxi $i$. It fixes all of this before the algorithm's random choice in that round, and it must serve immediately.
--
--   3. **One round.** The adversary pays $\sum_j d(y_j,z_j)+d(z_i,r)$; the algorithm draws $(\sigma',a)$ from its step rule and pays $d(x_a,r)$; then both serving taxis are relocated to $s$ for free, and $(\sigma',a)$ is appended to the history.
--
--   4. **Expected costs.** For a horizon $T$ (the adversary may stop earlier), $\mathbb E[\mathrm{ALG}]$ and $\mathbb E[\mathrm{ADV}]$ are the expected total costs of the two players over at most $T$ rounds, from initial configurations $x_0$ (algorithm) and $y_0$ (adversary), computed on the game tree of the algorithm's random choices; they take values in $[0,\infty]$.
--
--   5. **Competitiveness.** $A$ is **$\rho$-competitive against adaptive online adversaries** if for all initial configurations $x_0,y_0$ there is a finite constant $\beta\ge0$, independent of the adversary and of the horizon, such that
--   $$
--   \mathbb E[\mathrm{ALG}]\le\rho\,\mathbb E[\mathrm{ADV}]+\beta\qquad\text{for every adaptive online adversary and every horizon }T .
--   $$
--
--   These are the objects of Theorem 1.1 and of Lemmas 4.2, 4.7 and 4.8.
--
--   **Formalization Note** `OnlineAlg V k` has a field `State : Type`, `init`, and `step : State → (Fin k → V) → V → V → PMF (State × Fin k)`. `Adversary V k S` is `move : List (S × Fin k) → Option (V × V × (Fin k → V) × Fin k)`. `gameCost` is defined by recursion on the number of remaining rounds and returns both expected costs in `ℝ≥0∞`, with `∑'` against the algorithm's `PMF`; distances are `edist`. `IsCompetitive A ρ` takes `ρ : ℝ≥0` and quantifies `∀ x₀ y₀, ∃ β : ℝ≥0, ∀ adv T`.
-- source:
--   Christian Coester, Yichen Huang, Tze-Yang Poon, The k-Taxi Problem Is Competitive on All Metrics, STOC 2027 submission #96 (October 2026; PDF SHA-256 09242267e431f586117500ee75c63e6f203519f497d01ee4d90d6989341648ed), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/96.pdf, §1 (PDF p. 2, the hard version) and §2 Preliminaries (PDF p. 4, requests, adaptive online adversaries, competitive ratio); round order as in §4.1 (PDF p. 7)

import Mathlib

open scoped ENNReal NNReal

namespace KTaxi.Competitive

/-! # The online k-taxi game (hard version) against adaptive online adversaries

Coester, Huang, Poon, *The k-Taxi Problem Is Competitive on All Metrics*, STOC 2027 submission
#96, §1 (PDF p. 2) and §2 (PDF p. 4).

`k` taxis live in a metric space `V`. A request is an ordered pair `(r, s) ∈ V × V`; it is served
by moving one taxi to `r` (paying the distance) and then relocating it to `s` for free (the
"hard" cost of the paper). Configurations are labelled: `Fin k → V`, label ↦ location; taxis may
coincide.
-/

/-- A **randomized online algorithm** for k-taxi on `V`: an internal state type, an initial
state, and a step rule. On request `(r, s)`, given its current state and its current labelled
configuration, it returns a probability distribution on pairs (next state, label of the serving
taxi). It does not see the adversary's configuration nor future requests. -/
structure OnlineAlg (V : Type*) (k : ℕ) where
  /-- internal memory of the algorithm -/
  State : Type
  /-- initial memory -/
  init : State
  /-- randomized step: (state, own configuration, pickup `r`, drop-off `s`) ↦ law of
  (next state, serving taxi) -/
  step : State → (Fin k → V) → V → V → PMF (State × Fin k)

/-- A (deterministic) **adaptive online adversary** against an algorithm with state type `S`.
From the history of the algorithm's past outcomes (state, serving taxi), oldest first, it either
stops (`none`) or issues the next request `(r, s)` together with its own reaction: it moves its
taxis to a configuration `z` (any movement it likes) and serves the request with its taxi `i`
(which drives from `z i` to `r` and then to `s`). The decision is made before the algorithm's
random choice of the current round. -/
structure Adversary (V : Type*) (k : ℕ) (S : Type) where
  /-- history ↦ stop, or (pickup `r`, drop-off `s`, repositioned configuration `z`, serving taxi) -/
  move : List (S × Fin k) → Option (V × V × (Fin k → V) × Fin k)

variable {V : Type*} [MetricSpace V] {k : ℕ}

/-- The game tree with at most `T` further rounds, starting from algorithm state `σ`,
algorithm configuration `x`, adversary configuration `y` and history `h`. Returns the pair
(expected total cost of the algorithm, expected total cost of the adversary), both in `ℝ≥0∞`.

In a round with adversary move `(r, s, z, i)`: the adversary pays `∑ⱼ d(y j, z j) + d(z i, r)`;
the algorithm draws `(σ', a)` from `A.step σ x r s` and pays `d(x a, r)`; then both serving taxis
are relocated to `s` (free) and the outcome `(σ', a)` is appended to the history. -/
noncomputable def gameCost (A : OnlineAlg V k) (adv : Adversary V k A.State) :
    ℕ → A.State → (Fin k → V) → (Fin k → V) → List (A.State × Fin k) → ℝ≥0∞ × ℝ≥0∞
  | 0, _, _, _, _ => (0, 0)
  | T + 1, σ, x, y, h =>
    match adv.move h with
    | none => (0, 0)
    | some (r, s, z, i) =>
      ( ∑' o : A.State × Fin k, A.step σ x r s o *
          (edist (x o.2) r +
            (gameCost A adv T o.1 (Function.update x o.2 s) (Function.update z i s) (h ++ [o])).1),
        (∑ j, edist (y j) (z j)) + edist (z i) r +
          ∑' o : A.State × Fin k, A.step σ x r s o *
            (gameCost A adv T o.1 (Function.update x o.2 s) (Function.update z i s) (h ++ [o])).2 )

/-- `E[ALG]` over at most `T` rounds, both players starting from labelled configurations
`x₀` (algorithm) and `y₀` (adversary), the algorithm in its initial state, empty history. -/
noncomputable def algCost (A : OnlineAlg V k) (adv : Adversary V k A.State) (T : ℕ)
    (x₀ y₀ : Fin k → V) : ℝ≥0∞ :=
  (gameCost A adv T A.init x₀ y₀ []).1

/-- `E[ADV]` over at most `T` rounds, from the same starting data as `algCost`. -/
noncomputable def advCost (A : OnlineAlg V k) (adv : Adversary V k A.State) (T : ℕ)
    (x₀ y₀ : Fin k → V) : ℝ≥0∞ :=
  (gameCost A adv T A.init x₀ y₀ []).2

/-- `A` is **`ρ`-competitive against adaptive online adversaries** (§2, PDF p. 4): for all
initial configurations `x₀` (algorithm) and `y₀` (adversary) there is a finite constant `β ≥ 0`,
independent of the adversary and of the number of rounds, such that
`E[ALG] ≤ ρ · E[ADV] + β` for every adaptive online adversary and every horizon `T`. -/
def IsCompetitive (A : OnlineAlg V k) (ρ : ℝ≥0) : Prop :=
  ∀ x₀ y₀ : Fin k → V, ∃ β : ℝ≥0, ∀ (adv : Adversary V k A.State) (T : ℕ),
    algCost A adv T x₀ y₀ ≤ (ρ : ℝ≥0∞) * advCost A adv T x₀ y₀ + (β : ℝ≥0∞)

end KTaxi.Competitive


