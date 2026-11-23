-- Prove2me | Definitions.Def_LargeCongestion_Poisson_Supplement_Weighted
-- name    : LargeCongestion_Poisson_Supplement_Weighted
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T07:26:38.031953+00:00
-- url     : https://prove2.me/theorems/a6a0609c-e4fc-4167-a6e4-83529b8ecd2e
-- title:
--   §2.2 — weighted congestion games and independent mixed Nash profiles (4)–(7)
-- statement:
--   A weighted congestion game has finite resources $E$, finite player types $T$, nonempty feasible strategy families $S_t\subseteq 2^E$, and players $i\in\{0,\ldots,N-1\}$ with deterministic type $\tau_i$ and positive real mass $w_i$. Resource costs $C_e:[0,\infty)\to[0,\infty)$ are continuous and weakly increasing. The raw game data and the standing admissibility predicate are separate.
--
--   Independent mixed strategies $\sigma_i\in\Delta(S_{\tau_i})$ induce the product probability $\prod_i\sigma_i(a_i)$, weighted strategy flows and loads
--   $$Y_{t,s}=\sum_{i:\tau_i=t}w_i\mathbf1_{\{a_i=s\}},\qquad X_e=\sum_iw_i\mathbf1_{\{e\in a_i\}},\qquad X_{i,e}=w_i+\sum_{j\ne i}w_j\mathbf1_{\{e\in a_j\}}.$$
--   Mixed Nash equilibrium means that every used strategy minimizes the sum of expected conditional resource costs $\mathbb E[C_e(X_{i,e})]$. Demands and the mean flow-load pairs reuse the published finite sums, with mass in place of participation probability. Condition (12) asks that player counts diverge, maximum mass vanish, and each type demand converge. No mass is bounded by one.
--
--   These objects support the weighted limit and quantitative approximation theorems. Flow vectors contain only actual type-strategy coordinates; zero extension connects them to the published feasibility and Wardrop predicates.
--
--   **Formalization Note** The printed blackboard glyph in the weighted domains is read as $\mathbb R$, as required by vanishing positive weights in (12). Off-strategy probabilities are zero. Finite outcome sums are genuine expectations; an empty player set has maximum mass zero. All randomness is induced by the mixed profile.
-- source:
--   Cominetti, Scarsini, Schröder & Stier-Moses, Approximation and Convergence of Large Atomic Congestion Games, arXiv:2001.02797v7, pp. 9–13, (1)–(7), (12)

import Mathlib
import Definitions.Def_LargeCongestion_Poisson_Game

namespace LargeCongestion.Poisson.Supplement

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

variable {E T : Type*} [Fintype E] [DecidableEq E] [Fintype T] [DecidableEq T]

/-- The general weighted congestion-game data, §2.2, (4)–(7). Admissibility and regularity
are separate predicates, so this object does not impose strict cost growth or nonempty players. -/
structure WeightedGame (E T : Type*) (N : ℕ) where
  strategies : T → Finset (Finset E)
  cost : E → ℝ → ℝ
  playerType : Fin N → T
  mass : Fin N → ℝ

/-- The continuous, nonnegative, nondecreasing costs of §2, p. 9, on their real load domain.
The printed N glyphs on pp. 9–10 are read as R: (12) has positive weights tending to zero. -/
def ContinuousCosts (C : E → ℝ → ℝ) : Prop :=
  ∀ e, ContinuousOn (C e) (Set.Ici 0) ∧ MonotoneOn (C e) (Set.Ici 0) ∧
    ∀ x ∈ Set.Ici (0 : ℝ), 0 ≤ C e x

/-- A weighted game has nonempty strategy families, positive weights, and the standing costs. -/
def WeightedGame.Admissible {N : ℕ} (G : WeightedGame E T N) : Prop :=
  StrategiesNonempty G.strategies ∧ ContinuousCosts G.cost ∧ ∀ i, 0 < G.mass i

abbrev WOutcome (E : Type*) (N : ℕ) := Fin N → Finset E

/-- Product mixed-strategy probability, §2.2. Impossible strategies have zero mass. -/
def wProb {N : ℕ} (σ : Fin N → Finset E → ℝ) (a : WOutcome E N) : ℝ :=
  ∏ i, σ i (a i)

def wExpect {N : ℕ} (σ : Fin N → Finset E → ℝ) (f : WOutcome E N → ℝ) : ℝ :=
  ∑ a, wProb σ a * f a

/-- Weighted strategy flows (6). -/
def wFlow {N : ℕ} (τ : Fin N → T) (w : Fin N → ℝ)
    (a : WOutcome E N) (t : T) (s : Finset E) : ℝ :=
  ∑ i, if τ i = t ∧ a i = s then w i else 0

/-- Weighted resource loads (6). -/
def wLoad {N : ℕ} (w : Fin N → ℝ) (a : WOutcome E N) (e : E) : ℝ :=
  ∑ i, if e ∈ a i then w i else 0

/-- Own-player conditional resource load (7), with the player's full mass included. -/
def wConditionalLoad {N : ℕ} (w : Fin N → ℝ) (i : Fin N)
    (a : WOutcome E N) (e : E) : ℝ :=
  w i + ∑ j ∈ Finset.univ.erase i, if e ∈ a j then w j else 0

/-- Mixed Nash equilibrium, §2.2, p. 11. The expectations use the independent mixed profile. -/
def WeightedGame.IsMNE {N : ℕ} (G : WeightedGame E T N)
    (σ : Fin N → Finset E → ℝ) : Prop :=
  IsMixedProfile G.strategies G.playerType σ ∧
    ∀ i, ∀ s ∈ G.strategies (G.playerType i), ∀ s' ∈ G.strategies (G.playerType i),
      0 < σ i s →
      ∑ e ∈ s, wExpect σ (fun a => G.cost e (wConditionalLoad G.mass i a e)) ≤
      ∑ e ∈ s', wExpect σ (fun a => G.cost e (wConditionalLoad G.mass i a e))

/-- Weighted demand (4) is the same finite sum as expected Bernoulli demand, with masses
in place of participation probabilities. No upper bound of one is imposed on a mass. -/
def WeightedGame.demands {N : ℕ} (G : WeightedGame E T N) : T → ℝ :=
  demand G.playerType G.mass

/-- (12): player counts diverge, maximum weights vanish, and type demands converge.
The shared Condition14 is purely an algebraic limit predicate, not a probability predicate. -/
def Condition12 (N : ℕ → ℕ) (τ : ∀ n, Fin (N n) → T) (w : ∀ n, Fin (N n) → ℝ)
    (d : T → ℝ) : Prop := Condition14 N τ w d

/-- The finite-dimensional space of genuine flow coordinates and resource loads. -/
abbrev FlowLoad (S : T → Finset (Finset E)) := (FlowIdx S → ℝ) × (E → ℝ)

def wRandomPair {N : ℕ} (S : T → Finset (Finset E)) (τ : Fin N → T)
    (w : Fin N → ℝ) (a : WOutcome E N) : FlowLoad S :=
  (fun p => wFlow τ w a p.val.1 p.val.2, wLoad w a)

/-- The means in §2.2, p. 11, reuse the base sums (with weights, not Bernoulli trials). -/
def wMeanPair {N : ℕ} (S : T → Finset (Finset E)) (τ : Fin N → T)
    (w : Fin N → ℝ) (σ : Fin N → Finset E → ℝ) : FlowLoad S :=
  (fun p => expFlow τ w σ p.val.1 p.val.2, expLoad S τ w σ)

/-- Turn genuine flow coordinates into the base representation; unused coordinates are zero. -/
def extendFlow (S : T → Finset (Finset E)) (y : FlowIdx S → ℝ) (t : T) (s : Finset E) : ℝ :=
  if h : s ∈ S t then y ⟨(t, s), h⟩ else 0

end LargeCongestion.Poisson.Supplement


