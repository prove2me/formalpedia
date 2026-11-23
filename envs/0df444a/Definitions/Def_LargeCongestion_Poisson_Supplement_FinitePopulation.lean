-- Prove2me | Definitions.Def_LargeCongestion_Poisson_Supplement_FinitePopulation
-- name    : LargeCongestion_Poisson_Supplement_FinitePopulation
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T07:27:38.159114+00:00
-- url     : https://prove2.me/theorems/2030b965-11bf-42c9-985e-cd452c3fe03c
-- title:
--   §5.3 — finite Bernoulli games with arbitrary actions and count-vector costs
-- statement:
--   A finite population game has players $i\in\{0,\ldots,N-1\}$, types $\tau_i\in T$, independent participation indicators of probabilities $u_i\in(0,1]$, and arbitrary finite action spaces $A_t$. Players of the same type may use different mixed strategies. The independent participation/action product determines the random count vector $Y$ and the other-player count vector $Y^{-i}$, obtained by omitting player $i$.
--
--   The mean count and Nash condition are
--   $$y_{t,a}=\sum_{i:\tau_i=t}u_i\sigma_i(a),\qquad \sigma_i(a)>0\ \Longrightarrow\ \mathbb E[C(Y^{-i};\tau_i,a)]\le\mathbb E[C(Y^{-i};\tau_i,b)]\quad(b\in A_{\tau_i}).$$
--   The cost is a function of the entire vector, with no congestion or separability assumption. Bounded costs means that one finite bound controls $|C(n;t,a)|$ over all counts and type-action pairs; finiteness of the action index makes this equivalent to the source's individual bounds. Expectations are finite sums under the induced product law.
--
--   These definitions give the finite games in Theorem 4 without imposing the type symmetry of the limiting Poisson game.
-- source:
--   Cominetti, Scarsini, Schröder & Stier-Moses, Approximation and Convergence of Large Atomic Congestion Games, arXiv:2001.02797v7, pp. 23–24, Nash condition preceding Theorem 4

import Mathlib
import Definitions.Def_LargeCongestion_Poisson_Supplement_Population

namespace LargeCongestion.Poisson.Supplement

variable {T : Type*} [Fintype T] [DecidableEq T]
variable {A : T → Type*} [∀ t, Fintype (A t)] [∀ t, DecidableEq (A t)]

/-- The finite Bernoulli game of §5.3, p. 23, with unrestricted count-vector costs. -/
structure FinitePopulationGame (T : Type*) (A : T → Type*) (N : ℕ) where
  playerType : Fin N → T
  participation : Fin N → ℝ
  cost : (Sigma A → ℕ) → Sigma A → ℝ

/-- Finite profiles may be asymmetric within a type. -/
def IsFiniteProfile {N : ℕ} (τ : Fin N → T) (σ : ∀ i, A (τ i) → ℝ) : Prop :=
  (∀ i a, 0 ≤ σ i a) ∧ ∀ i, ∑ a, σ i a = 1

abbrev BOutcome {N : ℕ} (τ : Fin N → T) (A : T → Type*) :=
  ∀ i : Fin N, Bool × A (τ i)

/-- Independent participation and independent individual actions. -/
def bProb {N : ℕ} (τ : Fin N → T) (u : Fin N → ℝ)
    (σ : ∀ i, A (τ i) → ℝ) (ω : BOutcome τ A) : ℝ :=
  ∏ i, (if (ω i).1 then u i else 1 - u i) * σ i (ω i).2

def bExpect {N : ℕ} (τ : Fin N → T) (u : Fin N → ℝ)
    (σ : ∀ i, A (τ i) → ℝ) (f : BOutcome τ A → ℝ) : ℝ :=
  ∑ ω, bProb τ u σ ω * f ω

/-- Counts of all players, respectively of all players except the specified one. -/
def bCounts {N : ℕ} (τ : Fin N → T) (ω : BOutcome τ A) (p : Sigma A) : ℕ :=
  ∑ i, if (ω i).1 = true ∧ Sigma.mk (τ i) (ω i).2 = p then 1 else 0

def bOthers {N : ℕ} (τ : Fin N → T) (i : Fin N) (ω : BOutcome τ A) (p : Sigma A) : ℕ :=
  ∑ j ∈ Finset.univ.erase i,
    if (ω j).1 = true ∧ Sigma.mk (τ j) (ω j).2 = p then 1 else 0

/-- Expected counts are induced by the individual profile, not free variables. -/
def bMean {N : ℕ} (τ : Fin N → T) (u : Fin N → ℝ)
    (σ : ∀ i, A (τ i) → ℝ) (p : Sigma A) : ℝ :=
  ∑ i, ∑ a : A (τ i), if Sigma.mk (τ i) a = p then u i * σ i a else 0

/-- The Nash condition immediately preceding Theorem 4. -/
def FinitePopulationGame.IsNash {N : ℕ} (G : FinitePopulationGame T A N)
    (σ : ∀ i, A (G.playerType i) → ℝ) : Prop :=
  IsFiniteProfile G.playerType σ ∧
    ∀ i (a b : A (G.playerType i)), 0 < σ i a →
      bExpect G.playerType G.participation σ
        (fun ω => G.cost (bOthers G.playerType i ω) ⟨G.playerType i, a⟩) ≤
      bExpect G.playerType G.participation σ
        (fun ω => G.cost (bOthers G.playerType i ω) ⟨G.playerType i, b⟩)

/-- Myerson's bounded-cost assumption, over every count vector; costs may be signed. -/
def BoundedPopulationCosts (C : (Sigma A → ℕ) → Sigma A → ℝ) : Prop :=
  ∃ B : ℝ, ∀ n p, |C n p| ≤ B

end LargeCongestion.Poisson.Supplement


