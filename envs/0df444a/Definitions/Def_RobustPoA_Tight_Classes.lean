-- Prove2me | Definitions.Def_RobustPoA_Tight_Classes
-- name    : RobustPoA_Tight_Classes
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T00:49:14.524984+00:00
-- url     : https://prove2.me/theorems/e0a44c40-3900-45ca-8a45-8e1ce0406e1e
-- title:
--   Example 2.5, Definition 2.8, (34)–(36), (41), pp. 6, 10, 23–25 — congestion-game classes and smoothness bounds
-- statement:
--   A finite congestion game has a finite set of players, a finite set of resources, a nonempty set of resource subsets available to each player, and a cost function for each resource. For a profile $A$, the load $x_e(A)$ is the number of players using resource $e$. A player pays the sum of $c_e(x_e(A))$ over resources it uses, and $C(A)$ is the sum of player costs. The game model is imported from the published congestion-game definition.
--
--   A cost function $c:\mathbb N\to\mathbb R$ is admissible here when it is nonnegative and nondecreasing at positive loads and is nonzero at some positive load; $c(0)$ is unrestricted. Strict positivity means $c(x)>0$ for every $x\ge1$. For a set $\mathcal C$ of such functions, $\mathcal G(\mathcal C)$ contains all finite congestion games whose resource functions lie in $\mathcal C$, with any numbers of players and resources and at least one strategy for each player.
--
--   The resourcewise parameters $\mathcal A(\mathcal C)$ are the pairs $(\lambda,\mu)$ with $\mu<1$ such that, for every $c\in\mathcal C$, current load $x\ge0$, and reference load $x^*\ge1$,
--
--   $$c(x+1)x^*\le\lambda c(x^*)x^*+\mu c(x)x.$$
--
--   The value $\gamma(\mathcal C)$ is the infimum of $\lambda/(1-\mu)$ over these pairs. The bounded-load versions $\mathcal A(\mathcal C,n)$ and $\gamma(\mathcal C,n)$ restrict $x$ to $0,\ldots,n$ and $x^*$ to $1,\ldots,n$. A game is $(\lambda,\mu)$-smooth when the sum of costs of unilateral deviations from a feasible profile $A$ toward another feasible profile $A^*$ is at most $\lambda C(A^*)+\mu C(A)$. The class parameters $\mathcal A(\mathcal G(\mathcal C))$ make every game in the class smooth.
--
--   The pure price of anarchy of a game is the supremum of $C(A)/\min_{A^*}C(A^*)$ over its pure Nash equilibria. The worst-case price of anarchy takes the supremum over every finite game in $\mathcal G(\mathcal C)$. These definitions supply the common model for the main theorem and its supporting results.
--
--   **Formalization Note** Values of prices of anarchy and $\gamma$ lie in $[0,\infty]$, so an empty parameter set has infimum $+\infty$, and a positive equilibrium cost divided by a zero optimum is $+\infty$. Zero-load resource costs are never evaluated in a player cost or affect the resourcewise inequality. Games without pure Nash equilibria contribute $0$ to the supremum; every congestion game with nonempty strategy sets has an equilibrium.
-- source:
--   Roughgarden, Intrinsic Robustness of the Price of Anarchy, J. ACM 62(5) (2015), Example 2.5, p. 6; Definition 2.8, p. 10; equations (34)–(36), p. 23; equation (41), p. 25

import Mathlib
import Definitions.Def_CongestionPoA_AsymSum_Model

namespace RobustPoA.Tight

open scoped ENNReal
open CongestionPoA.AsymSum

/-- Example 2.5 and §5.1, pp. 6 and 23: a nonnegative, nondecreasing resource cost function
which is not identically zero on positive loads. The value at load zero is irrelevant. -/
def IsCostFn (c : ℕ → ℝ) : Prop :=
  (∀ x, 1 ≤ x → 0 ≤ c x) ∧
  (∀ x y, 1 ≤ x → x ≤ y → c x ≤ c y) ∧
  ∃ x, 1 ≤ x ∧ c x ≠ 0

/-- §5.1, p. 23: strict positivity on positive loads. -/
def IsStrictlyPos (c : ℕ → ℝ) : Prop := ∀ x, 1 ≤ x → 0 < c x

/-- (35), p. 23: the pairs `(λ, μ)` satisfying the resourcewise smoothness inequalities.
The reference load `x'` is positive; the current load `x` may be zero. -/
def smoothParams (C : Set (ℕ → ℝ)) : Set (ℝ × ℝ) :=
  {p | p.2 < 1 ∧ ∀ c ∈ C, ∀ x x' : ℕ, 1 ≤ x' →
    c (x + 1) * (x' : ℝ) ≤
      p.1 * (c x' * (x' : ℝ)) + p.2 * (c x * (x : ℝ))}

/-- (36), p. 23: the best ratio from (35), with `⊤` when there is no admissible pair. -/
noncomputable def gamma (C : Set (ℕ → ℝ)) : ℝ≥0∞ :=
  ⨅ p ∈ smoothParams C, ENNReal.ofReal (p.1 / (1 - p.2))

/-- §5.2, p. 25: (35) restricted to current loads `0,…,n` and reference loads `1,…,n`. -/
def smoothParamsN (C : Set (ℕ → ℝ)) (n : ℕ) : Set (ℝ × ℝ) :=
  {p | p.2 < 1 ∧ ∀ c ∈ C, ∀ x x' : ℕ, x ≤ n → 1 ≤ x' → x' ≤ n →
    c (x + 1) * (x' : ℝ) ≤
      p.1 * (c x' * (x' : ℝ)) + p.2 * (c x * (x : ℝ))}

/-- (41), p. 25: the best bounded-load smoothness ratio. -/
noncomputable def gammaN (C : Set (ℕ → ℝ)) (n : ℕ) : ℝ≥0∞ :=
  ⨅ p ∈ smoothParamsN C n, ENNReal.ofReal (p.1 / (1 - p.2))

/-- §5, p. 23: membership in the class of finite congestion games whose resource costs lie
in `C`. Every player has at least one strategy. -/
def InClass (C : Set (ℕ → ℝ)) {k m : ℕ}
    (G : CongestionGame (Fin k) (Fin m)) : Prop :=
  (∀ e, G.latency e ∈ C) ∧ ∀ i, (G.strategies i).Nonempty

/-- Definition 2.1, p. 4, specialized to the congestion-game model of Example 2.5. Both
outcomes must be feasible strategy profiles. -/
def IsSmoothCG {ι E : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype E] [DecidableEq E] (G : CongestionGame ι E) (lam mu : ℝ) : Prop :=
  ∀ A A' : ι → Finset E, IsProfile G A → IsProfile G A' →
    (∑ i, cost G (Function.update A i (A' i)) i) ≤
      lam * sumCost G A' + mu * sumCost G A

/-- (34), p. 23: parameters that make every game in the class smooth. The numbers of
players and resources range over all natural numbers. -/
def classParams (C : Set (ℕ → ℝ)) : Set (ℝ × ℝ) :=
  {p | p.2 < 1 ∧ ∀ (k m : ℕ) (G : CongestionGame (Fin k) (Fin m)),
    InClass C G → IsSmoothCG G p.1 p.2}

/-- Definition 2.8, p. 10: the least social cost among feasible profiles of a finite game. -/
noncomputable def optCost {ι E : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype E] [DecidableEq E] (G : CongestionGame ι E) : ℝ≥0∞ :=
  ⨅ A : ι → Finset E, ⨅ _ : IsProfile G A, ENNReal.ofReal (sumCost G A)

/-- Definition 2.8, p. 10: pure price of anarchy. If the optimum is zero and some pure
Nash equilibrium has positive cost, its ratio is `⊤`. -/
noncomputable def purePoA {ι E : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype E] [DecidableEq E] (G : CongestionGame ι E) : ℝ≥0∞ :=
  ⨆ A : ι → Finset E, ⨆ _ : IsPureNash G A,
    ENNReal.ofReal (sumCost G A) / optCost G

/-- (34), p. 23: worst pure price of anarchy over every finite congestion game in `C`. -/
noncomputable def worstPoA (C : Set (ℕ → ℝ)) : ℝ≥0∞ :=
  ⨆ k : ℕ, ⨆ m : ℕ, ⨆ G : CongestionGame (Fin k) (Fin m),
    ⨆ _ : InClass C G, purePoA G

/-- Proposition 5.2, p. 24: the robust price of anarchy of one congestion game, using all
smooth parameter pairs for that game. -/
noncomputable def robustPoACG {ι E : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype E] [DecidableEq E] (G : CongestionGame ι E) : ℝ≥0∞ :=
  ⨅ p ∈ {p : ℝ × ℝ | p.2 < 1 ∧ IsSmoothCG G p.1 p.2},
    ENNReal.ofReal (p.1 / (1 - p.2))

end RobustPoA.Tight


