-- Prove2me | Definitions.Def_EvolvHier_SocialOpt_Setting
-- name    : EvolvHier_SocialOpt_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-19T01:21:42.171051+00:00
-- url     : https://prove2.me/theorems/02da178c-696c-414f-8581-f7f1453614e4
-- title:
--   Technology, schemes, payoffs, and social value of an evolving hierarchy
-- statement:
--   Agents are indexed by $\mathbb N_0$, with agent 0 initially present. A technology $p$ assigns the probability of recruiting the next agent after nonnegative investment $x_i$. A scheme $t$ allocates each arriving agent's unit revenue among that agent and predecessors. It has $0\leq t_{ij}\leq1$, $t_{ij}=0$ for $i<j$, and $\sum_{j\leq i}t_{ij}=1$.
--
--   With $w_i(x)=\prod_{k<i}p(x_k)$, expected length and investment are
--
--   $$L(x)=\sum_{i\geq0}w_i(x),\qquad I(x)=\sum_{i\geq0}w_i(x)x_i.$$
--
--   The file also defines conditional payoff $E_i(t,x)$ from equation (1), gross return $E_i^*(t,x)$, social value $V(x)$, Nash equilibrium, decentralized social optimality, the full-transfer scheme $t^*$, $L_{\max}(X)$, and variation among agents reached with positive probability. These objects supply the shared model for the goal and milestones.
--
--   **Formalization Note** Nonnegative series use extended nonnegative reals and payoffs use extended reals. When $I(x)=\infty$, $V(x)$ is negative infinity; otherwise it is $L(x)-I(x)$. Differentiability of $p$ is required on $(0,\infty)$ with right continuity at zero. All technology assumptions of §2 are retained.
-- source:
--   Hougaard, Moreno-Ternero & Østerdal, Optimal Management of Evolving Hierarchies, UPO WP ECON 21.15 (Aug. 3, 2021; Manag. Sci. doi:10.1287/mnsc.2021.4185), §2, pp. 7–10; proof of Theorem 2, pp. 20–25

import Mathlib
import Definitions.Def_EvolvHier_SocialOpt_Game
open scoped BigOperators

namespace EvolvHier.SocialOpt

/-- The paper's recruitment technology on nonnegative investments. -/
structure Technology where
  p : ℝ → ℝ
  zero : p 0 = 0
  nonneg : ∀ x, 0 ≤ x → 0 ≤ p x
  lt_one : ∀ x, 0 ≤ x → p x < 1
  strictMono : StrictMonoOn p (Set.Ici 0)
  strictConcave : StrictConcaveOn ℝ (Set.Ici 0) p
  differentiable : ∀ x, 0 < x → DifferentiableAt ℝ p x
  continuous_zero : ContinuousWithinAt p (Set.Ici 0) 0
  deriv_zero : Filter.Tendsto (deriv p) (nhdsWithin 0 (Set.Ioi 0)) Filter.atTop
  convex_ratio : ConvexOn ℝ (Set.Ioi 0) (fun x => p x / deriv p x)

/-- Revenue from agent `i` is split among that agent and her predecessors. -/
def IsScheme (t : ℕ → ℕ → ℝ) : Prop :=
  (∀ i j, 0 ≤ t i j ∧ t i j ≤ 1) ∧
  (∀ i j, i < j → t i j = 0) ∧
  (∀ i, ∑ j ∈ Finset.range (i + 1), t i j = 1)

abbrev IsProfile (x : ℕ → ℝ) : Prop := IsNonnegativeProfile x

/-- Probability that agent `i` is realized, conditional on the initial agent. -/
def w (T : Technology) (x : ℕ → ℝ) (i : ℕ) : ℝ :=
  ∏ k ∈ Finset.range i, T.p (x k)

/-- Expected total number of realized agents. -/
noncomputable def L (T : Technology) (x : ℕ → ℝ) : ENNReal :=
  ∑' i, ENNReal.ofReal (w T x i)

/-- Expected total investment of realized agents. -/
noncomputable def I (T : Technology) (x : ℕ → ℝ) : ENNReal :=
  ∑' i, ENNReal.ofReal (w T x i * x i)

/-- Social value, with infinite expected investment assigned value negative infinity. -/
noncomputable def V (T : Technology) (x : ℕ → ℝ) : EReal :=
  if I T x = ⊤ then ⊥ else (((L T x).toReal - (I T x).toReal : ℝ) : EReal)

/-- Gross expected receipts by agent `i` from all later arrivals. -/
noncomputable def gross (T : Technology) (t : ℕ → ℕ → ℝ)
    (x : ℕ → ℝ) (i : ℕ) : ENNReal :=
  ∑' l, ENNReal.ofReal
    ((∏ k ∈ Finset.range (l + 1), T.p (x (i + k))) * t (i + l + 1) i)

/-- Equation (1): expected payoff conditional on agent `i` being realized. -/
noncomputable def payoff (T : Technology) (t : ℕ → ℕ → ℝ)
    (x : ℕ → ℝ) (i : ℕ) : EReal :=
  ((t i i - x i : ℝ) : EReal) + ((gross T t x i : ENNReal) : EReal)

/-- Expected gross return conditional on the next agent being realized. -/
noncomputable def Estar (T : Technology) (t : ℕ → ℕ → ℝ)
    (x : ℕ → ℝ) (i : ℕ) : ENNReal :=
  ∑' l, ENNReal.ofReal
    ((∏ k ∈ Finset.range l, T.p (x (i + 1 + k))) * t (i + 1 + l) i)

/-- The game induced by a transfer scheme and a recruitment technology. -/
noncomputable def inducedGame (T : Technology) (t : ℕ → ℕ → ℝ) :
    NonnegativeActionGame ℕ := ⟨payoff T t⟩

/-- A pure Nash equilibrium for the induced game. -/
def IsEquilibrium (T : Technology) (t : ℕ → ℕ → ℝ) (x : ℕ → ℝ) : Prop :=
  (inducedGame T t).IsNashEquilibrium x

/-- A scheme supporting an equilibrium at least as valuable as every equilibrium
of every other valid allocation scheme. -/
def IsDecSociallyOptimal (T : Technology) (t : ℕ → ℕ → ℝ) : Prop :=
  IsScheme t ∧ ∃ x, IsEquilibrium T t x ∧
    ∀ t' x', IsScheme t' → IsEquilibrium T t' x' → V T x' ≤ V T x

/-- The full transfer from each successor to its immediate predecessor. -/
def tStar : ℕ → ℕ → ℝ :=
  fun i j => if i = j + 1 ∨ (i = 0 ∧ j = 0) then 1 else 0

/-- Highest expected length attainable with exact expected investment `X`. -/
noncomputable def Lmax (T : Technology) (X : ℝ) : ENNReal :=
  ⨆ (x : ℕ → ℝ) (_ : IsProfile x ∧ I T x = ENNReal.ofReal X), L T x

/-- Variation among agents with positive probability of being realized. -/
def NonConstOnSupport (T : Technology) (x : ℕ → ℝ) : Prop :=
  ∃ i j, 0 < w T x i ∧ 0 < w T x j ∧ x i ≠ x j

end EvolvHier.SocialOpt


