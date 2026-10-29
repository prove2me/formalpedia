-- Prove2me | Definitions.Def_PutermanMDP_Multichain_Criteria
-- name    : PutermanMDP_Multichain_Criteria
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T02:59:48.124145+00:00
-- url     : https://prove2.me/theorems/df002148-41b9-4dbc-91a5-d641a4bb903b
-- title:
--   Finite multichain criteria, canonical bias, and nested optimality equations
-- statement:
--   Let $S$ be a finite state set and $A_s$ a nonempty finite set of available actions at state $s$. The stationary model has real rewards $r(s,a)$ and stochastic transition rows $p(j\mid s,a)$. An admissible deterministic rule $d$ defines the stationary history-dependent randomized policy $d^\infty$. All comparator policies are the published model's full history-dependent randomized policies.
--
--   Write $(P_a u)(s)=\sum_jp(j\mid s,a)u(j)$, let $R_n^d(s)$ be the expected reward at epoch $n$, and let $U_N^d(s)$ be the expected total reward over $N$ epochs. Define the discounted reward, gain, and canonical bias by
--   $$v_\lambda^d(s)=\sum_{n\ge0}\lambda^n R_n^d(s),\qquad g^d(s)=\liminf_{N\to\infty}\frac{U_N^d(s)}N,\qquad h^d(s)=\lim_{N\to\infty}\frac1N\sum_{k=1}^N\bigl(U_k^d(s)-k g^d(s)\bigr).$$
--   The last limit is the Cesàro representation of the bias, allowing periodic chains. In the finite stochastic model it exists and equals the fundamental-matrix bias.
--
--   The nested equations require $g(s)=\max_{a\in A_s}(P_a g)(s)$ and $g(s)+h(s)=\max_{a\in B_s}\{r(s,a)+(P_a h)(s)\}$, where $B_s=\{a\in A_s:(P_ag)(s)=g(s)\}$. The modified equations replace $B_s$ by $A_s$ in the second maximum. Every maximum includes attainment. The set $E$ consists of rules selecting from $B_s$ at each state; restricted and full selectors maximize the second expression over $E$ and all rules respectively.
--
--   The switch advantage is $w_\lambda(\delta,d)=r_\delta+\lambda P_\delta v_\lambda^d-v_\lambda^d$. Its Laurent residual subtracts $(P_\delta-I)g^d/(1-\lambda)+r_\delta-g^d+(P_\delta-I)h^d$. The improvement condition requires a strict lexicographic increase in $(P_\delta g^d,r_\delta+P_\delta h^d)$ at every changed state, but does not require any state to change. Strict near-one improvement means a positive extended-real lower limit of the difference of discounted values at at least one state.
--
--   These definitions separate policy values from Bellman equations and support the chapter's improvement results.
--
--   **Formalization Note** The published finite reward model is reused. Gain and bias are represented by real liminf; boundedness and convergence in finite chains prevent default values from replacing the intended quantities. Discounted series are used only for $0\le\lambda<1$ or on a left neighborhood of one, where they converge absolutely. The difference of discounted values is formed in the reals before embedding in the extended reals, so a divergent positive gain difference has lower limit $+\infty$.
-- source:
--   Puterman, Markov Decision Processes: Discrete Stochastic Dynamic Programming, Wiley, 1994, https://doi.org/10.1002/9780470316887, pp. 337–338 (PDF 353–354), §8.2.1; pp. 443–444 (PDF 459–460), §9.1.1; p. 456 (PDF 472), (9.2.10)–(9.2.14)

import Mathlib
import Definitions.Def_MarkovDecisionProcesses_AverageReward

open MarkovDecisionProcesses Filter
open scoped Topology

namespace PutermanMDP.Multichain

variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq A]

/-- Admissible deterministic stationary decision rules, §9.1.1. -/
def Rule (M : StationaryMDP S A) := {d : S → A // ∀ s, d s ∈ M.admissible s}

/-- The stationary rule as a history-dependent randomized policy. -/
noncomputable def policy (M : StationaryMDP S A) (d : Rule M) : AvgHRPolicy M :=
  stationaryPolicy M d.val d.property

/-- One transition applied to a vector. -/
noncomputable def act (M : StationaryMDP S A) (u : S → ℝ) (s : S) (a : A) : ℝ :=
  ∑ j, M.trans s a j * u j

/-- Expected reward at epoch n, with the first epoch indexed zero. -/
noncomputable def rewardAt (M : StationaryMDP S A) (d : Rule M) : ℕ → S → ℝ
  | 0 => fun s => M.reward s (d.val s)
  | n + 1 => fun s => act M (rewardAt M d n) s (d.val s)

/-- Expected discounted reward; the series is absolutely convergent for 0 ≤ lam < 1. -/
noncomputable def discounted (M : StationaryMDP S A) (d : Rule M) (lam : ℝ) (s : S) : ℝ :=
  ∑' n : ℕ, lam ^ n * rewardAt M d n s

/-- Stationary gain, equal to the ordinary average-reward limit in a finite chain. -/
noncomputable def gain (M : StationaryMDP S A) (d : Rule M) (s : S) : ℝ :=
  gainInf (policy M d) s

/-- Canonical bias: the Cesàro limit of total reward minus N times the gain,
§8.2.1, p. 338, (8.2.2)–(8.2.4). This limit exists also for periodic finite chains. -/
noncomputable def bias (M : StationaryMDP S A) (d : Rule M) (s : S) : ℝ :=
  Filter.liminf (fun N : ℕ =>
    (∑ k ∈ Finset.range N,
      (totalReward (policy M d) (k + 1) 0 [] s - (k + 1 : ℕ) * gain M d s)) / N)
    Filter.atTop

/-- First optimality equation, with attainment at each state. -/
def GainEquation (M : StationaryMDP S A) (g : S → ℝ) : Prop :=
  ∀ s, (∀ a ∈ M.admissible s, act M g s a ≤ g s) ∧
    ∃ a ∈ M.admissible s, act M g s a = g s

/-- Nested multichain equations (9.1.5)–(9.1.6). -/
def OptimalityEquations (M : StationaryMDP S A) (g h : S → ℝ) : Prop :=
  GainEquation M g ∧ ∀ s,
    (∀ a ∈ M.admissible s, act M g s a = g s →
      M.reward s a + act M h s a ≤ g s + h s) ∧
    ∃ a ∈ M.admissible s, act M g s a = g s ∧
      M.reward s a + act M h s a = g s + h s

/-- Modified equations (9.1.5) and (9.1.8), with both maxima attained. -/
def ModifiedEquations (M : StationaryMDP S A) (g h : S → ℝ) : Prop :=
  GainEquation M g ∧ ∀ s,
    (∀ a ∈ M.admissible s, M.reward s a + act M h s a ≤ g s + h s) ∧
    ∃ a ∈ M.admissible s, M.reward s a + act M h s a = g s + h s

/-- Membership in the restricted rule set E. -/
def InE (M : StationaryMDP S A) (g : S → ℝ) (d : Rule M) : Prop :=
  ∀ s, act M g s (d.val s) = g s

/-- Attainment of the componentwise bias maximum over E. -/
def RestrictedSelector (M : StationaryMDP S A) (g h : S → ℝ) (d : Rule M) : Prop :=
  InE M g d ∧ ∀ e : Rule M, InE M g e → ∀ s,
    M.reward s (e.val s) + act M h s (e.val s) ≤
      M.reward s (d.val s) + act M h s (d.val s)

/-- Attainment of the componentwise bias maximum over all rules D. -/
def FullSelector (M : StationaryMDP S A) (h : S → ℝ) (d : Rule M) : Prop :=
  ∀ s, ∀ a ∈ M.admissible s,
    M.reward s a + act M h s a ≤ M.reward s (d.val s) + act M h s (d.val s)

/-- One-step switch advantage (9.2.10), with subsequent use of d. -/
noncomputable def advantage (M : StationaryMDP S A) (δ d : Rule M) (lam : ℝ) (s : S) : ℝ :=
  M.reward s (δ.val s) + lam * act M (discounted M d lam) s (δ.val s) - discounted M d lam s

/-- Laurent residual in (9.2.11). -/
noncomputable def residual (M : StationaryMDP S A) (δ d : Rule M) (lam : ℝ) (s : S) : ℝ :=
  advantage M δ d lam s -
    ((act M (gain M d) s (δ.val s) - gain M d s) / (1 - lam) +
      (M.reward s (δ.val s) - gain M d s + act M (bias M d) s (δ.val s) - bias M d s))

/-- The changed-state implication exactly as printed in Proposition 9.2.2.
It deliberately does not assert δ ≠ d. -/
def ImprovementCondition (M : StationaryMDP S A) (δ d : Rule M) : Prop :=
  ∀ s, δ.val s ≠ d.val s →
    act M (gain M d) s (d.val s) < act M (gain M d) s (δ.val s) ∨
    (act M (gain M d) s (δ.val s) = act M (gain M d) s (d.val s) ∧
      M.reward s (d.val s) + act M (bias M d) s (d.val s) <
        M.reward s (δ.val s) + act M (bias M d) s (δ.val s))

/-- Extended-real liminf is essential: gain improvement can make it +∞. -/
def StrictNearOneImprovement (M : StationaryMDP S A) (δ d : Rule M) : Prop :=
  ∃ s, (0 : EReal) < Filter.liminf
    (fun lam : ℝ => ((discounted M δ lam s - discounted M d lam s : ℝ) : EReal))
    (nhdsWithin (1 : ℝ) (Set.Iio 1))

end PutermanMDP.Multichain


