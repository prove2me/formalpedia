-- Prove2me | Definitions.Def_RobustPoA_Static_Distribution
-- name    : RobustPoA_Static_Distribution
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T02:41:06.672988+00:00
-- url     : https://prove2.me/theorems/68dc1805-211f-4985-aad7-042924ba9f03
-- title:
--   §3.1, §4.1, pp. 12, 15 — distributions over outcomes, expectation, coarse correlated equilibria (15) and ε-coarse correlated equilibria
-- statement:
--   Let $G$ be a cost-minimization game with players $i$, strategy sets $S_i$ and player costs $C_i$. A **probability distribution** $\sigma$ over outcomes is here a finitely supported assignment of weights $\sigma(s) \ge 0$ to outcomes $s$ with $\sum_s \sigma(s) = 1$; the expectation of a function $f$ of the outcome is
--
--   $$\mathbf{E}_{s\sim\sigma}[f(s)] = \sum_{s} \sigma(s)\, f(s).$$
--
--   A **coarse correlated equilibrium** of $G$ is a probability distribution $\sigma$ over outcomes such that
--
--   $$\mathbf{E}_{s\sim\sigma}[C_i(s)] \le \mathbf{E}_{s\sim\sigma}[C_i(s_i', s_{-i})] \quad \text{for every player } i \text{ and every } s_i' \in S_i. \tag{15}$$
--
--   For $\epsilon \in \mathbb{R}$, an **$\epsilon$-coarse correlated equilibrium** is a probability distribution $\sigma$ over outcomes such that
--
--   $$\mathbf{E}_{s\sim\sigma}[C_i(s)] \le (1+\epsilon)\, \mathbf{E}_{s\sim\sigma}[C_i(s_i', s_{-i})] \quad \text{for every player } i \text{ and every } s_i' \in S_i.$$
--
--   Coarse correlated equilibria (the Hannan set) contain the pure Nash, mixed Nash and correlated equilibria, and are the limit points of no-regret play; they are the most permissive equilibrium concept to which the smoothness bounds extend.
--
--   **Formalization Note** Distributions are finitely supported (`Finsupp`), so expectations are finite sums and need no integrability conditions; this covers every finite game and all mixed Nash and correlated equilibria of finite games, but not distributions with infinite support. The weights are required to be nonnegative and to sum to $1$, so the zero weight function is not a distribution. The paper defines $\epsilon$-coarse correlated equilibria only by saying (p. 15) that the approximate versions of the equilibrium concepts of §3.1 "can be defined in the same way" as the $\epsilon$-Nash condition (26); the definition above is that extension of (15), the cost-minimization analogue of the condition written out in Remark 4.4 (p. 16).
-- source:
--   Roughgarden, Intrinsic Robustness of the Price of Anarchy, J. ACM 62(5) (2015), §3.1 (15), p. 12; §4.1, p. 15; Remark 4.4, p. 16

import Mathlib
import Definitions.Def_RobustPoA_Static_Game

namespace RobustPoA.Static

/-- A finitely supported probability distribution over outcomes: nonnegative weights of total
mass `1`. -/
def IsDist {ι : Type*} {S : ι → Type*} (σ : (∀ i, S i) →₀ ℝ) : Prop :=
  (∀ s, 0 ≤ σ s) ∧ (σ.sum fun _ w => w) = 1

/-- The expectation `E_{s∼σ}[f(s)] = ∑ₛ σ(s) f(s)` under a finitely supported weight `σ`. -/
noncomputable def expect {ι : Type*} {S : ι → Type*} (σ : (∀ i, S i) →₀ ℝ)
    (f : (∀ i, S i) → ℝ) : ℝ :=
  σ.sum fun s w => w * f s

/-- §3.1, (15), p. 12: a coarse correlated equilibrium is a probability distribution `σ` over
outcomes with `E_{s∼σ}[Cᵢ(s)] ≤ E_{s∼σ}[Cᵢ(s'ᵢ, s₋ᵢ)]` for every player `i` and `s'ᵢ ∈ Sᵢ`. -/
def IsCCE {ι : Type*} [DecidableEq ι] {S : ι → Type*}
    (C : ι → (∀ i, S i) → ℝ) (σ : (∀ i, S i) →₀ ℝ) : Prop :=
  IsDist σ ∧ ∀ (i : ι) (t : S i),
    expect σ (C i) ≤ expect σ (fun s => C i (Function.update s i t))

/-- §4.1, p. 15 ("defined in the same way" as (26)): an `ε`-coarse correlated equilibrium is a
probability distribution `σ` with `E_{s∼σ}[Cᵢ(s)] ≤ (1 + ε) E_{s∼σ}[Cᵢ(s'ᵢ, s₋ᵢ)]`. -/
def IsEpsCCE {ι : Type*} [DecidableEq ι] {S : ι → Type*}
    (C : ι → (∀ i, S i) → ℝ) (ε : ℝ) (σ : (∀ i, S i) →₀ ℝ) : Prop :=
  IsDist σ ∧ ∀ (i : ι) (t : S i),
    expect σ (C i) ≤ (1 + ε) * expect σ (fun s => C i (Function.update s i t))

end RobustPoA.Static


