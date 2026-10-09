-- Prove2me | Definitions.Def_StatComplexityDM_MAB_Bernoulli
-- name    : StatComplexityDM_MAB_Bernoulli
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T21:21:47.355974+00:00
-- url     : https://prove2.me/theorems/8fce9274-e3f3-4058-8276-743753754756
-- title:
--   §5.1, p. 28, p. 32 and §6.1.5, p. 43 — Bernoulli bandits, the hard family M_i(π) = Ber(1/2 + Δ·I{π = i}), and bandits with gap Δ
-- statement:
--   The multi-armed bandit with $A$ arms has decision space $\Pi = [A]$. This file fixes its Bernoulli instances.
--
--   1. $\mathrm{Ber}(q)$ is the distribution on $\{0, 1\}$ (encoded as $\{\texttt{false}, \texttt{true}\}$) with $\mathrm{Ber}(q)(1) = q$ and $\mathrm{Ber}(q)(0) = 1 - q$; the reward of outcome $y$ is $y$ itself, so the mean reward of $\mathrm{Ber}(q)$ is $q$.
--   2. The **Bernoulli bandits** with $A$ arms are all models $M$ with $M(\pi)$ a probability distribution on $\{0,1\}$ for every arm $\pi$.
--   3. For $\Delta \in \mathbb{R}$, the **hard family** of the proof of Proposition 5.3 is $M_i(\pi) = \mathrm{Ber}\bigl(\tfrac12 + \Delta\, \mathbb{I}\{\pi = i\}\bigr)$, $i \in [A]$.
--   4. For $\Delta > 0$, a Bernoulli bandit $M$ has **gap exactly $\Delta$** if there is an arm $\pi_0$ with
--   $$
--   f^M(\pi) + \Delta \le f^M(\pi_0) \quad \text{for all } \pi \neq \pi_0,
--   $$
--   with equality for at least one $\pi \ne \pi_0$. Then $\pi_0$ is the unique optimal arm $\pi_M$ and this says $\Delta_M := \min_{\pi \ne \pi_M} \{ f^M(\pi_M) - f^M(\pi) \} = \Delta$ (§6.1.5, p. 43). The **gap-$\Delta$ bandits** are the Bernoulli bandits with gap exactly $\Delta$.
--
--   **Formalization Note** The paper's model class for the multi-armed bandit is all reward distributions on $\mathcal{R} = [0,1]$ (with trivial observations). The Bernoulli bandits are a subclass; since the DEC is monotone in the class and the localized class only shrinks when intersected with a subclass, every DEC lower bound stated over the Bernoulli subclass implies the paper's bound over the full class. The hard family is a probability model only when $\tfrac12 + \Delta \in [0,1]$; the theorems that use it assume $\Delta \in (0, \tfrac12)$.
-- source:
--   arXiv:2112.13487v3, §5.1 (p. 28), proof of Proposition 5.3 (p. 32), §6.1.5 (p. 43)

import Mathlib
import Definitions.Def_FoundationsRL_GeneralDM_Protocol
import Definitions.Def_StatComplexityDM_LowerBound_Core

namespace StatComplexityDM.MAB

open FoundationsRL.GeneralDM

/-- The Bernoulli distribution `Ber(q)` on the outcome alphabet `Bool` (`true` = reward 1,
`false` = reward 0): `Ber(q)(true) = q`, `Ber(q)(false) = 1 − q` (arXiv:2112.13487v3, §5.1, p. 32;
App. A.2, p. 71). It is a probability vector exactly when `0 ≤ q ≤ 1`. -/
def ber (q : ℝ) : Bool → ℝ := fun y => if y then q else 1 - q

/-- The reward read off a Bernoulli outcome: `1` for `true`, `0` for `false`
(rewards `R = {0, 1} ⊆ [0, 1]`, observations `O = {∅}`, §5.1, p. 28). -/
def berRew : Bool → ℝ := fun y => if y then 1 else 0

/-- The class of all Bernoulli multi-armed bandits with `A` arms: models `M : [A] → Δ({0, 1})`,
the subclass of the paper's `M = {M : M(π) ∈ Δ(R)}`, `R = [0, 1]` (§5.1, p. 28) whose reward
distributions are supported on `{0, 1}`. -/
def bernoulliBandits (A : ℕ) : Set (Fin A → Bool → ℝ) := {m | StatComplexityDM.LowerBound.IsModel m}

/-- The hard family of the proof of Proposition 5.3 (p. 32): for arm `i`,
`M_i(π) = Ber(1/2 + Δ · I{π = i})`. -/
noncomputable def berFamily (A : ℕ) (Δ : ℝ) : Fin A → Fin A → Bool → ℝ :=
  fun i π => ber (1 / 2 + Δ * if π = i then 1 else 0)

/-- A Bernoulli bandit `m` has gap exactly `Δ` (§6.1.5, p. 43: `Δ_M := min_{π ≠ π_M}
{f^M(π_M) − f^M(π)}`): some arm `π₀` beats every other arm by at least `Δ`, and some other arm
is exactly `Δ` below it. For `Δ > 0`, `π₀` is the unique maximizer `π_M` and the minimum equals `Δ`. -/
def HasGap {A : ℕ} (m : Fin A → Bool → ℝ) (Δ : ℝ) : Prop :=
  0 < Δ ∧ ∃ π₀, (∀ π, π ≠ π₀ → fM berRew m π + Δ ≤ fM berRew m π₀) ∧
    ∃ π, π ≠ π₀ ∧ fM berRew m π + Δ = fM berRew m π₀

/-- The class of Bernoulli multi-armed bandits over `[A]` with gap exactly `Δ` (§6.1.5, p. 43,
Proposition 6.7), within the Bernoulli subclass of `R = [0, 1]` bandits. -/
def gapBandits (A : ℕ) (Δ : ℝ) : Set (Fin A → Bool → ℝ) := {m | StatComplexityDM.LowerBound.IsModel m ∧ HasGap m Δ}

end StatComplexityDM.MAB


