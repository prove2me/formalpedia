-- Prove2me | Definitions.Def_StatComplexityDM_LinearLB_Setting
-- name    : StatComplexityDM_LinearLB_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T21:21:36.423665+00:00
-- url     : https://prove2.me/theorems/e50a2919-9bfa-4a40-9981-23f19090ec1e
-- title:
--   §6.1.1 and (12), pp. 12, 41, 100 — linear bandits on the unit ball with Rademacher outcomes: Rad(μ), f^θ(π) = ⟨θ, π⟩, the regret g^θ, D²_H and the localized class M^∞_ε(M̄)
-- statement:
--   This file fixes the linear bandit setting of Proposition 6.2 on the Euclidean unit ball.
--
--   1. The **unit ball** $\mathbb{B}^d = \{v \in \mathbb{R}^d : \|v\|_2 \le 1\}$ serves both as the decision space $\Pi$ and as the parameter set $\Theta$. It carries the subspace topology and the Borel $\sigma$-algebra of $\mathbb{R}^d$. The point $0 \in \Theta$ is singled out as the parameter of a reference model.
--   2. For $\mu \in [-1, 1]$, the **Rademacher distribution** $\mathrm{Rad}(\mu)$ on the outcomes $\{-1, +1\}$ puts mass $(1+\mu)/2$ on $+1$ and $(1-\mu)/2$ on $-1$, so its mean is $\mu$.
--   3. The **linear model** with parameter $\theta \in \Theta$ has mean reward $f^\theta(\pi) = \langle \theta, \pi \rangle$ and outcome law $M_\theta(\pi) = \mathrm{Rad}(\langle \theta, \pi \rangle)$; this is a probability law because $|\langle \theta, \pi\rangle| \le 1$ on the ball.
--   4. A map $\theta \mapsto \pi_\theta$ is a **maximizer selector** if $\langle \theta, \pi \rangle \le \langle \theta, \pi_\theta \rangle$ for all $\theta, \pi$ in the ball, and the **instantaneous regret** is
--   $$
--   g^\theta(\pi) = f^\theta(\pi_\theta) - f^\theta(\pi).
--   $$
--   5. The squared Hellinger distance between the outcome laws of two models at a decision is $D^2_{\mathrm{H}}(M_\theta(\pi), M_{\bar\theta}(\pi))$, with $D^2_{\mathrm{H}}(P,Q) = \sum_y (\sqrt{P(y)} - \sqrt{Q(y)})^2$, as in (5).
--   6. The **$L_\infty$-localized class** around the reference parameter $\bar\theta$ at radius $\varepsilon$ is (12):
--   $$
--   \mathcal{M}^\infty_\varepsilon(\overline{M}) = \bigl\{ \theta \in \Theta : |g^\theta(\pi) - g^{\bar\theta}(\pi)| \le \varepsilon \ \ \forall \pi \in \Pi \bigr\}.
--   $$
--
--   These are the objects in which Proposition 6.2 and its proof are stated: the reference model $\overline{M} = \mathrm{Rad}(0)$ and the hard family $M_i(\pi) = \mathrm{Rad}(\langle \Delta e_i, \pi\rangle)$.
--
--   **Formalization Note** The paper's model class $\mathcal{M}_{\mathcal{F}}$ contains every reward law on $[-1,1]$ with mean $\langle\theta,\pi\rangle$. This file keeps only the models with $\pm 1$ outcomes, which are exactly the Rademacher laws, so a model is identified with its parameter $\theta$. Lower bounds proved for this subclass imply the paper's, because the localized class of the subclass is contained in the paper's. Outcomes are encoded on `Bool` (`true` for $+1$). The selector is a parameter with a hypothesis, so statements hold for whichever maximizer the paper meant; for $\theta = 0$ every decision is a maximizer and $g^0 \equiv 0$.
-- source:
--   arXiv:2112.13487v3, (12) (p. 12), §6.1 and §6.1.1 (p. 41), proof of Proposition 6.2 (p. 100), Lemma A.8 (p. 71)

import Mathlib
import Definitions.Def_FoundationsRL_GeneralDM_Divergences

namespace StatComplexityDM.LinearLB

open FoundationsRL.GeneralDM

/-- The closed Euclidean unit ball `{v ∈ ℝ^d | ‖v‖₂ ≤ 1}` of `ℝ^d`, which is both the decision
space `Π` and the parameter set `Θ` of Proposition 6.2 (arXiv:2112.13487v3, p. 41). It carries the
subspace topology and the Borel σ-algebra of `ℝ^d` restricted to the ball. -/
abbrev Ball (d : ℕ) : Type := {v : EuclideanSpace ℝ (Fin d) // ‖v‖ ≤ 1}

/-- The origin `0 ∈ Θ`, the parameter of the reference model `M̄(π) = Rad(⟨0, π⟩) = Rad(0)`
(proof of Proposition 6.2, p. 100). -/
def ballZero (d : ℕ) : Ball d := ⟨0, by simp⟩

/-- The Rademacher distribution `Rad(μ)` with mean `μ` on the outcomes `{−1, +1}`, encoded on
`Bool` (`true` ↔ `+1`, `false` ↔ `−1`): `Rad(μ)(+1) = (1 + μ)/2`, `Rad(μ)(−1) = (1 − μ)/2`. It is a
probability vector exactly when `μ ∈ [−1, 1]` (Lemma A.8, p. 71; §6.1.1, p. 41). -/
noncomputable def rad (μ : ℝ) : Bool → ℝ :=
  fun y => if y then (1 + μ) / 2 else (1 - μ) / 2

/-- The mean reward of the linear model with parameter `θ` at the decision `π`,
`f^θ(π) = ⟨θ, π⟩` (§6.1.1, p. 41: `F = {π ↦ ⟨θ, π⟩ | θ ∈ Θ}`). -/
noncomputable def linMean {d : ℕ} (θ π : Ball d) : ℝ :=
  inner ℝ (θ : EuclideanSpace ℝ (Fin d)) (π : EuclideanSpace ℝ (Fin d))

/-- The linear bandit model with parameter `θ` and `±1` outcomes, `M_θ(π) = Rad(⟨θ, π⟩)`
(proof of Proposition 6.2, p. 100); its mean reward is `⟨θ, π⟩`. -/
noncomputable def linModel {d : ℕ} (θ π : Ball d) : Bool → ℝ :=
  rad (linMean θ π)

/-- `piStar` selects, for every parameter `θ`, a maximizer `π_θ ∈ arg max_{π ∈ Π} ⟨θ, π⟩` of the
mean reward over the ball (`π_M`, p. 5). -/
def IsBallArgmax {d : ℕ} (piStar : Ball d → Ball d) : Prop :=
  ∀ θ π : Ball d, linMean θ π ≤ linMean θ (piStar θ)

/-- The instantaneous regret `g^θ(π) := f^θ(π_θ) − f^θ(π)` of the decision `π` under the model with
parameter `θ` ((12), p. 12). -/
noncomputable def gapLin {d : ℕ} (piStar : Ball d → Ball d) (θ π : Ball d) : ℝ :=
  linMean θ (piStar θ) - linMean θ π

/-- The squared Hellinger distance `D²_H(M_θ(π), M_θ̄(π))` between the outcome laws of the models
with parameters `θ` and `θ̄` at the decision `π` ((5), p. 10, no factor ½). -/
noncomputable def hellLin {d : ℕ} (θ θbar π : Ball d) : ℝ :=
  hellingerSq (linModel θ π) (linModel θbar π)

/-- The L∞-localized class (12), p. 12, of the linear model class `M = {M_θ : θ ∈ Θ}`:
`M^∞_ε(M̄) = {M ∈ M : |g^M(π) − g^{M̄}(π)| ≤ ε ∀ π ∈ Π}`, indexed by parameters. -/
def linLocalized {d : ℕ} (piStar : Ball d → Ball d) (θbar : Ball d) (ε : ℝ) : Set (Ball d) :=
  {θ | ∀ π : Ball d, |gapLin piStar θ π - gapLin piStar θbar π| ≤ ε}

end StatComplexityDM.LinearLB


