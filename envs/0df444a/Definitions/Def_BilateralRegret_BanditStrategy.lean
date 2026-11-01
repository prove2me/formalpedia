-- Prove2me | Definitions.Def_BilateralRegret_BanditStrategy
-- name    : BilateralRegret_BanditStrategy
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:12:26.639987+00:00
-- url     : https://prove2.me/theorems/4bfbe6cf-61fc-491d-b3cf-600cf031e771
-- title:
--   $K$-armed bandit strategies, the i.i.d. bandit scenario with rewards in $[0,1]^K$, and the bandit regret $R^\nu_\tau(\alpha)$
-- statement:
--   This module casts the $K$-armed bandit problem in the paper's sequential-game framework (Definitions 1–4): actions $[K]$, reward vectors $y\in\mathbb R^K$, reward $\rho(k,y)=y_k$ and bandit feedback $\varphi(k,y)=y_k$.
--
--   1. A **strategy** $\alpha=(\alpha_t)_{t\ge1}$ is a sequence of measurable maps $\alpha_t:\mathbb R^t\times\mathbb R^{t-1}\to[K]$. In round $t$ it plays $X_t=\alpha_t(V_1,\dots,V_t,Z_1,\dots,Z_{t-1})$, where $V_1,V_2,\dots$ are its uniform draws and $Z_s=Y_s(X_s)$ is the reward observed in round $s$.
--   2. An **admissible reward law** is a probability measure $\nu$ on $\mathbb R^K$ with $\nu([0,1]^K)=1$; the coordinates (arms) may be arbitrarily correlated.
--   3. The **scenario** over $\tau$ rounds: $Y_1,\dots,Y_\tau$ i.i.d. with law $\nu$, and $V_1,\dots,V_\tau$ i.i.d. uniform on $[0,1]$, independent of the rewards.
--   4. The **regret** of $\alpha$ after $\tau$ rounds is
--
--   $$
--   R^\nu_\tau(\alpha)=\max_{k\in[K]}\mathbb E\Big[\sum_{t=1}^\tau Y_t(k)-\sum_{t=1}^\tau Y_t(X_t)\Big].
--   $$
--
--   A distribution-free bound $\mathcal R_\tau(\alpha)$ in Theorem 3 is any number that bounds $R^\nu_\tau(\alpha)$ for every admissible $\nu$.
--
--   **Formalization Note** Arms are `Fin K`; round $t$ of $\alpha$ is index $t-1$. Each $\alpha_t$ accepts any real uniforms and rewards (the feedback space is $\mathbb R$; the uniforms lie in $[0,1]$ almost surely). The maximum over arms is a real supremum over `Fin K`.
-- source:
--   Cesa-Bianchi, Cesari, Colomboni, Fusco, Leonardi, Bilateral Trade: A Regret Minimization Perspective, arXiv:2109.12974v1, Definitions 1–4, pp.22–23 (footnote 3: measurability); App. C.2.3, p.24 (Stochastic (iid)); Theorem 3, p.12 ("distribution-free upper bound on the regret after τ rounds of α in the stochastic i.i.d. setting with [0,1]-valued rewards")

import Mathlib
import Definitions.Def_BilateralRegret_GFT

namespace BilateralRegret

open MeasureTheory

/-- **A player's strategy in the `K`-armed bandit game** (Definition 3, p.23, for the game with
action space `[K]`, reward vectors `y ∈ ℝ^K`, reward `ρ(k, y) = y_k` and bandit feedback
`φ(k, y) = y_k`).

`act t` is the paper's `α_{t+1} : [0,1]^{t+1} × 𝒵^{t} → [K]`: in round `t + 1` it maps the uniform
draws `V_1, …, V_{t+1}` and the observed rewards `Z_1, …, Z_t` to the arm played. Each `act t` is
measurable (Definition 1, footnote 3, p.23).

**Formalization Note.** Arms are `Fin K`; the uniforms and the feedback are real numbers, so a
strategy accepts any real reward (the feedback space is taken to be `ℝ`). -/
structure BanditStrategy (K : ℕ) where
  /-- The arm `α_{t+1}(V_1, …, V_{t+1}, Z_1, …, Z_t)` played in round `t + 1`. -/
  act : (t : ℕ) → (Fin (t + 1) → ℝ) × (Fin t → ℝ) → Fin K
  /-- Every `α_t` is measurable. -/
  measurable_act : ∀ t, Measurable (act t)

namespace BanditStrategy

variable {K : ℕ}

/-- The feedback history `(Z_1, …, Z_n)` of strategy `α` when it is run on the uniform draws
`v` and the reward vectors `y` (round `s + 1` stored at index `s`): `Z_{s} = y_s(X_s)`. Defined
inductively, as the actions in Definition 3, p.23. -/
noncomputable def feedbackHist (α : BanditStrategy K) (v : ℕ → ℝ) (y : ℕ → Fin K → ℝ) :
    (n : ℕ) → Fin n → ℝ
  | 0 => Fin.elim0
  | n + 1 => Fin.snoc (α := fun _ => ℝ) (feedbackHist α v y n)
      (y n (α.act n (fun i => v i, feedbackHist α v y n)))

/-- The arm `X_{t+1} = α_{t+1}(V_1, …, V_{t+1}, Z_1, …, Z_t)` played in round `t + 1`
(Definition 3, p.23). -/
noncomputable def action (α : BanditStrategy K) (v : ℕ → ℝ) (y : ℕ → Fin K → ℝ) (t : ℕ) : Fin K :=
  α.act t (fun i => v i, feedbackHist α v y t)

end BanditStrategy

/-- **An admissible reward law** of the `K`-armed bandit game in the stochastic i.i.d. setting
with `[0,1]`-valued rewards: a probability measure `ν` on reward vectors `ℝ^K` that is
concentrated on `[0,1]^K` (App. C.2.3, p.24, "Stochastic (iid)", for the bandit game). The arms
may be arbitrarily correlated. -/
def IsRewardLaw {K : ℕ} (ν : Measure (Fin K → ℝ)) : Prop :=
  IsProbabilityMeasure ν ∧ ν {y | ∀ k, y k ∈ Set.Icc (0 : ℝ) 1} = 1

/-- The scenario of the bandit game over `τ` rounds (Definition 2, p.23, truncated): the
reward vectors `Y_1, …, Y_τ` are i.i.d. with law `ν`, and the player's randomization
`V_1, …, V_τ` is i.i.d. uniform on `[0,1]` and independent of them. -/
noncomputable def banditScenario {K : ℕ} (ν : Measure (Fin K → ℝ)) (τ : ℕ) :
    Measure ((Fin τ → Fin K → ℝ) × (Fin τ → ℝ)) :=
  (Measure.pi fun _ : Fin τ => ν).prod (Measure.pi fun _ : Fin τ => unif)

/-- **The regret of a bandit strategy** after `τ` rounds in the i.i.d. scenario with reward law
`ν` (Definition 4, p.23):
`R^ν_τ(α) = max_{k ∈ [K]} 𝔼[ Σ_{t=1}^τ Y_t(k) − Σ_{t=1}^τ Y_t(X_t) ]`.

**Formalization Note.** The maximum over the finite set `Fin K` is a real `⨆` (for `K = 0` it is
`0`; every statement of the mission has `K ≥ 1`). -/
noncomputable def banditRegret {K : ℕ} (α : BanditStrategy K) (ν : Measure (Fin K → ℝ))
    (τ : ℕ) : ℝ :=
  ⨆ k : Fin K, ∫ ω, (∑ t : Fin τ, ω.1 t k
      - ∑ t : Fin τ, ω.1 t (α.action (extendSeq ω.2) (extendSeq ω.1) t)) ∂(banditScenario ν τ)

end BilateralRegret


