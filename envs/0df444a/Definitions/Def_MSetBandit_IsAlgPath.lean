-- Prove2me | Definitions.Def_MSetBandit_IsAlgPath
-- name    : MSetBandit_IsAlgPath
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:43:33.284363+00:00
-- url     : https://prove2.me/theorems/6fd6e6de-f4e7-4d31-8499-fc1ed1130078
-- title:
--   A sample path of Algorithm 1
-- statement:
--   Fix $T\ge1$ and $\delta\in(0,1)$, and let $\eta$ be the learning rate of Algorithm 1. Sequences of loss vectors $\ell_t\in\mathbb R^d$, parameters $\theta_t\in\mathbb R^d$ and actions $X_t\in\mathcal X$ form a **sample path of Algorithm 1** if
--   1. $\theta_1=\mathbf 0$, so $p_1=U$ (line 3);
--   2. the losses satisfy the action-level normalization $|x^\top\ell_t|\le1$ for every $x\in\mathcal X$ and every round $t\le T$;
--   3. at every round $t\le T$, with $Y_t=X_t^\top\ell_t$, $\hat\ell_t=M_t^{-1}X_tY_t$, $z_t=\hat\ell_t-\eta c_t$ and $\tilde\theta_{t+1}=\theta_t-\eta z_t$ (lines 8–10), the next parameter $\theta_{t+1}$ is an admissible output of line 11 on input $(\tilde\theta_{t+1},\eta,T)$.
--
--   The random draw $X_t\sim p_t$ is not a pathwise condition; it enters through the probabilistic run.
--
--   **Formalization Note** Rounds are indexed from $0$: the paper's $\theta_1,\ell_1,X_1$ are the values at index $0$ and its $\theta_{T+1}$ is the value at index $T$. Values beyond the horizon are unconstrained.
-- source:
--   Bacchiocchi–Cesari–Colomboni, An Efficient Minimax-Optimal Algorithm for Adversarial m-Set Bandits, arXiv:2608.12231, Algorithm 1, p.12; Section 2, p.4

import Mathlib
import Definitions.Def_MSetBandit_etaAlg
import Definitions.Def_MSetBandit_mwuParam
import Definitions.Def_MSetBandit_IsProjOutput
open Matrix

namespace MSetBandit

/-- **A sample path of Algorithm 1.** Bacchiocchi–Cesari–Colomboni, *An Efficient Minimax-Optimal Algorithm for Adversarial m-Set Bandits*, arXiv:2608.12231, Algorithm 1, p.12, with the loss normalization of
Section 2, p.4.

`IsAlgPath d m T δ ℓ θ X` says, for the losses `ℓ t`, parameters `θ t` and drawn actions `X t`
(rounds `t = 0, …, T − 1`), with `η = etaAlg d m T δ`:
1. `θ 0 = 0` (line 3: `θ₁ ← 0`, `p₁ = U`);
2. the action-level normalization `|x^⊤ ℓ_t| ≤ 1` for every action `x` and every round `t < T`;
3. for every round `t < T`, with `Y_t = X_t^⊤ ℓ_t` (line 8) and `θ̃_{t+1} = θ_t − η z_t`
   (lines 9–10), the next parameter `θ_{t+1}` is an output of line 11 on input
   `(θ̃_{t+1}, η, T)` (`IsProjOutput`).

**Formalization Note.** Rounds are 0-based: the paper's `θ₁, X₁, ℓ₁` are `θ 0, X 0, ℓ 0` and its
`θ_{T+1}` is `θ T`. The draw `X_t ∼ p_t` (line 7) is not a pathwise condition; it is the
conditional-law clause of `IsAlgRun`. Values of `ℓ, θ, X` at rounds beyond the horizon are
unconstrained. -/
def IsAlgPath (d m T : ℕ) (δ : ℝ) (ℓ θ : ℕ → Fin d → ℝ) (X : ℕ → Action d m) : Prop :=
  θ 0 = 0 ∧
  (∀ t < T, ∀ x : Action d m, |ind x ⬝ᵥ ℓ t| ≤ 1) ∧
  ∀ t < T, IsProjOutput m (etaAlg d m T δ) T
    (mwuParam (etaAlg d m T δ) (θ t) (X t) (ind (X t) ⬝ᵥ ℓ t)) (θ (t + 1))

end MSetBandit


