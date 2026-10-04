-- Prove2me | Definitions.Def_RegretBandits_Contextual_Banditron
-- name    : RegretBandits_Contextual_Banditron
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T10:10:35.728846+00:00
-- url     : https://prove2.me/theorems/5d2d52ec-eee0-4bce-a469-e1a73126672d
-- title:
--   The Banditron (Section 4.4, p. 58)
-- statement:
--   The **Banditron** of Bubeck and Cesa-Bianchi (Section 4.4) is a bandit version of the multiclass Perceptron: after predicting it observes only whether its prediction was correct. With parameter $\gamma \in (0, 1/2]$ it starts from the zero $K\times d$ matrix $W_1$ and at each round $t = 1, \dots, n$:
--
--   1. observes $x_t \in \mathbb R^d$ and sets $\hat y_t = \arg\max_{i} (W_t x_t)_i$;
--   2. predicts $Y_t$ drawn from $p_{i,t} = (1-\gamma)\mathbb 1_{\hat y_t = i} + \gamma/K$;
--   3. observes $\mathbb 1_{Y_t = y_t}$;
--   4. updates $W_{t+1} = W_t + \widetilde X_t$ with
--   $$(\widetilde X_t)_{i,j} = x_{t,j}\left(\frac{\mathbb 1_{Y_t = y_t}\mathbb 1_{Y_t = i}}{p_{i,t}} - \mathbb 1_{\hat y_t = i}\right).$$
--
--   Its number of prediction mistakes is $M_n = \sum_{t=1}^n \mathbb 1_{Y_t \ne y_t}$.
--
--   **Formalization Note** Rounds are numbered from $0$ and the weight matrix is a function of the earlier predictions. The argmax is taken through an argmax selector (any tie-breaking rule). The prediction law is the path law of `Protocol` applied to `banditronRule`.
-- source:
--   Bubeck, Cesa-Bianchi, Regret Analysis of Stochastic and Nonstochastic Multi-armed Bandit Problems, arXiv:1204.5721v2, p. 58, Section 4.4 (Banditron box)

import Mathlib
import Definitions.Def_RegretBandits_Contextual_Protocol
import Definitions.Def_RegretBandits_Contextual_Multiclass

namespace RegretBandits.Contextual

/-- Sampling distribution of the Banditron (p. 58, step (3)) given the current weight matrix `W`
and instance `x`: `p_i = (1-γ) 1{ŷ = i} + γ/K` with `ŷ = sel (W x)`. -/
noncomputable def banditronDist {K d : ℕ} (γ : ℝ) (sel : (Fin K → ℝ) → Fin K)
    (W : Matrix (Fin K) (Fin d) ℝ) (x : Fin d → ℝ) (i : Fin K) : ℝ :=
  (1 - γ) * (if sel (Matrix.mulVec W x) = i then 1 else 0) + γ / K

/-- Weight matrices of the Banditron (Bubeck–Cesa-Bianchi, arXiv:1204.5721v2, p. 58) with
parameter `γ`, argmax selector `sel`, on the examples `(x_t, y_t)` (rounds 0-based), as a function
of the predictions `h : Fin t → Fin K` of rounds `0, …, t-1`: `W_0 = 0` and
`W_{t+1} = W_t + X̃_t` with
`(X̃_t)_{i,j} = x_{t,j} (1{Y_t = y_t} 1{Y_t = i} / p_{i,t} - 1{ŷ_t = i})`,
`ŷ_t = sel (W_t x_t)` and `p_t = banditronDist γ sel W_t x_t`. -/
noncomputable def banditronW {K d : ℕ} (γ : ℝ) (sel : (Fin K → ℝ) → Fin K)
    (x : ℕ → Fin d → ℝ) (y : ℕ → Fin K) :
    (t : ℕ) → (Fin t → Fin K) → Matrix (Fin K) (Fin d) ℝ
  | 0, _ => 0
  | t + 1, h =>
      let W := banditronW γ sel x y t (Fin.init h)
      let Y := h (Fin.last t)
      W + Matrix.of (fun i j => x t j *
        ((if Y = y t ∧ Y = i then 1 / banditronDist γ sel W (x t) i else 0) -
          (if sel (Matrix.mulVec W (x t)) = i then 1 else 0)))

/-- The Banditron as a sampling rule: the prediction `Y_t` is drawn from
`p_t = banditronDist γ sel W_t x_t`. -/
noncomputable def banditronRule {K d : ℕ} (γ : ℝ) (sel : (Fin K → ℝ) → Fin K)
    (x : ℕ → Fin d → ℝ) (y : ℕ → Fin K) : PlayRule K :=
  fun t h i => banditronDist γ sel (banditronW γ sel x y t h) (x t) i

/-- Number of prediction mistakes of a prediction sequence `ω` in the first `n` rounds:
`M_n = ∑_{t<n} 1{Y_t ≠ y_t}`. -/
def predictionMistakes {K n : ℕ} (y : ℕ → Fin K) (ω : Fin n → Fin K) : ℝ :=
  ∑ t : Fin n, if ω t ≠ y t then 1 else 0

end RegretBandits.Contextual


