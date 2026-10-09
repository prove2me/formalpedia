-- Prove2me | Definitions.Def_ModernOnlineLearning_Classification_Perceptron
-- name    : ModernOnlineLearning_Classification_Perceptron
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T05:31:45.784182+00:00
-- url     : https://prove2.me/theorems/834d5f74-80ed-4c0c-bede-17fa86198503
-- title:
--   Algorithm 8.2, p. 143 — Perceptron iterates and mistake count
-- statement:
--   In online binary classification, let $z_t\in\mathbb R^d$ be the feature vector and $y_t\in\{-1,1\}$ its label. The **Perceptron** starts at $x_1=0$, predicts $\widetilde y_t=\operatorname{sign}(\langle z_t,x_t\rangle)$ with $\operatorname{sign}(0)=0$, and sets
--
--   $$
--   x_{t+1}=x_t+\mathbf 1\{y_t\widetilde y_t\le0\}\,y_tz_t.
--   $$
--
--   The indicator $\tau_t=\mathbf 1\{y_t\widetilde y_t\le0\}$ counts a zero score as a mistake. The total mistakes are $M=\sum_{t=1}^T\tau_t$. For a fixed competitor $u$, the cumulative hinge-power loss is $L_q(u)=\sum_{t=1}^T\ell_q(\langle z_t,u\rangle,y_t)$.
--
--   These definitions fix Algorithm 8.2 and the cumulative quantities in Theorem 8.2.
--
--   **Formalization Note** Rounds start at $1$; index $0$ is unused. The recursion is total for real labels, while each theorem restricts active labels to $\{-1,1\}$. Mathlib's real sign has value $0$ at zero.
-- source:
--   Orabona, arXiv:1912.13213v10, Algorithm 8.2, p. 143; M and L(q), p. 145

import Mathlib
import Definitions.Def_ModernOnlineLearning_Classification_HingePower
import Definitions.Def_ModernOnlineLearning_Adaptive_Defs

namespace ModernOnlineLearning.Classification

/-- Algorithm 8.2, p. 143. The unused zeroth iterate and the first iterate are zero.
At round `t ≥ 1` the update uses the sign of the current inner product, including a
zero score as a mistake. -/
noncomputable def perceptronIter {d : ℕ} (z : ℕ → ModernOnlineLearning.Adaptive.Vec d) (y : ℕ → ℝ) : ℕ → ModernOnlineLearning.Adaptive.Vec d :=
  Nat.rec 0 (fun t w =>
    if t = 0 then 0
    else w + if y t * Real.sign (inner ℝ (z t) w) ≤ 0 then y t • z t else 0)

/-- The indicator `τ_t = 1{y_t sign(⟨z_t,x_t⟩) ≤ 0}` of Algorithm 8.2. -/
noncomputable def mistakeIndicator {d : ℕ} (z : ℕ → ModernOnlineLearning.Adaptive.Vec d) (y : ℕ → ℝ)
    (t : ℕ) : ℝ :=
  if y t * Real.sign (inner ℝ (z t) (perceptronIter z y t)) ≤ 0 then 1 else 0

/-- The Perceptron's mistake count `M = ∑_{t=1}^T τ_t`, p. 145. -/
noncomputable def mistakes {d : ℕ} (z : ℕ → ModernOnlineLearning.Adaptive.Vec d) (y : ℕ → ℝ)
    (T : ℕ) : ℝ :=
  ∑ t ∈ Finset.Icc 1 T, mistakeIndicator z y t

/-- The competitor's cumulative hinge-power loss `L(q)`, p. 145. -/
noncomputable def cumulativeHinge {d : ℕ} (z : ℕ → ModernOnlineLearning.Adaptive.Vec d) (y : ℕ → ℝ)
    (T : ℕ) (u : ModernOnlineLearning.Adaptive.Vec d) (q : ℝ) : ℝ :=
  ∑ t ∈ Finset.Icc 1 T, hingePower q (inner ℝ (z t) u) (y t)

end ModernOnlineLearning.Classification


