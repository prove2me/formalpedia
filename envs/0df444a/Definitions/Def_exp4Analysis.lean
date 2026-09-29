-- Prove2me | Definitions.Def_exp4Analysis
-- name    : exp4Analysis
-- status  : Definition
-- author  : @Harry_Xu
-- created : 2026-07-29T00:08:01.938728+00:00
-- url     : https://prove2.me/theorems/a3a986c5-895a-408e-a8a3-4078a5d1b9a5
-- title:
--   Exp4 analysis processes
-- statement:
--   For Exp4 with exploration parameter $\gamma=0$, let $Q_{t,m}$ be the exponential weight of expert $m$, let $P_{t,a}=\sum_m Q_{t,m}E_{t,m,a}$ be the induced arm distribution, and let $(A_t,X_t)$ be the selected arm and observed reward.
--
--   The one-round score propagated to expert $m$ is
--
--   $$
--   \widetilde X_{t,m}
--   =
--   \sum_{a=1}^{k}E_{t,m,a}
--   \left(1-\frac{\mathbf 1\{A_t=a\}(1-X_t)}{P_{t,a}}\right).
--   $$
--
--   The analysis records the cumulative mixture score and cumulative quadratic mass
--
--   $$
--   \sum_{t=1}^{n}\sum_{m=1}^{M}Q_{t,m}\widetilde X_{t,m},
--   \qquad
--   \sum_{t=1}^{n}\sum_{m=1}^{M}Q_{t,m}(1-\widetilde X_{t,m})^2.
--   $$
--
--   These are the two process-level quantities occurring in the Exp4 potential inequality and its second-moment estimate, so they can be reused in regret analyses before expectation and optimization of the learning rate.
--
--   **Formalization Note** `exp4RewardIncrement`, `exp4MixtureEstimate`, and `exp4QuadraticMass` define the displayed quantities recursively on finite bandit histories.
-- source:
--   Lattimore and Szepesvári, Bandit Algorithms (Cambridge University Press, 2020), Algorithm 11, printed p. 229, lines 7–9, and Theorem 18.1 proof, printed p. 230, Eqs. (18.9)–(18.12). https://tor-lattimore.com/downloads/book/book.pdf

import Definitions.Def_exp4Policy

open MeasureTheory ProbabilityTheory

namespace BanditAlgorithm

/-!
Analysis quantities from Lattimore--Szepesvári, *Bandit Algorithms*,
Algorithm 11 and the proof of Theorem 18.1, printed pp. 229--230.
-/

/-- The one-round reward estimate propagated by Exp4 from the selected arm to
expert `m` (Algorithm 11, lines 7--8). -/
noncomputable def exp4RewardIncrement {k M : ℕ} (η : ℝ)
    (E : ℕ → Fin M → Fin k → ℝ) (r : ℕ)
    (h : BanditHistory k r) (m : Fin M) (z : Fin k × ℝ) : ℝ :=
  ∑ a, E r m a *
    (1 - if z.1 = a then
      (1 - z.2) / exp4Prob η 0 E r h a
    else 0)

/-- The cumulative Exp4 mixture score
`∑ₜ ∑ₘ Qₜₘ X̃ₜₘ` in Eqs. (18.9)--(18.11). -/
noncomputable def exp4MixtureEstimate {k M : ℕ} (η : ℝ)
    (E : ℕ → Fin M → Fin k → ℝ) :
    (n : ℕ) → BanditHistory k n → ℝ
  | 0, _ => 0
  | r + 1, h =>
      exp4MixtureEstimate η E r (Fin.init h) +
        ∑ m, exp4ExpertWeights η 0 E r (Fin.init h) m *
          exp4RewardIncrement η E r (Fin.init h) m (h (Fin.last r))

/-- The cumulative quadratic term
`∑ₜ ∑ₘ Qₜₘ (1-X̃ₜₘ)²` in Eqs. (18.9)--(18.12). -/
noncomputable def exp4QuadraticMass {k M : ℕ} (η : ℝ)
    (E : ℕ → Fin M → Fin k → ℝ) :
    (n : ℕ) → BanditHistory k n → ℝ
  | 0, _ => 0
  | r + 1, h =>
      exp4QuadraticMass η E r (Fin.init h) +
        ∑ m, exp4ExpertWeights η 0 E r (Fin.init h) m *
          (1 - exp4RewardIncrement η E r (Fin.init h) m
            (h (Fin.last r))) ^ 2

end BanditAlgorithm


