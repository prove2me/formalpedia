-- Prove2me | Definitions.Def_KellyReversibility_Symmetric_GammaMixture
-- name    : KellyReversibility_Symmetric_GammaMixture
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T02:36:53.975407+00:00
-- url     : https://prove2.me/theorems/908eebff-a5d5-432a-b28b-0c16ce7284fe
-- title:
--   Distribution functions of mixtures of gamma distributions with integer shape
-- statement:
--   For an integer $w \ge 1$ and $d > 0$, let $G_{w,d}$ be the distribution function of the sum of $w$ independent exponential random variables of mean $d$, i.e. of the gamma distribution with shape $w$ and rate $1/d$ (mean $wd$, variance $wd^2$).
--
--   A function $F : \mathbb R \to \mathbb R$ is the **distribution function of a mixture of gamma distributions** (Kelly, p. 76) when there are countably many components $z$ with weights $p(z) \ge 0$, $\sum_z p(z) = 1$, integer shapes $w(z) \ge 1$ and stage means $d(z) > 0$ such that
--   $$F(x) = \sum_z p(z)\, G_{w(z), d(z)}(x) \qquad \text{for all } x \in \mathbb R.$$
--
--   These are exactly the service requirement distributions for which a symmetric queue has the Markov description of §3.3; Lemma 3.9 says they approximate every distribution of a positive random variable.
--
--   **Formalization Note** The countable index set is $\mathbb N$; a finite mixture is the case of weights that vanish from some index on. $G_{w,d}$ is Mathlib's `cdf (gammaMeasure w d⁻¹)`.
-- source:
--   Kelly, Reversibility and Stochastic Networks, Wiley 1979, p. 76 (PDF p. 79), 'mixture of gamma distributions'; p. 74 (stages and the gamma distribution)

import Mathlib

namespace KellyReversibility.Symmetric

open MeasureTheory ProbabilityTheory

/-- The distribution function of the gamma distribution of a sum of `w ≥ 1` independent
exponential stages each of mean `d > 0`: shape `w`, rate `1/d`, mean `w d`, variance `w d²`
(Kelly 1979, pp. 72, 74). -/
noncomputable def gammaStageCDF (w : ℕ) (d : ℝ) (x : ℝ) : ℝ :=
  cdf (gammaMeasure (w : ℝ) d⁻¹) x

/-- `F` is the distribution function of a mixture of gamma distributions (Kelly 1979, p. 76):
there are countably many components `z`, indexed here by `ℕ`, with weights `p z ≥ 0` summing
to `1`, integer shapes `w z ≥ 1` and stage means `d z > 0`, such that
`F x = ∑_z p z · G_{w z, d z}(x)` for every real `x`. -/
def IsGammaMixtureCDF (F : ℝ → ℝ) : Prop :=
  ∃ (p : ℕ → ℝ) (w : ℕ → ℕ) (d : ℕ → ℝ),
    (∀ z, 0 ≤ p z) ∧ HasSum p 1 ∧ (∀ z, 1 ≤ w z) ∧ (∀ z, 0 < d z) ∧
    ∀ x, F x = ∑' z, p z * gammaStageCDF (w z) (d z) x

end KellyReversibility.Symmetric


