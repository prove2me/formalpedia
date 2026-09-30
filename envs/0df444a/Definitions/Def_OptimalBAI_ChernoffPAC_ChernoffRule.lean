-- Prove2me | Definitions.Def_OptimalBAI_ChernoffPAC_ChernoffRule
-- name    : OptimalBAI_ChernoffPAC_ChernoffRule
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T02:01:53.98301+00:00
-- url     : https://prove2.me/theorems/58052662-3096-43b4-b77e-5fd041e36b43
-- title:
--   Bernoulli bandit class, Bernoulli GLR statistic and Chernoff's stopping rule (8)
-- statement:
--   Consider $K$ arms $\mathcal A = \{1,\dots,K\}$. A **Bernoulli bandit model** is a vector of means $\boldsymbol\mu = (\mu_1,\dots,\mu_K) \in [0,1]^K$; pulling arm $a$ yields reward $1$ with probability $\mu_a$ and $0$ otherwise. The class $\mathcal S$ consists of the Bernoulli models with a **unique optimal arm**: there is an arm $a^*(\boldsymbol\mu)$ with $\mu_{a^*} > \mu_i$ for every $i \ne a^*$.
--
--   Along a trajectory of the bandit game, let $N_a(t)$ be the number of the first $t$ rounds in which arm $a$ was pulled, and $s_a(t)$ the number of those rounds in which the reward was $1$. The likelihood, under mean $u$, of the observations $\underline X^a_{N_a(t)}$ of arm $a$ available at time $t$ is
--
--   $$p_u\big(\underline X^a_{N_a(t)}\big) = u^{s_a(t)}(1-u)^{N_a(t)-s_a(t)} .$$
--
--   For arms $a, b$, the **generalized likelihood ratio statistic** is
--
--   $$Z_{a,b}(t) = \log \frac{\max_{\mu'_a \ge \mu'_b} p_{\mu'_a}\big(\underline X^a_{N_a(t)}\big)\, p_{\mu'_b}\big(\underline X^b_{N_b(t)}\big)}{\max_{\mu'_a \le \mu'_b} p_{\mu'_a}\big(\underline X^a_{N_a(t)}\big)\, p_{\mu'_b}\big(\underline X^b_{N_b(t)}\big)},$$
--
--   the maxima being taken over $\mu'_a, \mu'_b \in [0,1]$. It measures the evidence in the data that arm $a$ is at least as good as arm $b$.
--
--   Given an exploration rate $\beta(t)$, **Chernoff's stopping rule** stops at
--
--   $$\tau = \inf\{t \ge 1 : \exists a \in \mathcal A,\ \forall b \in \mathcal A\setminus\{a\},\ Z_{a,b}(t) > \beta(t)\},$$
--
--   with $\tau = \infty$ if no such $t$ exists. The **informational threshold** of Theorem 10 is $\beta(t,\delta) = \log\big(2t(K-1)/\delta\big)$.
--
--   **Formalization Note** The class $\mathcal S$ is the image of the platform's `bernoulliBandit` on mean vectors in $[0,1]^K$ with a unique maximum; the degenerate means $0$ and $1$ are included (the paper's exponential-family parameterization has mean space $(0,1)$; restricting to $(0,1)$ gives a weaker statement). The paper takes the maxima over the family's mean space $(0,1)$; they equal the maxima over $[0,1]$ by continuity of the likelihood. Both maxima are attained (continuous function, nonempty compact set) and the denominator is positive (it is at least $2^{-(N_a(t)+N_b(t))}$, its value at $\mu'_a = \mu'_b = 1/2$), so the logarithm has no junk value. Trajectory coordinate $s$ is round $s+1$, so "time $t$" means the first $t$ coordinates. The stopping rule starts at $t \ge 1$: at $t = 0$ no arm has been observed, $Z_{a,b}(0) = 0$, and $\beta(0,\delta) = \log 0$ is undefined in the paper (it is $0$ in Lean), so round $0$ never triggers either way. The rule is parametric in $\beta$, matching eq. (8), where $\beta$ is "to be tuned appropriately".
-- source:
--   Garivier, Kaufmann, Optimal Best Arm Identification with Fixed Confidence, arXiv:1602.04589v2, p. 3 (§2.1, δ-PAC and S), p. 4 (S fixed), p. 8 (§3.2, GLR statistic and eq. (8)), p. 10 (Theorem 10, threshold)

import Definitions.Def_TrackAndStop
import Definitions.Def_bernoulliRelativeEntropy

/-!
Garivier, Kaufmann, *Optimal Best Arm Identification with Fixed Confidence*,
arXiv:1602.04589v2: the Bernoulli bandit class `𝒮` (p. 3–4), the Bernoulli
generalized likelihood ratio statistic `Z_{a,b}(t)` (§3.2, p. 8), Chernoff's
stopping rule (8) (p. 8) and the informational threshold
`β(t, δ) = log(2t(K-1)/δ)` of Theorem 10 (p. 10).

Trajectory conventions are those of `Def_BanditTrajectory`: coordinate `s` of
`ω : ℕ → Fin K × ℝ` is round `s + 1`, so "the observations available at time
`t`" are the first `t` coordinates.
-/

open MeasureTheory BanditAlgorithm

namespace OptimalBAI.ChernoffPAC

variable {K : ℕ}

/-- The class `𝒮` of Bernoulli bandit models with a unique optimal arm
(p. 3–4): all `bernoulliBandit μ` with `μ ∈ [0,1]^K` such that some arm `a`
satisfies `μ_i < μ_a` for every `i ≠ a`. -/
def bernoulliClass (K : ℕ) : Set (StochasticBandit K) :=
  Set.range fun μ : {μ : Fin K → ℝ //
      (∀ i, μ i ∈ Set.Icc (0 : ℝ) 1) ∧ ∃ a, ∀ i, i ≠ a → μ i < μ a} =>
    bernoulliBandit μ.1 μ.2.1

/-- `s_a(t)`: the number of rounds among the first `t` in which arm `a` was
played and the observed reward equals `1`. Together with `N_a(t) =
trajPullCount a t ω` it is a sufficient statistic of the Bernoulli sample of
arm `a` (rewards lie in `{0,1}` almost surely under a Bernoulli bandit). -/
noncomputable def trajOnesCount (a : Fin K) (t : ℕ) (ω : ℕ → Fin K × ℝ) : ℕ :=
  ((Finset.range t).filter fun s ↦ (ω s).1 = a ∧ (ω s).2 = 1).card

/-- The Bernoulli likelihood `u^s (1-u)^{n-s}` of a sample of size `n` with `s`
ones (natural-number exponents, so `0^0 = 1`). -/
noncomputable def bernCountLik (n s : ℕ) (u : ℝ) : ℝ :=
  u ^ s * (1 - u) ^ (n - s)

/-- `p_u(X^a_{N_a(t)})`: the likelihood, under mean `u`, of the observations of
arm `a` available at time `t`. -/
noncomputable def trajArmLik (a : Fin K) (t : ℕ) (ω : ℕ → Fin K × ℝ) (u : ℝ) : ℝ :=
  bernCountLik (trajPullCount a t ω) (trajOnesCount a t ω) u

/-- The generalized likelihood ratio statistic of §3.2 (p. 8), Bernoulli case:
`Z_{a,b}(t) = log (max_{u ≥ v} p_u(X^a) p_v(X^b) / max_{u ≤ v} p_u(X^a) p_v(X^b))`,
the maxima taken over means `u, v ∈ [0,1]`. Both maxima are attained (a
continuous function on a nonempty compact set) and the denominator is positive
(it is at least its value `2^{-(N_a(t)+N_b(t))}` at `u = v = 1/2`), so the
logarithm is applied to a positive real. -/
noncomputable def glrStat (a b : Fin K) (t : ℕ) (ω : ℕ → Fin K × ℝ) : ℝ :=
  Real.log
    (sSup ((fun p : ℝ × ℝ ↦ trajArmLik a t ω p.1 * trajArmLik b t ω p.2) ''
        {p | p.1 ∈ Set.Icc (0 : ℝ) 1 ∧ p.2 ∈ Set.Icc (0 : ℝ) 1 ∧ p.2 ≤ p.1}) /
      sSup ((fun p : ℝ × ℝ ↦ trajArmLik a t ω p.1 * trajArmLik b t ω p.2) ''
        {p | p.1 ∈ Set.Icc (0 : ℝ) 1 ∧ p.2 ∈ Set.Icc (0 : ℝ) 1 ∧ p.1 ≤ p.2}))

/-- The informational threshold of Theorem 10 (p. 10):
`β(t, δ) = log(2t(K-1)/δ)`. -/
noncomputable def informationalThreshold (K : ℕ) (δ : ℝ) (t : ℕ) : ℝ :=
  Real.log (2 * (t : ℝ) * ((K : ℝ) - 1) / δ)

/-- Chernoff's stopping rule (8) (p. 8) with exploration rate `β`:
`τ = inf {t ≥ 1 : ∃ a, ∀ b ≠ a, Z_{a,b}(t) > β(t)}`, with value `⊤` if the set is
empty (the rule never stops). -/
noncomputable def chernoffStop (β : ℕ → ℝ) (ω : ℕ → Fin K × ℝ) : ℕ∞ :=
  sInf {t : ℕ∞ | ∃ n : ℕ, (n : ℕ∞) = t ∧ 1 ≤ n ∧
    ∃ a : Fin K, ∀ b : Fin K, b ≠ a → β n < glrStat a b n ω}

end OptimalBAI.ChernoffPAC


