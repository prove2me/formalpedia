-- Prove2me | Definitions.Def_PosteriorSamplingRL_Regret_Confidence
-- name    : PosteriorSamplingRL_Regret_Confidence
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T21:05:00.230977+00:00
-- url     : https://prove2.me/theorems/1a4a8702-6e6a-4547-b92e-1a68addde3ef
-- title:
--   §5.2, p. 6 — visit counts N_{t_k}(s,a), empirical P̂ and R̂, widths β_k(s,a), confidence set 𝓜_k
-- statement:
--   This module defines the confidence sets of §5.2, used in the analysis of PSRL.
--
--   1. **Visit counts.** For a sequence of state–action pairs $(s_{l,j},a_{l,j})$ indexed by episode $l$ and step $j$, $N_{t_k}(s,a)$ is the number of pairs equal to $(s,a)$ in the episodes $l<k$. For a PSRL run it is the number of times $(s,a)$ was sampled before the first time $t_k$ of episode $k$.
--   2. **Empirical estimates.** $\hat P_a(s'\mid s)$ is the fraction of the observed transitions out of $(s,a)$ that went to $s'$, and $\hat R_a(s)$ the average of the rewards observed at $(s,a)$, both over the episodes before $k$.
--   3. **Widths.** For a run of $m$ episodes, with $t_k=(k-1)\tau+1$,
--   $$
--   \beta_k(s,a)=\sqrt{\frac{14\,S\log(2SAm\,t_k)}{\max\{1,N_{t_k}(s,a)\}}}.
--   $$
--   4. **Confidence set.** An MDP $\theta$ lies in $\mathcal M_k$ if for every $(s,a)$
--   $$
--   \big\|\hat P_a(\cdot\mid s)-P^\theta_a(\cdot\mid s)\big\|_1\le\beta_k(s,a)\quad\text{and}\quad\big|\hat R_a(s)-\overline R^\theta_a(s)\big|\le\beta_k(s,a).
--   $$
--
--   The set $\mathcal M_k$ depends only on the history $H_{t_k}$; the analysis bounds the regret on the event that both $M^*$ and $M_k$ lie in it.
--
--   **Formalization Note** In Lean's 0-based episodes $t_k=k\tau+1$. When $(s,a)$ has not been visited, Lean's convention $x/0=0$ sets $\hat P$ and $\hat R$ to $0$; this is harmless, because then $\beta_k(s,a)\ge\sqrt{14\log 2}>2$ while both deviations are at most $1$. The page writes $|\hat R^t_a(s)-R^M_a(s)|$ with $R^M_a(s)$ a distribution; the mean $\overline R^\theta_a(s)$ is meant (footnote 3: the sets are those of UCRL2 with $\delta=1/m$). Transitions are counted including the last step of each episode, whose next state is observed.
-- source:
--   arXiv:1306.0940v5, §5.2, p. 6

import Mathlib
import Definitions.Def_PosteriorSamplingRL_Regret_Run

namespace PosteriorSamplingRL.Regret

open MeasureTheory ProbabilityTheory

variable {S A τ : ℕ} {Θ : Type} [MeasurableSpace Θ]

/-- `visitCount sa k p`: the number of times the pair `p = (s, a)` occurs in the visit sequence
`sa` (episode `l`, step `j`) during episodes `l < k`. For the PSRL run this is
`N_{t_k}(s, a) = ∑_{t=1}^{t_k - 1} 1{(s_t, a_t) = (s, a)}` (arXiv:1306.0940v5, §5.2, p. 6). -/
def visitCount (sa : ℕ → Fin τ → Fin S × Fin A) (k : ℕ) (p : Fin S × Fin A) : ℕ :=
  ((Finset.range k ×ˢ (Finset.univ : Finset (Fin τ))).filter (fun lj => sa lj.1 lj.2 = p)).card

namespace PSRLRun

variable {F : MDPFamily S A Θ} {ρ : Fin S → ℝ} {f : Measure Θ} {sel : Θ → Policy S A τ}
  {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The visited state–action pairs `(s_{k,j}, a_{k,j})` of the run. -/
def visits (R : PSRLRun F ρ f sel μ) (ω : Ω) : ℕ → Fin τ → Fin S × Fin A :=
  fun l j => (R.st l j.castSucc ω, R.act l j ω)

/-- `N_{t_k}(s, a)`: the number of visits to `(s, a)` before (0-based) episode `k`. -/
def count (R : PSRLRun F ρ f sel μ) (k : ℕ) (s : Fin S) (a : Fin A) (ω : Ω) : ℕ :=
  visitCount (R.visits ω) k (s, a)

/-- The number of observed transitions `(s, a) → s'` before episode `k`. -/
def transCount (R : PSRLRun F ρ f sel μ) (k : ℕ) (s : Fin S) (a : Fin A) (s' : Fin S) (ω : Ω) :
    ℕ :=
  ((Finset.range k ×ˢ (Finset.univ : Finset (Fin τ))).filter
    (fun lj => R.visits ω lj.1 lj.2 = (s, a) ∧ R.st lj.1 lj.2.succ ω = s')).card

/-- The sum of the rewards observed at `(s, a)` before episode `k`. -/
noncomputable def rewardSum (R : PSRLRun F ρ f sel μ) (k : ℕ) (s : Fin S) (a : Fin A) (ω : Ω) :
    ℝ :=
  ∑ lj ∈ (Finset.range k ×ˢ (Finset.univ : Finset (Fin τ))).filter
      (fun lj => R.visits ω lj.1 lj.2 = (s, a)), R.rw lj.1 lj.2 ω

/-- The empirical transition distribution `P̂_a(s'|s)` before episode `k` (`0` if `(s, a)` was
never visited). -/
noncomputable def Phat (R : PSRLRun F ρ f sel μ) (k : ℕ) (s : Fin S) (a : Fin A) (s' : Fin S)
    (ω : Ω) : ℝ :=
  (R.transCount k s a s' ω : ℝ) / (R.count k s a ω : ℝ)

/-- The empirical average reward `R̂_a(s)` before episode `k` (`0` if `(s, a)` was never
visited). -/
noncomputable def Rhat (R : PSRLRun F ρ f sel μ) (k : ℕ) (s : Fin S) (a : Fin A) (ω : Ω) : ℝ :=
  R.rewardSum k s a ω / (R.count k s a ω : ℝ)

/-- The confidence width (p. 6) for a run of `m` episodes:
`β_k(s, a) = √(14 S log(2 S A m t_k) / max{1, N_{t_k}(s, a)})`, with `t_k = kτ + 1` the first time
of (0-based) episode `k`. -/
noncomputable def β (R : PSRLRun F ρ f sel μ) (m k : ℕ) (s : Fin S) (a : Fin A) (ω : Ω) : ℝ :=
  Real.sqrt (14 * (S : ℝ) * Real.log (2 * (S : ℝ) * A * m * ((k : ℝ) * τ + 1))
    / max 1 (R.count k s a ω : ℝ))

/-- `θ ∈ 𝓜_k` (p. 6): for every `(s, a)`, `‖P̂_a(·|s) − P^θ_a(·|s)‖₁ ≤ β_k(s, a)` and
`|R̂_a(s) − R̄^θ_a(s)| ≤ β_k(s, a)`. -/
def InConf (R : PSRLRun F ρ f sel μ) (m k : ℕ) (θ : Θ) (ω : Ω) : Prop :=
  ∀ s a, ∑ s', |R.Phat k s a s' ω - F.P θ s a s'| ≤ R.β m k s a ω ∧
    |R.Rhat k s a ω - meanReward F θ s a| ≤ R.β m k s a ω

end PSRLRun

end PosteriorSamplingRL.Regret


