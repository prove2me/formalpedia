-- Prove2me | Definitions.Def_CorrelatedTrials_Consistency_CpdeProcess
-- name    : CorrelatedTrials_Consistency_CpdeProcess
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-18T17:26:15.156845+00:00
-- url     : https://prove2.me/theorems/e9a9f404-e2eb-464b-a336-718891573d3f
-- title:
--   §1.2, §3.2 — the trial space and the cPDE allocation process $(\mu^t,\Sigma^t,u_t)$
-- statement:
--   Fix an instance $(\mu^0,\Sigma^0,\lambda,c)$ with $M\ge2$ arms.
--
--   **Trial space.** The sample space carries the unknown mean vector $\theta\in\mathbb R^M$ and an array of noises $\varepsilon_{i,k}$, $i$ an arm and $k=0,1,2,\dots$, with law $\theta\sim N(\mu^0,\Sigma^0)$ independent of i.i.d. $\varepsilon_{i,k}\sim N(0,1)$. The $k$-th sample of arm $i$ is
--
--   $$
--   W_{i,k}=\theta_i+\sqrt{\lambda_i}\,\varepsilon_{i,k},
--   $$
--
--   so that, given $\theta$, the samples are independent with $W_{i,k}\sim N(\theta_i,\lambda_i)$.
--
--   **The cPDE process.** Start from $(\mu^0,\Sigma^0)$ with sample counts $n^0_i=0$. At each time $t=0,1,2,\dots$:
--   1. allocate the observation to the arm $u_t$ that maximizes the cPDE index $\nu^*_i(\mu^t,\Sigma^t)$ of (EC.8), choosing the least index among ties;
--   2. observe $y=W_{u_t,\,n^t_{u_t}}$, the next unread sample of that arm;
--   3. update $(\mu^{t+1},\Sigma^{t+1})$ from $(\mu^t,\Sigma^t)$ by the Bayesian update (8) for arm $u_t$ and observation $y$, and increase $n^t_{u_t}$ by one.
--
--   The trial never stops. $\mu^t$, $\Sigma^t$, $n^t$ and $u_t$ are random through $\omega=(\theta,\varepsilon)$.
--
--   This is the process about which Theorem 1 asserts asymptotic consistency.
--
--   **Formalization Note** The paper breaks ties in the argmax at random (p. 11); here the least index wins. Every arm is eligible at every time ($\mathcal M_t=\mathcal M$). The observation array is the standard construction: the paper's "observation of patient $t+1$" is $W_{u_t,n^t_{u_t}}$, and the law of the trial is the same. Time $t$ counts observations so far, $t=0$ being the prior; arms are 0-based.
-- source:
--   Chick, Gans, Yapar, Bayesian Sequential Learning for Clinical Trials of Multiple Correlated Medical Interventions, SSRN 3184758 (version of August 31, 2020), pp. 5–6, §1.1–1.2; p. 9, (8); p. 11, cPDE allocation policy; p. ec3, (EC.8)

import Mathlib
import Definitions.Def_CorrelatedTrials_Consistency_Model
import Definitions.Def_CorrelatedTrials_Consistency_AllocationIndex

open MeasureTheory ProbabilityTheory

namespace CorrelatedTrials.Consistency

/-! The clinical trial run under the cPDE allocation policy forever (Chick, Gans, Yapar, Bayesian
Sequential Learning for Clinical Trials of Multiple Correlated Medical Interventions,
SSRN 3184758 (version of August 31, 2020), pp. 5–6, §1.1–1.2; p. 9, (8); p. 11, the cPDE
allocation policy; p. ec3, (EC.8)). -/

/-- The trial's sample space: the unknown mean vector `θ` and an array of standard normal noises
`ε_{i,k}`, one for the `k`-th sample (0-based) of each arm `i`. -/
abbrev TrialSpace (M : ℕ) := EuclideanSpace ℝ (Fin M) × (Fin M × ℕ → ℝ)

/-- The law of the trial: `θ ∼ N(µ0, Σ0)` independent of i.i.d. `ε_{i,k} ∼ N(0, 1)`. -/
noncomputable def trialMeasure {M : ℕ} (I : Instance M) : Measure (TrialSpace M) :=
  (multivariateGaussian (WithLp.toLp 2 I.mu0) I.Sig0).prod
    (Measure.infinitePi fun _ : Fin M × ℕ => gaussianReal 0 1)

/-- The unknown mean vector `θ`. -/
def theta {M : ℕ} (ω : TrialSpace M) : Fin M → ℝ := fun i => ω.1 i

/-- The observation array: `W i k = θ_i + √λ_i ε_{i,k}` is the `k`-th (0-based) sample of arm
`i`, so that `W i k | θ ∼ N(θ_i, λ_i)`, independent across `(i, k)` given `θ` (§1.2, p. 6). -/
noncomputable def W {M : ℕ} (I : Instance M) (i : Fin M) (k : ℕ) (ω : TrialSpace M) : ℝ :=
  theta ω i + Real.sqrt (I.lam i) * ω.2 (i, k)

/-- The least-index maximizer of `g` over the arms. -/
noncomputable def leastArgmax {M : ℕ} (hM : 0 < M) (g : Fin M → ℝ) : Fin M :=
  (Finset.univ.filter fun i => ∀ j, g j ≤ g i).min' (by
    obtain ⟨k, _, hk⟩ := Finset.exists_max_image Finset.univ g
      (Finset.univ_nonempty_iff.mpr ⟨⟨0, hM⟩⟩)
    exact ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun j => hk j (Finset.mem_univ _)⟩⟩)

/-- The state of the trial after `t` observations: the posterior mean `µ^t`, the posterior
covariance `Σ^t` and the sample counts `n^t_i`. -/
abbrev State (M : ℕ) := (Fin M → ℝ) × Matrix (Fin M) (Fin M) ℝ × (Fin M → ℕ)

/-- The arm the cPDE allocation policy samples in state `s`: the least-index maximizer of
`ν*_i(µ, Σ)` (EC.8). -/
noncomputable def cpdeChoice {M : ℕ} (I : Instance M) (s : State M) : Fin M :=
  leastArgmax (by have := I.two_le; omega) fun i => nuStar I.lam I.c s.1 s.2.1 i

/-- The cPDE process: start from the prior `(µ0, Σ0)` with no samples; at time `t` allocate one
observation to the arm `u_t` maximizing `ν*_i(µ^t, Σ^t)`, read its next sample
`y = W u_t (n^t_{u_t})`, update the belief by (8), and increase `n^t_{u_t}` by one.

Formalization Note:
1. Ties in the argmax are broken toward the least index; the paper breaks them randomly
   (p. 11).
2. Every arm is eligible at every time (`M_t = M`, Assumption 1 iii) trivial).
3. Time `t` is the number of observations so far; `t = 0` is the prior. -/
noncomputable def cpdeState {M : ℕ} (I : Instance M) : ℕ → TrialSpace M → State M
  | 0, _ => (I.mu0, I.Sig0, fun _ => 0)
  | t + 1, ω =>
    let s := cpdeState I t ω
    let u := cpdeChoice I s
    let b := update I.lam s.1 s.2.1 u (W I u (s.2.2 u) ω)
    (b.1, b.2, Function.update s.2.2 u (s.2.2 u + 1))

/-- The posterior mean `µ^t`. -/
noncomputable def mu {M : ℕ} (I : Instance M) (t : ℕ) (ω : TrialSpace M) : Fin M → ℝ :=
  (cpdeState I t ω).1

/-- The posterior covariance `Σ^t`. -/
noncomputable def Sig {M : ℕ} (I : Instance M) (t : ℕ) (ω : TrialSpace M) :
    Matrix (Fin M) (Fin M) ℝ :=
  (cpdeState I t ω).2.1

/-- The sample counts `n^t_i` (number of observations of arm `i` among the first `t`). -/
noncomputable def count {M : ℕ} (I : Instance M) (t : ℕ) (ω : TrialSpace M) : Fin M → ℕ :=
  (cpdeState I t ω).2.2

/-- The arm `u_t` the cPDE policy samples at time `t`, given the belief `(µ^t, Σ^t)`. -/
noncomputable def alloc {M : ℕ} (I : Instance M) (t : ℕ) (ω : TrialSpace M) : Fin M :=
  cpdeChoice I (cpdeState I t ω)

end CorrelatedTrials.Consistency


