-- Prove2me | Definitions.Def_FragileBandit_CauchyTail_Setting
-- name    : FragileBandit_CauchyTail_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-24T04:40:05.011993+00:00
-- url     : https://prove2.me/theorems/dc0415a8-7760-46df-af12-3a03189417b4
-- title:
--   §2, pp. 7–9 — one-parameter exponential family (1)–(3), M_P-optimized algorithms (Definition 2), discrimination equivalence (Definition 3), the tail exponent of (7)
-- statement:
--   The model of Fan and Glynn, *The Fragility of Optimized Bandit Algorithms* (§2, pp. 7–9), built on the published canonical bandit model: an environment $\nu = (Q_1,\dots,Q_K)$ is a $K$-tuple of probability laws on $\mathbb R$, an algorithm $\pi$ is a sequence of probability kernels from the history to the next arm, $\mathbb P_{\nu\pi}$ is the induced law of the history, and $N_i(T)$ is the number of plays of arm $i$ in the first $T$ rounds. Write $\mu_i$ for the mean of $Q_i$ and $\mu_*(\nu) = \max_i \mu_i$.
--
--   **Exponential family.** Let $P$ be a probability law on $\mathbb R$ (the base distribution) with cumulant generating function $\Lambda_P(\theta) = \log \int e^{\theta x}P(dx)$, and let
--
--   $$\Theta_P = \{\theta \in \mathbb R : \Lambda_P(\theta) < \infty\}.$$
--
--   For $\theta \in \Theta_P$ the tilt $P^\theta(dx) = \exp(\theta x - \Lambda_P(\theta))\,P(dx)$ is a probability law. The mean set $\mathcal I_P$ is the set of finite means of these tilts, and for $z \in \mathcal I_P$, $\theta_P(z)$ is the parameter whose tilt has mean $z$, so that
--
--   $$P^z(dx) = \exp\big(\theta_P(z)x - \Lambda_P(\theta_P(z))\big)\,P(dx),\qquad z \in \mathcal I_P \quad (1)$$
--
--   and $\mathcal M_P = \{P^z : z \in \mathcal I_P\}$ (2). The divergence of (3) is $d_P(z_1,z_2) = \int \log \frac{dP^{z_1}}{dP^{z_2}}\,dP^{z_1}$, the Kullback–Leibler divergence $D(P^{z_1}\,\|\,P^{z_2})$. An environment lies in $\mathcal M_P^K$ when every arm law lies in $\mathcal M_P$; the paper's standing convention (p. 7) is that the arm means are pairwise distinct. $\mathbb E_{\nu\pi}[N_i(T)]$ denotes the expected number of plays of arm $i$.
--
--   **Definition 2 ($\mathcal M_P$-optimized algorithm).** $\pi$ is $\mathcal M_P$-optimized if for every environment $\nu \in \mathcal M_P^K$ (with distinct means) and every sub-optimal arm $i$,
--
--   $$\lim_{T\to\infty} \frac{\mathbb E_{\nu\pi}[N_i(T)]}{\log T} = \frac{1}{d_P(\mu_i,\mu_*(\nu))}.$$
--
--   **Tail exponent.** For $z_1, z_2 \in \mathbb R$ set $\rho_P(z_1,z_2) = \inf_{z \in \mathcal I_P,\ z < z_2} d_P(z,z_1)/d_P(z,z_2)$, with $\inf\emptyset = +\infty$. For an arm $k$ the exponent of (7) is $\sum_{j:\ \mu_j > \mu_k} \rho_P(\mu_j,\mu_k)$: when $k = r(i)$ is the $i$-th-best arm, the arms with a larger mean are $r(1),\dots,r(i-1)$.
--
--   **Definition 3 (discrimination equivalence).** $P$ is discrimination equivalent if $\rho_P(z_1,z_2) = 1$ for all $z_1 > z_2$ in $\mathcal I_P$ (6).
--
--   Finally, for an environment $\nu$, an arm $i$ and a probability law $Q$, $\nu$ with arm $i$ replaced by $Q$ is the environment of the changes of measure in Appendix D.
--
--   These objects carry every statement of the mission: the goal (Theorem 1) bounds the tail of $N_k(T)$ by the exponent above for every $\mathcal M_P$-optimized algorithm.
--
--   **Formalization Note** $\Theta_P$ is the set of $\theta$ for which $x\mapsto e^{\theta x}$ is $P$-integrable (Mathlib's `cgf` has the junk value 0 at a non-integrable $\theta$). Tilts use `Measure.tilted`. $\mathcal I_P$ requires the tilt to have an integrable identity, so an endpoint $\theta$ whose tilt has infinite mean contributes nothing. $\theta_P(z)$ is a chosen parameter with mean $z$: it is unique unless $P$ is a point mass, in which case every tilt is $P$. $d_P$ is `klDiv`, valued in $[0,\infty]$; for $z_1 \ne z_2$ in $\mathcal I_P$ it is finite and positive, so Definition 2 takes its real value. $\rho_P$ and the exponent are valued in $[0,\infty]$. Distinct means is `Function.Injective` of the arm means. $\mathbb E_{\nu\pi}[N_i(T)]$ integrates the pull count against `banditMeasure ν π T`.
-- source:
--   Fan, Glynn, The Fragility of Optimized Bandit Algorithms, arXiv:2109.13595v8, pp. 7–9, §2.1, (1)–(3), Definitions 2–3, (6), (7)

import Mathlib
import Definitions.Def_StochasticBandit
import Definitions.Def_BanditPolicy
import Definitions.Def_ConsistentBanditPolicy

namespace FragileBandit.CauchyTail

open MeasureTheory ProbabilityTheory Filter BanditAlgorithm
open scoped ENNReal Topology

/-- The natural parameter set `Θ_P = {θ ∈ ℝ : Λ_P(θ) < ∞}` of a base law `P` (§2.2, p. 8), written as
the set of `θ` for which `x ↦ e^{θx}` is `P`-integrable (equivalently `Λ_P(θ) = log ∫ e^{θx} P(dx) < ∞`).
This avoids Mathlib's `cgf`, whose junk value `0` at a non-integrable `θ` would put every `θ` into `Θ_P`. -/
def natParamSet (P : Measure ℝ) : Set ℝ :=
  {θ | Integrable (fun x => Real.exp (θ * x)) P}

/-- The exponential tilt `P^θ(dx) = exp(θx − Λ_P(θ)) P(dx)` of `P` (the right side of (1), p. 7, with
`θ = θ_P(z)`). Mathlib's `Measure.tilted` normalizes by `∫ e^{θx} P(dx) = e^{Λ_P(θ)}`; it is used only for
`θ ∈ Θ_P`. -/
noncomputable def tilt (P : Measure ℝ) (θ : ℝ) : Measure ℝ :=
  P.tilted (fun x => θ * x)

/-- The mean set `I_P` (p. 8): the means of the tilts `P^θ`, `θ ∈ Θ_P`, whose mean is finite. -/
def meanSet (P : Measure ℝ) : Set ℝ :=
  {z | ∃ θ ∈ natParamSet P, Integrable id (tilt P θ) ∧ ∫ x, x ∂(tilt P θ) = z}

open Classical in
/-- The mean parameterization `θ_P(z)` (p. 8): for `z ∈ I_P`, a natural parameter `θ ∈ Θ_P` whose tilt has
mean `z` (chosen; it is unique unless `P` is a point mass, in which case every tilt equals `P`). The value
`0` outside `I_P` is never used. -/
noncomputable def thetaOf (P : Measure ℝ) (z : ℝ) : ℝ :=
  if h : ∃ θ ∈ natParamSet P, Integrable id (tilt P θ) ∧ ∫ x, x ∂(tilt P θ) = z then h.choose else 0

/-- The mean-parameterized family member `P^z` of (1), p. 7: the tilt of `P` at `θ_P(z)`. -/
noncomputable def expFam (P : Measure ℝ) (z : ℝ) : Measure ℝ :=
  tilt P (thetaOf P z)

/-- The model `M_P = {P^z : z ∈ I_P}` of (2), p. 8. -/
def model (P : Measure ℝ) : Set (Measure ℝ) :=
  expFam P '' meanSet P

/-- The divergence `d_P(z₁, z₂) = ∫ log (dP^{z₁}/dP^{z₂}) dP^{z₁}` of (3), p. 8: the Kullback–Leibler
divergence `D(P^{z₁} ‖ P^{z₂})`, valued in `ℝ≥0∞`. -/
noncomputable def dP (P : Measure ℝ) (z₁ z₂ : ℝ) : ℝ≥0∞ :=
  InformationTheory.klDiv (expFam P z₁) (expFam P z₂)

/-- `ν ∈ M_P^K` (p. 8): every arm law of the environment lies in `M_P`. -/
def IsModelEnv {K : ℕ} (P : Measure ℝ) (ν : StochasticBandit K) : Prop :=
  ∀ i, ν.P i ∈ model P

/-- The standing convention of §2.1 (p. 7) that for each `i` the `i`-th-best arm is unique: the arm means
are pairwise distinct. -/
def DistinctMeans {K : ℕ} (ν : StochasticBandit K) : Prop :=
  Function.Injective (banditArmMean ν)

/-- The expected number of plays `E_νπ[N_i(T)]` of arm `i` in the first `T` rounds. -/
noncomputable def expPulls {K : ℕ} (ν : StochasticBandit K) (π : BanditPolicy K) (T : ℕ) (i : Fin K) : ℝ :=
  ∫ h, (armPullCount i h : ℝ) ∂(banditMeasure ν π T)

/-- Definition 2 (p. 8), `M_P`-optimized algorithm: for every environment `ν ∈ M_P^K` (with pairwise
distinct means, the §2.1 convention) and every sub-optimal arm `i`,
`E_νπ[N_i(T)] / log T → 1 / d_P(µ_i, µ_*(ν))`. For `µ_i < µ_*(ν)` in `I_P` the divergence is finite and
positive, so `toReal` is faithful. -/
def IsOptimized {K : ℕ} (P : Measure ℝ) (π : BanditPolicy K) : Prop :=
  ∀ ν : StochasticBandit K, IsModelEnv P ν → DistinctMeans ν → ∀ i, 0 < banditGap ν i →
    Tendsto (fun T : ℕ => expPulls ν π T i / Real.log T) atTop
      (𝓝 (1 / (dP P (banditArmMean ν i) (banditOptimalMean ν)).toReal))

/-- The ratio `inf_{z ∈ I_P, z < z₂} d_P(z, z₁) / d_P(z, z₂)` of (6) and (7), valued in `ℝ≥0∞`
(the infimum of the empty set is `+∞`). -/
noncomputable def tailRatio (P : Measure ℝ) (z₁ z₂ : ℝ) : ℝ≥0∞ :=
  ⨅ z ∈ meanSet P ∩ Set.Iio z₂, dP P z z₁ / dP P z z₂

/-- The tail exponent of (7) for arm `k` (the paper's `r(i)`):
`∑_{j=1}^{i-1} inf_{z ∈ I_P, z < µ_{r(i)}} d_P(z, µ_{r(j)}) / d_P(z, µ_{r(i)})`, where the arms
`r(1), …, r(i−1)` are exactly the arms `j` with `µ_j > µ_k`. Valued in `ℝ≥0∞`. -/
noncomputable def tailExponent {K : ℕ} (P : Measure ℝ) (ν : StochasticBandit K) (k : Fin K) : ℝ≥0∞ :=
  ∑ j ∈ Finset.univ.filter (fun j => banditArmMean ν k < banditArmMean ν j),
    tailRatio P (banditArmMean ν j) (banditArmMean ν k)

/-- Definition 3 (p. 9), discrimination equivalence: for all `z₁ > z₂` in `I_P`,
`inf_{z ∈ I_P, z < z₂} d_P(z, z₁) / d_P(z, z₂) = 1`. -/
def IsDiscEquiv (P : Measure ℝ) : Prop :=
  ∀ z₁ ∈ meanSet P, ∀ z₂ ∈ meanSet P, z₂ < z₁ → tailRatio P z₁ z₂ = 1

/-- The environment obtained from `ν` by replacing the law of arm `i` by the probability measure `Q`
(the changes of environment in Appendix D, pp. 45–46). -/
noncomputable def replaceArm {K : ℕ} (ν : StochasticBandit K) (i : Fin K) (Q : Measure ℝ)
    (hQ : IsProbabilityMeasure Q) : StochasticBandit K where
  P := Function.update ν.P i Q
  prob := fun j => by
    by_cases h : j = i
    · subst h; simpa using hQ
    · simpa [Function.update_of_ne h] using ν.prob j

end FragileBandit.CauchyTail


