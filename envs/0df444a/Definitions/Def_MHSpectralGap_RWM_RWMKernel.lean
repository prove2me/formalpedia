-- Prove2me | Definitions.Def_MHSpectralGap_RWM_RWMKernel
-- name    : MHSpectralGap_RWM_RWMKernel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T22:14:06.403154+00:00
-- url     : https://prove2.me/theorems/bf97da06-b780-4700-841f-c1dd8f1d70ea
-- title:
--   (2.5) and Algorithm 2, pp. 8, 14 — the Gaussian target γ_m on ℝ^m with variances 1/i², the RWM proposal, acceptance and kernel P_m
-- statement:
--   Fix $m\in\mathbb N$ and identify $\mathbb R^m$ with coordinates $x=(x_1,\dots,x_m)$. The **target measure** (2.5) is
--
--   $$
--   \mu_m=\gamma_m=\mathcal L\Bigl(\sum_{i=1}^m \tfrac1i\,\xi_i e_i\Bigr),\qquad \xi_i\ \text{i.i.d.}\ \mathcal N(0,1),
--   $$
--
--   i.e. the centred Gaussian measure on $\mathbb R^m$ with independent coordinates $x_i\sim\mathcal N(0,1/i^2)$; its covariance $C$ satisfies $\langle x,C^{-1}x\rangle=\sum_{i=1}^m i^2x_i^2$.
--
--   **Random walk Metropolis** (Algorithm 2) with step size $\delta$ proposes, from $x$, the point $y=x+\sqrt{2\delta}\,\xi$ with $\xi\sim\gamma_m$, and accepts it with probability
--
--   $$
--   \alpha(x,y)=1\wedge\exp\Bigl(\tfrac12\langle x,C^{-1}x\rangle-\tfrac12\langle y,C^{-1}y\rangle\Bigr)=1\wedge\exp\Bigl(\sum_{i=1}^m\tfrac{i^2}{2}\,(x_i^2-y_i^2)\Bigr),
--   $$
--
--   which is Algorithm 2's acceptance probability with potential $\Phi=0$ (p. 14: "in the setting of (1.1) this corresponds to $\Phi=0$"). The RWM Markov kernel $P_m$ is the Metropolis–Hastings kernel (1.3) built from this proposal and this acceptance probability; it is reversible with respect to $\gamma_m$.
--
--   These are the objects of Theorem 2.17, which shows that the $L^2$-spectral gap of $P_m$ degenerates as $m\to\infty$ under the step-size scaling $\delta_m=s\,m^{-a}$.
--
--   **Formalization Note** The state space is `Fin m → ℝ`; the coordinate `i : Fin m` is the paper's $x_{i+1}$, so its variance is $1/(i+1)^2$ and its weight in $\langle x,C^{-1}x\rangle$ is $(i+1)^2$. The paper's space $\mathcal H^\sigma_m$ is all of $\mathbb R^m$ for every $\sigma$, since the defining sum is finite. Display (1.4) prints the acceptance probability without the exponential; that is a misprint, and Algorithm 2 and p. 16 have it. The file also records the instances that $\gamma_m$ is a probability measure and the proposal is a Markov kernel.
-- source:
--   Hairer, Stuart and Vollmer, Spectral gaps for a Metropolis–Hastings algorithm in infinite dimensions, arXiv:1112.1392v4, p. 14, display (2.5); p. 8, Algorithm 2; p. 3, display (1.3)

import Mathlib
import Definitions.Def_MHSpectralGap_RWM_MHKernel

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace MHSpectralGap.RWM

/-- The target (2.5), p. 14: `μ_m = γ_m = L(∑_{i=1}^m (1/i) ξ_i e_i)` with `ξ_i` i.i.d. `N(0,1)`,
as a measure on `ℝ^m = Fin m → ℝ`. Coordinate `i : Fin m` is the paper's `x_{i+1}`, so it is
`N(0, 1/(i+1)²)`, independently across coordinates. -/
noncomputable def gammaM (m : ℕ) : Measure (Fin m → ℝ) :=
  Measure.pi (fun i : Fin m => gaussianReal 0 (1 / ((i : ℝ≥0) + 1) ^ 2))

/-- The RWM proposal of Algorithm 2, p. 8: from `x`, propose `x + √(2δ) ξ` with `ξ ∼ γ_m`. -/
noncomputable def rwmProposal (m : ℕ) (δ : ℝ) :
    ProbabilityTheory.Kernel (Fin m → ℝ) (Fin m → ℝ) :=
  (ProbabilityTheory.Kernel.id ×ₖ ProbabilityTheory.Kernel.const _ (gammaM m)).map
    (fun p => p.1 + Real.sqrt (2 * δ) • p.2)

instance (m : ℕ) : IsProbabilityMeasure (gammaM m) := by
  unfold gammaM; infer_instance

instance (m : ℕ) (δ : ℝ) : ProbabilityTheory.IsMarkovKernel (rwmProposal m δ) :=
  ProbabilityTheory.Kernel.IsMarkovKernel.map _ (by fun_prop)

/-- The RWM acceptance probability of Algorithm 2, p. 8, for the target (2.5) (`Φ = 0`,
`⟨x, C⁻¹x⟩ = ∑_{i=1}^m i² x_i²`):
`α(x, y) = 1 ∧ exp(½⟨x, C⁻¹x⟩ − ½⟨y, C⁻¹y⟩) = 1 ∧ exp(∑_i (i²/2)(x_i² − y_i²))`. -/
noncomputable def rwmAccept (m : ℕ) (x y : Fin m → ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (min 1 (Real.exp (∑ i : Fin m, ((i : ℝ) + 1) ^ 2 / 2 * (x i ^ 2 - y i ^ 2))))

/-- The RWM Markov kernel `P_m` with step size `δ` for the target `γ_m`: the
Metropolis–Hastings kernel (1.3) with proposal `rwmProposal m δ` and acceptance `rwmAccept m`. -/
noncomputable def rwmKernel (m : ℕ) (δ : ℝ) : ProbabilityTheory.Kernel (Fin m → ℝ) (Fin m → ℝ) :=
  mhKernel (rwmProposal m δ) (rwmAccept m)

end MHSpectralGap.RWM


