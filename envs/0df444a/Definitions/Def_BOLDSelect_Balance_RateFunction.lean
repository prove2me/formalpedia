-- Prove2me | Definitions.Def_BOLDSelect_Balance_RateFunction
-- name    : BOLDSelect_Balance_RateFunction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T00:41:04.225041+00:00
-- url     : https://prove2.me/theorems/fd381e96-bfa1-467e-97fa-166c90373389
-- title:
--   §2–§3, pp. 3370–3371 — the rate function $I_x(u;\theta)$ of a distributional family, its derivative $D_x(u;\theta)$ and its effective domain
-- statement:
--   This file fixes the large-deviations objects of Chen and Ryzhov's analysis of the BOLD allocation for ranking and selection.
--
--   There are $M$ alternatives, indexed by $x \in \{1,\dots,M\}$. Each alternative $x$ comes with a **distributional family**: for every real parameter $\theta$, a probability law $F_x(\theta)$ on $\mathbb R$, thought of as the member of $x$'s family with mean $\theta$. Different alternatives may have different families (one normal, one Bernoulli, and so on).
--
--   1. **Log-moment generating function.** For a sample $W \sim F_x(\theta)$,
--   $$\Psi_{x,\theta}(\gamma) = \log \mathbb E\, e^{\gamma W} \in (-\infty, +\infty],$$
--   with the value $+\infty$ when the expectation is infinite.
--   2. **Rate function.** The large-deviations rate function of the member with mean $\theta$ is the Fenchel–Legendre transform
--   $$I_x(u;\theta) = \sup_{\gamma \in \mathbb R} \big(\gamma u - \Psi_{x,\theta}(\gamma)\big) \in [0, +\infty].$$
--   It may equal $+\infty$: for a Bernoulli family, $I_x(u;\theta) = +\infty$ for $u \notin [0,1]$.
--   3. **Derivative.** $D_x(u;\theta) = \frac{d}{du} I_x(u;\theta)$, the derivative in the first argument.
--   4. **Effective domain.** $\mathcal D_x$ is the interior of the set of pairs $(u,\theta)$ with $I_x(u;\theta) < \infty$. For a normal family it is all of $\mathbb R^2$; for a Bernoulli family it is $(0,1)^2$.
--
--   The plug-in estimates of §3 are $I^n_x(\cdot) = I_x(\cdot;\theta^n_x)$ and $D^n_x(\cdot) = D_x(\cdot;\theta^n_x)$, where $\theta^n_x$ is the sample mean of alternative $x$ at time $n$; they are built from these objects in the companion definition file of the BOLD algorithm. For the normal family $\mathcal N(\theta,\lambda_x^2)$ one has $I_x(u;\theta) = (u-\theta)^2/(2\lambda_x^2)$.
--
--   **Formalization Note** $\Psi$ and the Legendre transform are the published `BellWilliams2001.ThresholdPolicy.logMGF` and `legendre`, computed in the extended reals, so $+\infty$ is a genuine value and never a junk $0$. The rate function is also provided as an element of $[0,\infty]$ (`rateE`); this loses nothing because $I_x \ge 0$ for a probability law (take $\gamma = 0$). $D_x$ is the derivative of the real part of $I_x$; it is a genuine derivative only on the effective domain, and every condition on it in the mission is imposed there. Alternatives are `Fin M`, indexed $0,\dots,M-1$.
-- source:
--   Chen & Ryzhov, Balancing Optimal Large Deviations in Ranking and Selection, Proc. 2019 Winter Simulation Conference, pp. 3370–3371, §2 (definition of Ψ_x and I_x) and §3 (I^n_x, D_x, D^n_x)

import Mathlib
import Definitions.Def_BellWilliams2001_ThresholdPolicy_LargeDeviation

open MeasureTheory
open scoped ENNReal

namespace BOLDSelect.Balance

/-!
Chen & Ryzhov, *Balancing Optimal Large Deviations in Ranking and Selection*, Proc. 2019 Winter
Simulation Conference, §2 (p. 3370) and §3 (p. 3371): the large-deviations rate function
`I_x(u;θ)` of the member with mean `θ` of alternative `x`'s distributional family, its derivative
`D_x(u;θ) = ∂I_x/∂u`, and the region on which `I_x` is finite.

Alternatives are `Fin M` (the paper's `1, …, M`). A family is `Fam : Fin M → ℝ → Measure ℝ`; the
member `Fam x θ` is the law with mean parameter `θ` (constrained only where the theorems say so).
-/

/-- The rate function `I_x(u;θ) = sup_γ (γ u − Ψ(γ))`, the Fenchel–Legendre transform of the
log-MGF `Ψ(γ) = log E e^{γ W}` of a sample `W ∼ Fam x θ` (p. 3370), with values in `[0, +∞]` as an
extended real (`+∞` where the supremum is infinite, e.g. outside `[0,1]` for a Bernoulli family). -/
noncomputable def rateI {M : ℕ} (Fam : Fin M → ℝ → Measure ℝ) (x : Fin M) (u θ : ℝ) : EReal :=
  BellWilliams2001.ThresholdPolicy.legendre
    (BellWilliams2001.ThresholdPolicy.logMGF (Fam x θ) id) u

/-- `I_x(u;θ)` as an element of `[0, ∞]`. For a probability measure `I_x ≥ 0` (take `γ = 0`), so this
loses nothing; it is the form used in the ratios (12) and in `Γ` (11). -/
noncomputable def rateE {M : ℕ} (Fam : Fin M → ℝ → Measure ℝ) (x : Fin M) (u θ : ℝ) : ℝ≥0∞ :=
  (rateI Fam x u θ).toENNReal

/-- `D_x(u;θ) = (d/du) I_x(u;θ)` (p. 3371): the derivative in `u` of the real-valued rate function.
It is meaningful on `effDom Fam x`, where `I_x` is finite near `(u, θ)`. -/
noncomputable def rateD {M : ℕ} (Fam : Fin M → ℝ → Measure ℝ) (x : Fin M) (u θ : ℝ) : ℝ :=
  deriv (fun v => (rateI Fam x v θ).toReal) u

/-- The (interior of the) effective domain of `(u, θ) ↦ I_x(u;θ)`: the pairs near which the rate
function is finite. For a normal family it is all of `ℝ × ℝ`; for a Bernoulli family it is
`(0,1) × (0,1)`. -/
def effDom {M : ℕ} (Fam : Fin M → ℝ → Measure ℝ) (x : Fin M) : Set (ℝ × ℝ) :=
  interior {p : ℝ × ℝ | rateI Fam x p.1 p.2 ≠ ⊤}

end BOLDSelect.Balance


