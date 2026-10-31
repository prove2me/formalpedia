-- Prove2me | Definitions.Def_FrechetPrefs_Wasserstein
-- name    : FrechetPrefs_Wasserstein
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:02:31.759497+00:00
-- url     : https://prove2.me/theorems/385b2117-ff31-41ac-bd7f-2c5c76b095d7
-- title:
--   Quantile function, $P_2(\mathbb R)$, the distance $W_2$, the Fréchet function and the barycenter
-- statement:
--   Let $Q$ be a probability measure on $\mathbb R$ with distribution function $F(x)=Q((-\infty,x])$. Its **quantile function** is
--   $$F^{-1}(s)=\inf\{x : s\le F(x)\},\qquad s\in(0,1).$$
--
--   $P_2(\mathbb R)$ is the set of probability measures on $\mathbb R$ with finite second moment. For two such measures the **2-Wasserstein distance** is given by the quantile formula
--   $$d(Q_1,Q_2):=\Big(\int_0^1\big(F_1^{-1}(s)-F_2^{-1}(s)\big)^2\,ds\Big)^{1/2}.$$
--
--   Given models $Q_1,\dots,Q_n$ and weights $w$ in the simplex $\Delta^{n-1}$, the **Fréchet function** is
--   $$F_{\mathbb M}(Q)=\sum_{i=1}^n w_i\,d^2(Q,Q_i),$$
--   and a **barycenter** $Q_B$ is a measure in $P_2(\mathbb R)$ at which $F_{\mathbb M}$ attains its minimum over $P_2(\mathbb R)$.
--
--   These objects are general facts of one-dimensional optimal transport and carry no decision-theoretic content. Every statement of the mission is built on them.
--
--   **Formalization Note** The quantile is the published `RiskFunctionals.StochDominance.quantileFunction`. The distance is the paper's eq. (1), with no coupling infimum. The integrals are over the open interval, and the distance is only used on $P_2(\mathbb R)$, where they are finite. That the barycenter is the quantile average is a theorem of the mission, not the definition.
-- source:
--   Petracou, Xepapadeas, Yannacopoulos, Decision Making under Model Uncertainty: Fréchet-Wasserstein Mean Preferences, manuscript MS-DEC-19-01009-REV (accepted manuscript, hdl.handle.net/11585/863779), §2.2, pp.5–6, Fréchet function and barycenter p.5, eq. (1) p.6; P₂(ℝ) p.ec6

import Mathlib
import Definitions.Def_RiskFunctionals_StochDominance_QuantileFunction

open MeasureTheory Set

namespace FrechetPrefs

/-- The quantile function `F⁻¹` of a probability measure on `ℝ`, `F⁻¹(s) = inf {x : s ≤ Q((−∞, x])}`.
Petracou–Xepapadeas–Yannacopoulos, Decision Making under Model Uncertainty, manuscript
MS-DEC-19-01009-REV, §2.2, p.5.

**Formalization Note.** This is the published `RiskFunctionals.StochDominance.quantileFunction`, the
left-continuous inverse. It is evaluated on `s ∈ (0,1)` only, where the infimum is of a nonempty
set bounded below. The page's `[0,1]` differs by two points, where the quantile can be infinite. -/
noncomputable def q (μ : ProbabilityMeasure ℝ) (s : ℝ) : ℝ :=
  RiskFunctionals.StochDominance.quantileFunction (μ : Measure ℝ) s

/-- `P₂(ℝ)`: the probability measures on `ℝ` with finite second moment. Manuscript
MS-DEC-19-01009-REV, p.ec6 ("Q ∈ P₂(R)"). This is the domain on which the distance of eq. (1) is
finite. -/
def P2 : Set (ProbabilityMeasure ℝ) :=
  {μ | Integrable (fun x : ℝ => x ^ 2) (μ : Measure ℝ)}

/-- The 2-Wasserstein distance on the line, by its quantile formula, eq. (1), p.6 of manuscript
MS-DEC-19-01009-REV: `d(Q₁,Q₂) := (∫₀¹ (F₁⁻¹(s) − F₂⁻¹(s))² ds)^{1/2}`.

**Formalization Note.** Eq. (1) is the paper's own `:=`, so no coupling infimum appears. The integral
is over the open interval, which has the same value. On measures outside `P2` the integrand can fail
to be integrable and the Bochner integral is `0`; every statement of this mission takes its measures
in `P2`. -/
noncomputable def W2 (μ ν : ProbabilityMeasure ℝ) : ℝ :=
  Real.sqrt (∫ s in Ioo (0 : ℝ) 1, (q μ s - q ν s) ^ 2)

/-- The Fréchet function `F_M(Q) = ∑ᵢ wᵢ d²(Q, Qᵢ)`, §2.2, p.5 of manuscript MS-DEC-19-01009-REV,
with `d = W₂`. The weights `w` are taken in the simplex by each statement that uses this. -/
noncomputable def frechet {n : ℕ} (w : Fin n → ℝ) (Q : Fin n → ProbabilityMeasure ℝ)
    (μ : ProbabilityMeasure ℝ) : ℝ :=
  ∑ i, w i * (W2 μ (Q i)) ^ 2

/-- The barycenter (Fréchet mean) `Q_B` of the models `Qᵢ` with weights `w`: "the probability model
which provides the minimum of the Fréchet function", §2.2, p.5 of manuscript MS-DEC-19-01009-REV.

**Formalization Note.** The minimum is over `P2`, the domain of the distance. That the barycenter
is the weighted quantile average is the theorem `barycenter_quantile_average`, not this
definition. -/
def IsBarycenter {n : ℕ} (w : Fin n → ℝ) (Q : Fin n → ProbabilityMeasure ℝ)
    (B : ProbabilityMeasure ℝ) : Prop :=
  B ∈ P2 ∧ ∀ ν ∈ P2, frechet w Q B ≤ frechet w Q ν

end FrechetPrefs


