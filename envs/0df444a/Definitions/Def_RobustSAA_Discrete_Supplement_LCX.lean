-- Prove2me | Definitions.Def_RobustSAA_Discrete_Supplement_LCX
-- name    : RobustSAA_Discrete_Supplement_LCX
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T19:38:08.892856+00:00
-- url     : https://prove2.me/theorems/78fc8836-b126-4e6d-b72b-c3d3e1682603
-- title:
--   (13)–(17), (49)–(50) — linear-convex order, the LCX statistic, its confidence region and threshold
-- statement:
--   Let $\Xi\subseteq\mathbb R^d$ be the support and let $G,G'$ be probability laws on $\Xi$. With $\|a\|_1=\sum_j|a_j|$ and the hinge $h_{a,b}(\xi)=\max\{a^\top\xi-b,0\}$:
--
--   1. **Linear-convex order** (13), p. 11: $G\preceq_{LCX}G'$ iff $\mathbb E_G[h_{a,b}(\xi)]\le\mathbb E_{G'}[h_{a,b}(\xi)]$ for all $\|a\|_1+|b|\le1$ (expectations in $[0,\infty]$).
--   2. **LCX statistic** (p. 11): for data $\xi^1,\dots,\xi^N$,
--   $$C_N(F_0)=\sup_{\|a\|_1+|b|\le1}\Big(\mathbb E_{F_0}[h_{a,b}(\xi)]-\frac1N\sum_{i=1}^N h_{a,b}(\xi^i)\Big)\in(-\infty,+\infty].$$
--   3. **Confidence region** (17), p. 12, with thresholds $Q_C=Q_{C_N}(\alpha_1)$ and $Q_R=Q_{R_N}(\alpha_2)$:
--   $$\mathcal F^{\alpha_1,\alpha_2}_{C_N,R_N}=\Big\{F_0: C_N(F_0)\le Q_C,\ \mathbb E_{F_0}[\|\xi\|_2^2]\ge\frac1N\sum_i\|\xi^i\|_2^2-Q_R\Big\},$$
--   and the data-driven set map obtained from threshold sequences $Q_C(N)$, $Q_R(N)$.
--   4. **Consistency** (Definition 2, p. 12) restricted to an admissible class of null hypotheses: for every data-generating $F$ and every admissible $F_0\ne F$, the probability of accepting $F_0$ tends to $0$.
--   5. The exponent (50), $p=\tfrac12\big(\sqrt{\log256+8\log N+(\log 2N)^2}-\log 2N\big)$, and the right-hand side of (49),
--   $$(1+B)\Big(1+\frac p{2-p}\Big)\frac{2^{1/2+1/p}}{N^{1-1/p}}\sqrt{d+1+(d+1)\log\frac N{d+1}+\log\frac4{\alpha_1}},$$
--   for a second-moment bound $B$.
--
--   **Formalization Note** Hinge and second-moment expectations are lower Lebesgue integrals in $[0,\infty]$; the statistic is extended-real valued, so a law with an infinite hinge expectation has $C_N=+\infty$. The acceptance probability in item 4 is an outer measure, so no measurability of the event is presupposed; its convergence to $0$ is equivalent to the rejection probability tending to $1$. Laws, data and the iid product measure are those of the published `RobustSAA.Convergence.Setting`.
-- source:
--   Bertsimas, Gupta, Kallus, Robust Sample Average Approximation, arXiv:1408.4445v3, (13) p. 11, statistic C_N p. 11, (17) p. 12, Definition 2 p. 12, (49)–(50) p. 34

import Mathlib
import Definitions.Def_RobustSAA_Convergence_Setting

namespace RobustSAA.Discrete.Supplement

open MeasureTheory Filter Topology RobustSAA.Convergence
open scoped BigOperators ENNReal

variable {d : ℕ} {Ξ : Set (Pt d)}

/-- `‖a‖₁ = Σⱼ |aⱼ|`. -/
noncomputable def l1norm (a : Pt d) : ℝ :=
  ∑ j, |a j|

/-- The hinge function `max{aᵀξ − b, 0}` of (13). -/
noncomputable def hinge (a : Pt d) (b : ℝ) (ξ : Pt d) : ℝ :=
  max (inner ℝ a ξ - b) 0

/-- `E_G[max{aᵀξ − b, 0}] ∈ [0, ∞]` (a lower Lebesgue integral of a nonnegative function). -/
noncomputable def hingeMean (G : ProbabilityMeasure ↥Ξ) (a : Pt d) (b : ℝ) : ℝ≥0∞ :=
  ∫⁻ ξ, ENNReal.ofReal (hinge a b (ξ : Pt d)) ∂(G : Measure ↥Ξ)

/-- `E_G[‖ξ‖₂²] ∈ [0, ∞]`. -/
noncomputable def secondMoment (G : ProbabilityMeasure ↥Ξ) : ℝ≥0∞ :=
  ∫⁻ ξ, ENNReal.ofReal (‖(ξ : Pt d)‖ ^ 2) ∂(G : Measure ↥Ξ)

/-- The linear-convex order (13), p. 11: `G ⪯_LCX G'` iff
`E_G[max{aᵀξ − b, 0}] ≤ E_{G'}[max{aᵀξ − b, 0}]` for all `‖a‖₁ + |b| ≤ 1`. -/
def LCXle (G G' : ProbabilityMeasure ↥Ξ) : Prop :=
  ∀ a : Pt d, ∀ b : ℝ, l1norm a + |b| ≤ 1 → hingeMean G a b ≤ hingeMean G' a b

/-- The LCX statistic (p. 11):
`C_N(F₀) = sup_{‖a‖₁+|b|≤1} (E_{F₀}[max{aᵀξ − b, 0}] − (1/N) Σᵢ max{aᵀξⁱ − b, 0})`,
valued in `EReal` (it is `+∞` when some hinge expectation under `F₀` is infinite). -/
noncomputable def lcxStat {N : ℕ} (F₀ : ProbabilityMeasure ↥Ξ) (s : Fin N → ↥Ξ) : EReal :=
  ⨆ a : Pt d, ⨆ b : ℝ, ⨆ (_ : l1norm a + |b| ≤ 1),
    ((hingeMean F₀ a b : ℝ≥0∞) : EReal) -
      (((1 / (N : ℝ)) * ∑ i, hinge a b ((s i : ↥Ξ) : Pt d) : ℝ) : EReal)

/-- The empirical second moment `(1/N) Σᵢ ‖ξⁱ‖₂²`. -/
noncomputable def empSecondMoment {N : ℕ} (s : Fin N → ↥Ξ) : ℝ :=
  (1 / (N : ℝ)) * ∑ i, ‖((s i : ↥Ξ) : Pt d)‖ ^ 2

/-- The confidence region (17), p. 12, of the LCX-based test with thresholds `QC = Q_{C_N}(α₁)`
and `QR = Q_{R_N}(α₂)`:
`{F₀ : C_N(F₀) ≤ QC, E_{F₀}[‖ξ‖₂²] ≥ (1/N) Σᵢ ‖ξⁱ‖₂² − QR}`. -/
noncomputable def lcxRegion {N : ℕ} (QC QR : ℝ) (s : Fin N → ↥Ξ) :
    Set (ProbabilityMeasure ↥Ξ) :=
  {F₀ | lcxStat F₀ s ≤ (QC : EReal) ∧
    ((empSecondMoment s - QR : ℝ) : EReal) ≤ ((secondMoment F₀ : ℝ≥0∞) : EReal)}

/-- The DUS map of the LCX-based test with threshold sequences `QC N`, `QR N`. -/
noncomputable def lcxDUS (QC QR : ℕ → ℝ) : DUS Ξ :=
  fun N s => lcxRegion (QC N) (QR N) s

/-- Definition 2, p. 12, restricted to the null hypotheses `F₀` satisfying `Adm F₀`: for every
data-generating `F` and every admissible `F₀ ≠ F`, the probability of accepting `F₀` tends to `0`
(equivalently, the probability of rejecting `F₀` tends to `1`; the acceptance event is measured by
the outer measure, so no measurability of the event is presupposed). -/
def IsConsistentOn (Adm : ProbabilityMeasure ↥Ξ → Prop) (𝓕 : DUS Ξ) : Prop :=
  ∀ F F₀ : ProbabilityMeasure ↥Ξ, Adm F₀ → F₀ ≠ F →
    Tendsto (fun N => dataLaw F {ω | F₀ ∈ 𝓕 N (sample ω N)}) atTop (𝓝 0)

/-- The exponent `p` of (50), p. 34:
`p = ½ (√(log 256 + 8 log N + (log 2N)²) − log 2N)`. -/
noncomputable def pExp (N : ℕ) : ℝ :=
  (1 / 2) * (Real.sqrt (Real.log 256 + 8 * Real.log N + (Real.log (2 * N)) ^ 2) -
    Real.log (2 * N))

/-- The right-hand side of (49), p. 34, with second-moment bound `B`:
`(1 + B)(1 + p/(2−p)) (2^{1/2+1/p} / N^{1−1/p}) √(d+1 + (d+1) log(N/(d+1)) + log(4/α₁))`. -/
noncomputable def lcxThreshold (d N : ℕ) (α₁ B : ℝ) : ℝ :=
  (1 + B) * (1 + pExp N / (2 - pExp N)) *
    ((2 : ℝ) ^ (1 / 2 + 1 / pExp N) / (N : ℝ) ^ (1 - 1 / pExp N)) *
    Real.sqrt ((d + 1 : ℝ) + (d + 1 : ℝ) * Real.log (N / (d + 1 : ℝ)) + Real.log (4 / α₁))

end RobustSAA.Discrete.Supplement


