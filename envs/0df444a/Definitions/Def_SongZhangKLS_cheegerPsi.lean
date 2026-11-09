-- Prove2me | Definitions.Def_SongZhangKLS_cheegerPsi
-- name    : SongZhangKLS_cheegerPsi
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T23:06:07.937219+00:00
-- url     : https://prove2.me/theorems/1d17b633-8184-4a95-b861-bd4ab9840d71
-- title:
--   Outer boundary measure $\mu^+$, reciprocal Cheeger constant $\psi_\mu$ and $\psi_n$
-- statement:
--   Let $\mu$ be a measure on $\mathbb R^n$ and $B_2^n=\{x\in\mathbb R^n:\|x\|\le1\}$.
--
--   1. The **outer boundary measure** of a Borel set $A\subseteq\mathbb R^n$ is
--   $$\mu^+(A)=\liminf_{\varepsilon\to0^+}\frac{\mu(A+\varepsilon B_2^n)-\mu(A)}{\varepsilon},$$
--   where $A+\varepsilon B_2^n$ is the Minkowski sum.
--   2. The **reciprocal Cheeger constant** of $\mu$ is
--   $$\psi_\mu=\sup_{\substack{A\subseteq\mathbb R^n\text{ Borel}\\0<\mu(A)<1}}\frac{\min\{\mu(A),1-\mu(A)\}}{\mu^+(A)}.$$
--   3. $\psi_n$ is the supremum of $\psi_\mu$ over all isotropic log-concave probability measures $\mu$ on $\mathbb R^n$.
--
--   The KLS conjecture asserts that $\psi_n\le C$ for a universal constant $C$; small $\psi_\mu$ means that every set of moderate measure has a large boundary.
--
--   **Formalization Note** All values lie in $[0,\infty]$: a ratio with $\mu^+(A)=0$ is $+\infty$, an empty supremum is $0$. The limit inferior is one-sided ($\varepsilon>0$), since the quotient divides by $\varepsilon$ and $A+\varepsilon B_2^n$ does not depend on its sign; the measure of the possibly non-Borel set $A+\varepsilon B_2^n$ is its outer measure. Log-concavity and isotropy are the published `FunctionalInequalities.KLS.LogConcave` (compact sets, $0<t<1$) and `FunctionalInequalities.KLS.Isotropic` (finite second moment, mean zero, identity covariance).
-- source:
--   Z. Song, X. Zhang, An O(1) Bound for the KLS Constant, arXiv:2610.01447 (preprint; version of October 2026, sha256 c7d2264f…8a6c), §1, p.2 (definitions of $\mu^+$, $\psi_\mu$, $\psi_n$)

import Mathlib
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_LogConcave
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_Isotropic

open MeasureTheory Filter Topology
open scoped ENNReal Pointwise

noncomputable section

namespace SongZhangKLS

/-- The **outer boundary measure** `µ⁺(A) = liminf_{ε→0} (µ(A + εB₂ⁿ) − µ(A))/ε`, with
`B₂ⁿ = {x : ‖x‖ ≤ 1}` (Song, Zhang, *An O(1) Bound for the KLS Constant*, arXiv:2610.01447,
version of October 2026, sha256 c7d2264f…8a6c, §1, p.2).

**Formalization Note.** The limit inferior is taken as `ε → 0⁺` (the filter `𝓝[>] 0`): the
quotient divides by `ε` and `A + εB₂ⁿ` is the same set for `±ε`, so only positive `ε` is meaningful.
`A + ε • closedBall 0 1` is the Minkowski sum (not a thickening). The quotient is computed in
`ℝ≥0∞`; the truncated subtraction is exact because `A ⊆ A + εB₂ⁿ`. The measure of the possibly
non-Borel set `A + εB₂ⁿ` is its outer measure. -/
def outerBoundary {n : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin n)))
    (A : Set (EuclideanSpace ℝ (Fin n))) : ℝ≥0∞ :=
  liminf (fun ε : ℝ =>
      (μ (A + ε • Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) - μ A) / ENNReal.ofReal ε)
    (𝓝[>] 0)

/-- The **reciprocal Cheeger constant**
`ψ_µ = sup_{A Borel, 0 < µ(A) < 1} min{µ(A), 1 − µ(A)} / µ⁺(A)` (Song, Zhang, arXiv:2610.01447,
version of October 2026, sha256 c7d2264f…8a6c, §1, p.2).

**Formalization Note.** Computed in `ℝ≥0∞`: a ratio with `µ⁺(A) = 0` is `⊤` (the paper's infinite
ratio), and the supremum of an empty family (no Borel `A` with `0 < µ(A) < 1`) is `0`. Borel sets are
the measurable sets of the Borel σ-algebra of `EuclideanSpace ℝ (Fin n)`. -/
def cheegerPsi {n : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin n))) : ℝ≥0∞ :=
  ⨆ (A : Set (EuclideanSpace ℝ (Fin n))) (_ : MeasurableSet A ∧ 0 < μ A ∧ μ A < 1),
    min (μ A) (1 - μ A) / outerBoundary μ A

/-- `ψ_n`, the supremum of `ψ_µ` over all isotropic log-concave probability measures `µ` on `ℝⁿ`
(Song, Zhang, arXiv:2610.01447, version of October 2026, sha256 c7d2264f…8a6c, §1, p.2).

**Formalization Note.** Log-concavity and isotropy are the published
`FunctionalInequalities.KLS.LogConcave` (compact sets, `0 < t < 1`) and
`FunctionalInequalities.KLS.Isotropic` (finite second moment, mean `0`, covariance operator the
identity). The supremum is in `ℝ≥0∞`. -/
def psiN (n : ℕ) : ℝ≥0∞ :=
  ⨆ (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
    (_ : FunctionalInequalities.KLS.LogConcave μ ∧ FunctionalInequalities.KLS.Isotropic μ),
    cheegerPsi (μ : Measure (EuclideanSpace ℝ (Fin n)))

end SongZhangKLS


