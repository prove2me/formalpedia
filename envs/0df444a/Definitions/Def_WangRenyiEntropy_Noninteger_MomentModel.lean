-- Prove2me | Definitions.Def_WangRenyiEntropy_Noninteger_MomentModel
-- name    : WangRenyiEntropy_Noninteger_MomentModel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:46:40.861328+00:00
-- url     : https://prove2.me/theorems/35816415-bc72-4b60-9761-b1231a46d842
-- title:
--   Bounded mixing laws, matching moments, and Poisson mixture distance
-- statement:
--   For a real $M$, a bounded law $\nu$ is an arbitrary Borel probability measure assigning mass one to $[0,M]$. Its real moment is
--   $$\mu_\nu^{(q)}=\int x^q\,d\nu(x).$$
--   Two laws match $K$ moments when these integrals agree for every integer order $1\le j\le K$; their zeroth moments already equal one. The Poisson mixture has masses
--   $$m_\nu(j)=\mathbb E_{U\sim\nu}[e^{-U}U^j/j!],\qquad j\in\mathbb N,$$
--   and the distance between two such mixtures is $\frac12\sum_{j\ge0}|m_{\nu_0}(j)-m_{\nu_1}(j)|$.
--
--   The model retains arbitrary real mixing distributions and the entire countable Poisson alphabet. Extended nonnegative sums avoid a non-summable real-series default; positive moments of compactly supported laws are finite. The nonnegative-rate conversion agrees with the rate everywhere on the support.
-- source:
--   Qisheng Wang, STOC 2027 submission #447 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/447.pdf, printed 6,7 / PDF 8, 9, Lemmas 2.3 and 3.1

import Mathlib

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
noncomputable section

namespace WangRenyiEntropy.Noninteger

/-- Arbitrary real-valued mixing laws, with no finite-support or density condition. -/
structure BoundedLaw (M : ℝ) where
  law : ProbabilityMeasure ℝ
  supported : (law : Measure ℝ) (Set.Icc 0 M) = 1

/-- Real moments on a compact nonnegative interval. Only positive orders are used. -/
def moment {M : ℝ} (ν : BoundedLaw M) (q : ℝ) : ℝ :=
  ∫ x, Real.rpow x q ∂(ν.law : Measure ℝ)

/-- Matching integer moments 1 through K; the zeroth moment is already one. -/
def MomentMatching {M : ℝ} (K : ℕ) (ν₀ ν₁ : BoundedLaw M) : Prop :=
  ∀ j : ℕ, 1 ≤ j → j ≤ K → moment ν₀ j = moment ν₁ j

/-- The actual Poisson-mixture mass, E[exp(-U) U^j / j!]. -/
def mixtureMass {M : ℝ} (ν : BoundedLaw M) (j : ℕ) : ℝ≥0∞ :=
  ∫⁻ x, (poissonMeasure (Real.toNNReal x)) {j} ∂(ν.law : Measure ℝ)

/-- Half the l1 distance; nonnegative extended sums cannot hide divergence. -/
def mixtureTV {M : ℝ} (ν₀ ν₁ : BoundedLaw M) : ℝ≥0∞ :=
  (1 / 2 : ℝ≥0∞) * ∑' j : ℕ,
    ENNReal.ofReal |(mixtureMass ν₀ j).toReal - (mixtureMass ν₁ j).toReal|

end WangRenyiEntropy.Noninteger


