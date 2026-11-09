-- Prove2me | Definitions.Def_HindsightGain_Uniform_rademacher
-- name    : HindsightGain_Uniform_rademacher
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:49:48.152961+00:00
-- url     : https://prove2.me/theorems/e3024fde-02bc-4584-b0dd-6129c54ff274
-- title:
--   Countable random-sign series and extended expected suprema
-- statement:
--   Let $\ell_2$ be the real square-summable sequences. For a finite or countable coordinate set $J$, the sign law is the product of fair Boolean laws, interpreted as signs in $\{-1,1\}$. For $a\in\ell_2$ the random-sign series is
--   $$X_a(\epsilon)=\lim_{N\to\infty}\sum_{k<N}\epsilon_k a_k.$$
--   The definition uses this ordered partial-sum limit, with value zero only where it does not exist. Under independent fair signs this exceptional event is null; for a countable class one common event supports all these limits.
--   For an extended-real process $X$, its signed extended expectation is
--   $$\mathbb E X=\int X^+\,dP-\int X^-\,dP.$$
--   Scalar and vector complexities take the extended supremum over a class $S$ of $\sum_i\epsilon_i\psi_i(s)$ and $\sum_iX_{\phi_i(s)}(\epsilon_{i,\cdot})$, respectively. For nonempty countable $S$ each supremum is bounded below by a fixed mean-zero integrable process, so its negative part is integrable and its expectation can be $+\infty$. For $S=\varnothing$ both are $-\infty$. No boundedness, uniform square-norm bound or integrability of the suprema is imposed. These are the processes used by Theorem 7; no unconditional summation or real integral of an unbounded supremum is substituted.
-- source:
--   Xiaohui Bei, Wenhao Wu, The Optimizer's Windfall: Bounding Hindsight Gain under Random Restrictions, STOC 2027 submission #464 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/464.pdf, §3.3, Theorem 7, p.16; its cited [Mau16] random-sign ℓ₂ process convention

import Mathlib

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped BigOperators ENNReal Topology

namespace HindsightGain.Uniform

/-- The square-summable real sequences, with their Hilbert norm. -/
abbrev SequenceL2 := lp (fun _ : ℕ => ℝ) 2

/-- Canonical independent fair signs, for either finite or countable index sets. -/
def signLaw (J : Type) [Countable J] : Measure (J → Bool) :=
  Measure.infinitePi (fun _ : J => (PMF.uniformOfFintype Bool).toMeasure)

def sign (b : Bool) : ℝ := if b then 1 else -1

/-- The ordered random-sign series: its partial-sum limit when it exists, 0 otherwise.
For square-summable coefficients under signLaw, the exceptional event is null. -/
def signSeries (a : SequenceL2) (ε : ℕ → Bool) : ℝ := by
  classical
  exact if h : ∃ l : ℝ, Tendsto (fun N : ℕ => ∑ k ∈ Finset.range N, sign (ε k) * a k) atTop (𝓝 l)
  then Classical.choose h else 0

/-- Signed extended expectation via its two nonnegative integrals. In the processes below,
nonempty countable classes have integrable negative part; empty classes have expectation -∞. -/
def extendedMean {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (X : Ω → EReal) : EReal :=
  ((∫⁻ ω, (X ω).toENNReal ∂μ : ℝ≥0∞) : EReal) -
    ((∫⁻ ω, (-X ω).toENNReal ∂μ : ℝ≥0∞) : EReal)

def scalarComplexity {S : Type} (n : ℕ) (ψ : Fin n → S → ℝ) : EReal :=
  extendedMean (signLaw (Fin n)) (fun ε => ⨆ s : S, ((∑ i, sign (ε i) * ψ i s : ℝ) : EReal))

def vectorComplexity {S : Type} (n : ℕ) (φ : Fin n → S → SequenceL2) : EReal :=
  extendedMean (signLaw (Fin n × ℕ))
    (fun ε => ⨆ s : S, ((∑ i, signSeries (φ i s) (fun k => ε (i, k)) : ℝ) : EReal))

end HindsightGain.Uniform


