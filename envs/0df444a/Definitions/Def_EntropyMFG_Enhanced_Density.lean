-- Prove2me | Definitions.Def_EntropyMFG_Enhanced_Density
-- name    : EntropyMFG_Enhanced_Density
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T02:22:34.791261+00:00
-- url     : https://prove2.me/theorems/b2516d19-92ca-47ca-8721-a2fe59a26784
-- title:
--   Lebesgue densities and differential entropy
-- statement:
--   A real probability density is Lebesgue integrable, nonnegative almost everywhere, and has integral one. Its law is Lebesgue measure weighted by its density. Densities are identified through their associated measures.
--
--   For an extended-real measurable function, its signed integral is defined only when its positive and negative parts are not both infinite. The relation records this integral and allows either one-sided infinity; a finite output certifies integrability. The extended logarithm at zero is minus infinity. Differential Shannon entropy is $-\int p(u)\log p(u)\,du$, with $0\log0=0$. Population cross-entropy first integrates $\log\alpha(u;y)$ against the population law and then integrates its negative against the agent's action law. This is an average of log densities, not the log of their average. The sum guard excludes opposite infinities.
--
--   These are general density and integration objects, independent of the equilibrium candidate.
-- source:
--   Guo, Xu, Zariphopoulou, Entropy Regularization for Mean Field Games with Learning, arXiv:2010.00145v2, https://arxiv.org/abs/2010.00145v2, §2, pp. 3–5, (2.1), (2.5)–(2.6)

import Mathlib

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
noncomputable section

namespace EntropyMFG.Enhanced

/-- Lebesgue probability densities, identified up to almost everywhere equality. -/
def IsDensity (p : ℝ → ℝ) : Prop :=
  Integrable p volume ∧ (∀ᵐ u ∂volume, 0 ≤ p u) ∧ ∫ u, p u = 1

def densityMeasure (p : ℝ → ℝ) : Measure ℝ :=
  volume.withDensity (fun u => ENNReal.ofReal (p u))

/-- Signed extended integral relation. The two infinite parts are never subtracted.
A finite output therefore certifies integrability, rather than a default zero. -/
def HasExtendedIntegral {E : Type*} [MeasurableSpace E]
    (μ : Measure E) (f : E → EReal) (z : EReal) : Prop :=
  AEMeasurable f μ ∧
  let p := ∫⁻ x, (f x).toENNReal ∂μ
  let n := ∫⁻ x, (-f x).toENNReal ∂μ
  (p ≠ ⊤ ∨ n ≠ ⊤) ∧ z = (p : EReal) - (n : EReal)

/-- The extended logarithm, with log zero = minus infinity. -/
def logDensity (a : ℝ) : EReal := if 0 < a then (Real.log a : EReal) else ⊥

/-- Differential Shannon entropy, with the convention 0 log 0 = 0. -/
def HasShannonEntropy (p : ℝ → ℝ) (h : EReal) : Prop :=
  HasExtendedIntegral volume (fun u => (-(p u * Real.log (p u)) : ℝ)) h

/-- Average of log densities, followed by the action integral; not log of a mixture.
Zero action mass contributes zero even when the population log is infinite. -/
def HasCrossEntropy (p : ℝ → ℝ) (α : ℝ → ℝ → ℝ) (μ : Measure ℝ)
    (h : EReal) : Prop :=
  ∃ L : ℝ → EReal,
    (∀ᵐ u ∂(densityMeasure p),
      HasExtendedIntegral μ (fun y => logDensity (α y u)) (L u)) ∧
    HasExtendedIntegral (densityMeasure p) (fun u => -L u) h

/-- Excludes the indeterminate addition of opposite infinities. -/
def DefinedSum (a b : EReal) : Prop :=
  ¬ (a = ⊤ ∧ b = ⊥) ∧ ¬ (a = ⊥ ∧ b = ⊤)

end EntropyMFG.Enhanced


