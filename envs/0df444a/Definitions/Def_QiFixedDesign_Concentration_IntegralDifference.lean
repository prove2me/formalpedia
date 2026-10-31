-- Prove2me | Definitions.Def_QiFixedDesign_Concentration_IntegralDifference
-- name    : QiFixedDesign_Concentration_IntegralDifference
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T14:59:09.642785+00:00
-- url     : https://prove2.me/theorems/8d3876a3-43d1-4bca-81fc-a21159dbeab4
-- title:
--   Definedness of signed integral differences
-- statement:
--   For a real measurable function $f$, write $I^+(\mu,f)=\int\max(f,0)\,d\mu$ and $I^-(\mu,f)=\int\max(-f,0)\,d\mu$ as nonnegative extended integrals. Its signed integral is defined when at least one of these is finite, and then equals $I^+-I^-$. A difference $\int f\,d\mu-\int f\,d\nu$ is defined when both signed integrals are defined and they are not both $+\infty$ or both $-\infty$. The extended-real expression is used only together with this definedness assertion. This makes the missing-definedness issue in the unrestricted printed duality lemma visible instead of silently replacing a nonintegrable integral by zero.
-- source:
--   Qi, Cao and Shen (2021), Distributionally Robust Conditional Quantile Prediction with Fixed Design, DOI 10.1287/mnsc.2020.3903, supplied source.pdf, semantics of (16), Lemma 1, PDF/printed p. 12

import Mathlib

open MeasureTheory Matrix Filter Topology
open scoped ENNReal

namespace QiFixedDesign.Concentration

noncomputable def positiveIntegral {Ξ : Type*} [MeasurableSpace Ξ]
    (μ : Measure Ξ) (f : Ξ → ℝ) : ℝ≥0∞ := ∫⁻ z, ENNReal.ofReal (f z) ∂μ

def SignedIntegralDefined {Ξ : Type*} [MeasurableSpace Ξ]
    (μ : Measure Ξ) (f : Ξ → ℝ) : Prop :=
  positiveIntegral μ f < ⊤ ∨ positiveIntegral μ (fun z => -f z) < ⊤

noncomputable def signedIntegral {Ξ : Type*} [MeasurableSpace Ξ]
    (μ : Measure Ξ) (f : Ξ → ℝ) : EReal :=
  (positiveIntegral μ f : EReal) - (positiveIntegral μ (fun z => -f z) : EReal)

def IntegralDifferenceDefined {Ξ : Type*} [MeasurableSpace Ξ]
    (μ ν : Measure Ξ) (f : Ξ → ℝ) : Prop :=
  SignedIntegralDefined μ f ∧ SignedIntegralDefined ν f ∧
  ¬ (signedIntegral μ f = ⊤ ∧ signedIntegral ν f = ⊤) ∧
  ¬ (signedIntegral μ f = ⊥ ∧ signedIntegral ν f = ⊥)

end QiFixedDesign.Concentration


