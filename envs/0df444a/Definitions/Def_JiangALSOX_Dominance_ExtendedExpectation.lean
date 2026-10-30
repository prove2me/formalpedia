-- Prove2me | Definitions.Def_JiangALSOX_Dominance_ExtendedExpectation
-- name    : JiangALSOX_Dominance_ExtendedExpectation
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T01:04:48.192696+00:00
-- url     : https://prove2.me/theorems/d6740fff-8539-4577-ad05-72fc9e75cb78
-- title:
--   Extended expectations with explicit signed definedness
-- statement:
--   For a measure $P$ and a measurable real function $f$, put
--   $$E^+_P(f)=\int \max(f,0)\,dP\in[0,+\infty].$$
--   The signed extended expectation is defined exactly when at least one of $E^+_P(f)$ and $E^+_P(-f)$ is finite; its value is their difference. It is marked undefined if both parts are infinite, or if the function is not measurable. No integrability is imposed on a nonnegative function. An infinite nonnegative expectation is $+\infty$, never zero.
--
--   **Formalization Note.** The nonnegative integral is Mathlib's Lebesgue integral in $\mathbb R_{\ge0}\cup\{+\infty\}$. A defined signed expectation is `some` of an `EReal` value and an undefined expression is `none`. The positive-part helper is used only with measurable arguments in the optimization models and certificates. This generic expectation layer is independent of the paper's model.
-- source:
--   Nan Jiang and Weijun Xie, ALSO-X and ALSO-X+: Better Convex Approximations for Chance Constrained Programs, arXiv:2012.04763v4 (14 October 2021), https://arxiv.org/abs/2012.04763v4, pp. 6–7, 12–13, 42, expectations in (7), (13), (KKT1) and (KKT2)

import Mathlib

open MeasureTheory
open scoped ENNReal

namespace JiangALSOX.Dominance

noncomputable def positiveExpectation {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (f : Ω → ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, ENNReal.ofReal (f ω) ∂P

noncomputable def signedExpectation {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (f : Ω → ℝ) : Option EReal := by
  classical
  exact if Measurable f ∧
      (positiveExpectation P f ≠ ⊤ ∨ positiveExpectation P (fun ω => -f ω) ≠ ⊤)
    then some ((positiveExpectation P f).toEReal -
      (positiveExpectation P (fun ω => -f ω)).toEReal)
    else none

end JiangALSOX.Dominance


