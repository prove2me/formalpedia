-- Prove2me | Definitions.Def_MoneyBurningTrade_IndependentSurplus_Supplement_JointObjectives
-- name    : MoneyBurningTrade_IndependentSurplus_Supplement_JointObjectives
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T17:35:41.987653+00:00
-- url     : https://prove2.me/theorems/bd86ca07-f934-4389-acfb-936b7af05abb
-- title:
--   Section 3.3 — social welfare, traders’ utility and first-best welfare for joint laws
-- statement:
--   For a mechanism $M=(x,p_B,p_S)$ and a valuation profile $p=(v_s,v_b)$ (seller's value first), equations (12) and (14) of §3.3 define the **social welfare** and the **traders' utility**
--
--   $$\mathrm{SW}_M(v_s,v_b)=v_b\,x(v_s,v_b)+v_s\,\bigl(1-x(v_s,v_b)\bigr),$$
--
--   $$\mathrm{TU}_M(v_s,v_b)=\bigl(v_b\,x-p_B\bigr)+\bigl(p_S+v_s(1-x)\bigr)=\mathrm{SW}_M(v_s,v_b)-\bigl(p_B-p_S\bigr)(v_s,v_b).$$
--
--   Social welfare counts the money burnt by the mechanism; traders' utility counts only the two traders. For a joint law $F$ of $(v_s,v_b)$ on $\mathbb R^2$, which may be correlated,
--
--   $$\mathrm{SW}_M(F)=\mathbb E_F[\mathrm{SW}_M(v_s,v_b)],\qquad \mathrm{TU}_M(F)=\mathbb E_F[\mathrm{TU}_M(v_s,v_b)],\qquad \mathrm{SW}_{\mathrm{OPT}}(F)=\mathbb E_F[\max\{v_s,v_b\}].$$
--
--   By the paper's own definition the first best burns no money, so $\mathrm{TU}_{\mathrm{OPT}}(F)=\mathrm{SW}_{\mathrm{OPT}}(F)$. Finally, *finite joint objectives* of $M$ under $F$ means that the payments, both traders' surpluses, the traders' surplus, the gains from trade (the published `FiniteObjectives`), the welfare and the traders' utility are all $F$-integrable.
--
--   These objects complete the published objective layer (which has the traders' surplus and gains-from-trade integrands) for the correlated-value results of §4.3 and §5.2.
--
--   **Formalization Note** Expectations are Bochner integrals, which are $0$ for a non-integrable integrand; every theorem therefore states finiteness of the objectives as a conclusion, never as a restriction on the mechanisms.
-- source:
--   Moshe Babaioff, Noam Nisan, Ariel Shaulker, STOC 2027 submission #303 (October 2026), §3.3, equations (12), (14) and the first-best benchmarks, printed p. 16–17 (PDF p. 17–18); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/303.pdf

import Mathlib
import Definitions.Def_MoneyBurningTrade_IndependentSurplus_Objectives

open MeasureTheory

set_option autoImplicit false

namespace MoneyBurningTrade.IndependentSurplus.Supplement

/-- Equation (12), §3.3 p.17: social welfare at the profile `p = (s, b)`,
the value of whoever holds the item at the end, `b·x + s·(1 − x)`.
Burnt money is counted (it is the mechanism's own utility). -/
def welfarePoint (M : SecondBestBT.Mechanism) (p : ℝ × ℝ) : ℝ :=
  p.2 * M.x p + p.1 * (1 - M.x p)

/-- Equation (14), §3.3 p.17: traders' utility `u_b + u_s` at the profile `p = (s, b)`,
with `u_b = b·x − p_B` and `u_s = p_S + s·(1 − x)`; burnt money is not counted. -/
def tradersUtilityPoint (M : SecondBestBT.Mechanism) (p : ℝ × ℝ) : ℝ :=
  (p.2 * M.x p - M.pB p) + (M.pS p + p.1 * (1 - M.x p))

/-- `SW_M(F)`, §3.3 p.17, for a general (possibly correlated) joint law `μ`. -/
noncomputable def SW (μ : Measure (ℝ × ℝ)) (M : SecondBestBT.Mechanism) : ℝ :=
  ∫ p, welfarePoint M p ∂μ

/-- `TU_M(F)`, §3.3 p.17, for a general (possibly correlated) joint law `μ`. -/
noncomputable def TU (μ : Measure (ℝ × ℝ)) (M : SecondBestBT.Mechanism) : ℝ :=
  ∫ p, tradersUtilityPoint M p ∂μ

/-- First-best social welfare `SW_OPT(F) = E[max{v_s, v_b}]`, §3.3 p.17, for a joint law.
By the paper's definition `TU_OPT(F) = SW_OPT(F)` (the first best burns no money). -/
noncomputable def firstBestSW (μ : Measure (ℝ × ℝ)) : ℝ :=
  ∫ p, max p.1 p.2 ∂μ

/-- Integrability of every objective of `M` under `μ`: the base `FiniteObjectives`
together with the welfare and traders'-utility integrands. Used only as a theorem
conclusion, so that no Bochner integral silently takes its default value 0. -/
def FiniteJointObjectives (μ : Measure (ℝ × ℝ)) (M : SecondBestBT.Mechanism) : Prop :=
  FiniteObjectives μ M ∧ Integrable (welfarePoint M) μ ∧
  Integrable (tradersUtilityPoint M) μ

end MoneyBurningTrade.IndependentSurplus.Supplement


