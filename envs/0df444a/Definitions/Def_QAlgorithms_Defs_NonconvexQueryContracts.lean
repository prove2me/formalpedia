-- Prove2me | Definitions.Def_QAlgorithms_Defs_NonconvexQueryContracts
-- name    : QAlgorithms_Defs_NonconvexQueryContracts
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T18:39:10.758863+00:00
-- url     : https://prove2.me/theorems/79eb704a-21a3-450a-a55c-d1f41cf6f838
-- title:
--   NonconvexQueryContracts
-- statement:
--   NonconvexQueryContracts
-- source:
--   Source references and exact conventions are recorded in each declaration docstring. algorithms\QAlgorithms\Defs\NonconvexQueryContracts.lean

import Definitions.Def_QAlgorithms_Defs_IdealRealEvaluation
noncomputable section

open scoped Matrix ComplexConjugate ENNReal ComplexOrder

attribute [local instance] Classical.propDecidable

open MeasureTheory
open scoped ENNReal
namespace QAlgorithms.Nonconvex

/-- A bound with displayed scale Delta*log^2(n)*epsilon^(-7/4), tilde-O interpreted
by the p.1 footnote. Fix suppressed smoothness and confidence parameters first.
The positive constant, logarithmic polynomial degree and threshold precede every
n,epsilon,gap,f,U_f, and in particular are uniform over the displayed gap Delta.
Theorem 4 Eq.(67) counts iterations as 3*max(Delta/F',Delta*blockDuration/E);
Eqs.(71)-(73) retain Delta in both query contributions and their total. Gap enters
simulation-time logarithms through delta0 in Eqs.(62)-(63), not an arbitrary
multiplicative constant. Remark 3 extends gradient replacement without fixing Delta.
Audit correction: the inventory's fixed-gap-constants wording is not supported by
these formulas; allowing C or the threshold to depend on gap could erase the displayed
gap dependence. The original uniform-gap signature and quantifier order are retained.
Inputs must tie gap to the objective's actual initialGap, and law to program execution;
this contract alone asserts neither algorithm existence nor a favorable output law.
Positive-gap and asymptotic guards exclude zero scales and log(1); the headline handles
zero gap separately. No gate-time conclusion.
Source: arxiv-2007.10253v3 PDF p.1 footnote 1, pp.18-19 Theorem 4 Eqs.(62)-(73),
p.20 Remark 2, and p.24 Remark 3 and the asserted implication of Theorem 1. -/
def SoftEvaluationQueryContract {Input : ℕ → ℝ → ℝ → Type*}
    (law : (n : ℕ) → (eps gap : ℝ) → Input n eps gap → Measure (Vector n × ℕ))
    (success : (n : ℕ) → (eps gap : ℝ) → Input n eps gap → Vector n → Prop)
    (delta : ℝ) (_hd : 0 < delta ∧ delta < 1) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ degree : ℕ, ∃ threshold : ℝ, 1 ≤ threshold ∧
    ∀ (n : ℕ) (eps gap : ℝ), 2 ≤ n → 0 < eps → 0 < gap →
    let scale := gap*Real.log n^2*eps^(-(7/4 : ℝ))
    threshold ≤ scale → ∀ input : Input n eps gap,
      law n eps gap input {xq | success n eps gap input xq.1 ∧
        (xq.2 : ℝ) ≤ C*scale*max 1 (Real.log scale)^degree} ≥ ENNReal.ofReal (1-delta)

example {d : ℕ} : (0 : Measure (Vector d × ℕ)) Set.univ = 0 := by simp

end QAlgorithms.Nonconvex


