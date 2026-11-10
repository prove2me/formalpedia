-- Prove2me | Definitions.Def_IntegerSumAmplification_Main_CircuitPrediction
-- name    : IntegerSumAmplification_Main_CircuitPrediction
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T04:04:08.140024+00:00
-- url     : https://prove2.me/theorems/4ba2a452-8192-488b-a055-ace0fde88743
-- title:
--   Circuit hardness and the exact reconstruction budget
-- statement:
--   For a target $f:U\to\{0,\ldots,r-1\}$ and an input law $D$, hardness at real threshold $s$ and error $\delta$ means
--   $$\forall C\text{ with }|C|\le s,\quad\Pr_{X\sim D}[C(X)=f(X)]\le1-\delta.$$
--   The quantification includes every well-formed Boolean circuit with the required input and output widths. Output words are decoded as natural numbers, so invalid range codes fail to match the target. Gate counts are natural numbers compared with a real threshold; negative thresholds are not truncated. Plain circuits use the published zero-arity oracle convention, whose oracle instructions have no effect on the output. No depth bound is imposed. Additional Boolean cost counts precisely the non-oracle instructions of an oracle circuit.
--
--   The exact reconstruction query budget is
--   $$L(\delta,\varepsilon)=\left\lceil\frac{8}{\varepsilon^2}\ln\frac8\delta\right\rceil.$$
--   Theorems use $0<\delta,\varepsilon<1$, so its argument is positive. The logarithm is natural; binary widths use the separate integer base-two ceiling logarithm.
-- source:
--   Farhan Ali and Weiqiang Yuan, Optimal Black-Box Hardness Amplification for Integer Sums, held manuscript dated November 3, 2026 (STOC 2027 submission; acceptance not asserted); citation_basis: published. Definition 3.1, printed p. 8 / PDF p. 11; Theorem 5.1, printed p. 11 / PDF p. 14. PDF SHA256 181fd8ae5069b0c062ebccc0aa72d5a78ec0c836e6d8f6f99dd60464c0b746d7.

import Definitions.Def_LowDepthPRF_Circuit
import Definitions.Def_IntegerSumAmplification_Main_OrderStatistic
open MeasureTheory

namespace IntegerSumAmplification.Main

def booleanGates {oa ob n w : ℕ} (C : LowDepthPRF.Circuit oa ob n w) : ℕ :=
  C.gates.countP (fun g => !g.isOracle)

noncomputable def HardAt {n : ℕ} (r : ℕ) (D : Measure (Bits n))
    (f : Bits n → ℕ) (s δ : ℝ) : Prop :=
  ∀ C : LowDepthPRF.Circuit 0 0 n (wordWidth r), C.WF → (C.size : ℝ) ≤ s →
    D.real {x | decode (C.evalPlain x) = f x} ≤ 1 - δ

noncomputable def reconstructionBudget (δ ε : ℝ) : ℕ :=
  ⌈8 / ε ^ 2 * Real.log (8 / δ)⌉₊

end IntegerSumAmplification.Main


