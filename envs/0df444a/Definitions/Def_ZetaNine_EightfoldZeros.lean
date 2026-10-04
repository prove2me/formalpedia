-- Prove2me | Definitions.Def_ZetaNine_EightfoldZeros
-- name    : ZetaNine_EightfoldZeros
-- status  : Definition
-- author  : @Yuxuan Xu
-- created : 2026-10-02T14:08:39.746326+00:00
-- url     : https://prove2.me/theorems/a57d441d-db5c-46db-b2f7-c52197d21c72
-- title:
--   Eightfold-zero repaired rational function
-- statement:
--   For $n\ge0$, define the exact repaired rational function
--
--   $$R_n^*(t)=\frac{(4n)!^2}{n!^8}\frac{\prod_{j=1}^n(t-j)^8}{\prod_{j=0}^{4n}(t+j)^2}.$$
--
--   The definition file contains the scalar prefactor, numerator and denominator polynomials, and their quotient as a real function. The endpoint-zero and derivative theorems are separate proofs. No convergence, sign, asymptotic, content or irrationality assertion is embedded in the definition.
-- source:
--   https://github.com/Anchen0823/zeta9-research-notes/releases/tag/research-2026-10-02; research/new-linear-form-route-repair-2026-10-02.md, opening unnumbered definition of R*_n and the following endpoint-zero paragraph.

import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Analysis.Calculus.ContDiff.Polynomial
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.NormNum

set_option autoImplicit false

/-!
The explicit eightfold-zero repair from `new-linear-form-route-repair-2026-10-02.md`.
The numerator has an eighth-power factor at each positive endpoint `1,...,n`.
Its derivatives through order seven vanish there, as do the genuine iterated
real derivatives of the rational function, whose denominator is nonzero there.
This file makes no sign, nonvanishing, asymptotic or irrationality claim.
-/

noncomputable section

open Polynomial
open scoped BigOperators

namespace ZetaNine.EightfoldZeros

/-! ## Construction definitions (the lightweight Definitions layer) -/

/-- The exact scalar prefactor of the repair candidate. -/
def repairScale (n : ℕ) : ℝ :=
  ((Nat.factorial (4 * n) : ℝ) ^ 2) / ((Nat.factorial n : ℝ) ^ 8)

/-- The explicit repair numerator, with one eighth-power factor per endpoint. -/
def repairNumerator (n : ℕ) : ℝ[X] :=
  C (repairScale n) * ∏ j ∈ Finset.range n, (X - C ((j + 1 : ℕ) : ℝ)) ^ 8

/-- Its denominator is exactly `[t(t+1)...(t+4n)]²`. -/
def repairDenominator (n : ℕ) : ℝ[X] :=
  ∏ j ∈ Finset.range (4 * n + 1), (X + C (j : ℝ)) ^ 2

/-- The real rational function `R*_n` in the repair note. -/
def repairFunction (n : ℕ) (t : ℝ) : ℝ :=
  (repairNumerator n).eval t / (repairDenominator n).eval t


end ZetaNine.EightfoldZeros


