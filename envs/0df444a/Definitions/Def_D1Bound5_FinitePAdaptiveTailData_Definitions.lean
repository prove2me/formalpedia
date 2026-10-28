-- Prove2me | Definitions.Def_D1Bound5_FinitePAdaptiveTailData_Definitions
-- name    : D1Bound5_FinitePAdaptiveTailData_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-24T01:26:41.649197+00:00
-- url     : https://prove2.me/theorems/075349a1-d402-4e08-93e6-0c2253f946ba
-- title:
--   Finite PAdaptive Tail Data
-- statement:
--   Power of A/B retained by a combined root-column coefficient after removing its first reciprocal-anchor factor. The named objects in this bundle include `finitePAdaptiveTailExponent`, `finitePAdaptiveTailWeight`.
-- source:
--   D1Bound5/FinitePAdaptiveTailData.lean, lines 6-10, SHA-256 7413f6f034f62f29a71bf7601fa054eb71ec31e2a6c85f06e6f3607c6aab796c; D1Bound5/FinitePAdaptiveTailData.lean, lines 12-14, SHA-256 7413f6f034f62f29a71bf7601fa054eb71ec31e2a6c85f06e6f3607c6aab796c. Project: https://github.com/tomislav-math/d1-bound5-lean

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_FinitePHeight_Definitions

section
namespace D1Bound5

/-- Power of A/B retained by a combined root-column coefficient after
removing its first reciprocal-anchor factor. -/
def finitePAdaptiveTailExponent (i : Fin 4) (l j t : Fin 3) : ℕ :=
  2+(if j=0 then 0 else 4+(l : ℕ))-
    ((finitePRootTerms i l j t).2.2.1+(finitePRootTerms i l j t).2.2.2)

noncomputable def finitePAdaptiveTailWeight (i : Fin 4) (x : ℝ) : ℝ :=
  ∑ j : Fin 3, ∑ l : Fin 3, ∑ t : Fin 3,
    |((finitePRootTerms i l j t).1 : ℝ)| *x^(finitePAdaptiveTailExponent i l j t)







end D1Bound5
end


