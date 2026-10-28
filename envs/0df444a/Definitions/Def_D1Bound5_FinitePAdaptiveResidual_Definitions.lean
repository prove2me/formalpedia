-- Prove2me | Definitions.Def_D1Bound5_FinitePAdaptiveResidual_Definitions
-- name    : D1Bound5_FinitePAdaptiveResidual_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-23T22:24:11.069409+00:00
-- url     : https://prove2.me/theorems/1f388e10-e45e-424a-9726-686e6b2642f5
-- title:
--   Finite PAdaptive Residual
-- statement:
--   Manuscript R(q) is this positive polynomial evaluated at 1/q. The named objects in this bundle include `finitePAdaptiveRate`.
-- source:
--   D1Bound5/FinitePAdaptiveResidual.lean, lines 6-9, SHA-256 25fa69daa14e28209c09660c5858b952ff9e39422be6b297ad69d024782cb11b. Project: https://github.com/tomislav-math/d1-bound5-lean

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
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

section
namespace D1Bound5

/-- Manuscript R(q) is this positive polynomial evaluated at 1/q. -/
noncomputable def finitePAdaptiveRate (x : ℝ) : ℝ :=
  (15+80*x+150*x^2+280*x^3+35*x^4)/256+
    (21/(1024*999) : ℝ)*(885+1144*x+435*x^2+2634*x^3+170*x^4)













end D1Bound5
end


