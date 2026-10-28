-- Prove2me | Definitions.Def_D1Bound5_FinitePAdaptiveLeading_Definitions
-- name    : D1Bound5_FinitePAdaptiveLeading_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-23T22:24:53.212525+00:00
-- url     : https://prove2.me/theorems/632a41d0-86ca-421b-86d6-8820d53e7a06
-- title:
--   Finite PAdaptive Leading
-- statement:
--   The six remaining terms of H after its pure reciprocal squares cancel. The named objects in this bundle include `finitePAdaptiveLeadingTerms`, `finitePLeadingNumeratorExponent`, `finitePLeadingRatioExponent`, `finitePAdaptiveLeadingTermValue`, `finitePLeadingWeight`.
-- source:
--   D1Bound5/FinitePAdaptiveLeading.lean, lines 6-12, SHA-256 eb474c59b02738fa364b083f7c3f854ab6e1f57dae76acf74969fb1b0dcbbac0; D1Bound5/FinitePAdaptiveLeading.lean, lines 14-15, SHA-256 eb474c59b02738fa364b083f7c3f854ab6e1f57dae76acf74969fb1b0dcbbac0; D1Bound5/FinitePAdaptiveLeading.lean, lines 17-19, SHA-256 eb474c59b02738fa364b083f7c3f854ab6e1f57dae76acf74969fb1b0dcbbac0; D1Bound5/FinitePAdaptiveLeading.lean, lines 21-24, SHA-256 eb474c59b02738fa364b083f7c3f854ab6e1f57dae76acf74969fb1b0dcbbac0; D1Bound5/FinitePAdaptiveLeading.lean, lines 26-31, SHA-256 eb474c59b02738fa364b083f7c3f854ab6e1f57dae76acf74969fb1b0dcbbac0. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_FinitePLeadingBound_Definitions

section
namespace D1Bound5

/-- The six remaining terms of H after its pure reciprocal squares cancel. -/
def finitePAdaptiveLeadingTerms (i : Fin 4) : Fin 12 → FinitePLeadingTerm :=
  if i=1 then
    ![(5,1,0,1,3),(-5,0,1,1,3),(5,2,1,1,3),(-5,1,2,1,3),
      (-5,2,0,1,3),(5,0,2,1,3),(0,0,0,0,1),(0,0,0,0,1),
      (0,0,0,0,1),(0,0,0,0,1),(0,0,0,0,1),(0,0,0,0,1)]
  else finitePLeadingTerms i

def finitePLeadingNumeratorExponent (u : FinitePLeadingTerm) (j : Fin 3) : ℕ :=
  if j=u.2.2.1 then u.2.2.2.1 else 0

def finitePLeadingRatioExponent (u : FinitePLeadingTerm) : ℕ :=
  (if u.2.1=0 then 2 else u.2.2.2.2+2)-
    (finitePLeadingNumeratorExponent u 1+finitePLeadingNumeratorExponent u 2)

noncomputable def finitePAdaptiveLeadingTermValue (a b s : ℂ) (u : FinitePLeadingTerm) : ℂ :=
  (u.1 : ℂ)*a^(finitePLeadingNumeratorExponent u 0)*
    b^(finitePLeadingNumeratorExponent u 1)*s^(finitePLeadingNumeratorExponent u 2)/
      (![a,b,s] u.2.1)^u.2.2.2.2

/-- Exact positive leading polynomials in x=A/B from the manuscript. -/
noncomputable def finitePLeadingWeight (x : ℝ) : Fin 4 → ℝ :=
  ![(5*x+10*x^2+10*x^4+5*x^5)/256,
    (10*x+10*x^4+10*x^5)/256,
    (15+80*x+150*x^2+120*x^3+35*x^4)/256,
    (15+80*x+150*x^2+280*x^3+35*x^4)/256]









end D1Bound5
end


