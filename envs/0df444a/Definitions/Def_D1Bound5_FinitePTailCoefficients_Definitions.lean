-- Prove2me | Definitions.Def_D1Bound5_FinitePTailCoefficients_Definitions
-- name    : D1Bound5_FinitePTailCoefficients_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-23T22:27:59.360208+00:00
-- url     : https://prove2.me/theorems/71a0a905-838b-4135-849b-f65584cdd84d
-- title:
--   Finite PTail Coefficients
-- statement:
--   Signed coefficient, power of the root anchor, power of the other anchor. Zero padding keeps each coefficient a sum over Fin3. The named objects in this bundle include `finitePTailCoeffTerms`, `finitePTailCoeffWeight`.
-- source:
--   D1Bound5/FinitePTailCoefficients.lean, lines 8-22, SHA-256 48599cb8aa9aff9768b21efa168c2d0d2e6b70cc69039e6172943d1904229fb4; D1Bound5/FinitePTailCoefficients.lean, lines 24-25, SHA-256 48599cb8aa9aff9768b21efa168c2d0d2e6b70cc69039e6172943d1904229fb4. Project: https://github.com/tomislav-math/d1-bound5-lean

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

section
namespace D1Bound5

attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three

/-- Signed coefficient, power of the root anchor, power of the other
anchor. Zero padding keeps each coefficient a sum over Fin3. -/
def finitePTailCoeffTerms : Fin 2 → Fin 2 → Fin 3 → Fin 3 → ℤ × ℕ × ℕ :=
  ![![![![(7,2,0),(-35,1,1),(0,0,0)],
        ![(64,3,0),(-140,2,1),(0,0,0)],
        ![(72,4,0),(-120,3,1),(0,0,0)]],
      ![![(35,1,1),(-7,2,0),(0,0,0)],
        ![(140,2,1),(-64,3,0),(0,0,0)],
        ![(120,3,1),(-72,4,0),(0,0,0)]]],
    ![![![(-15,3,0),(56,2,1),(-105,1,2)],
        ![(-180,4,0),(512,3,1),(-420,2,2)],
        ![(-240,5,0),(576,4,1),(-360,3,2)]],
      ![![(70,2,1),(-6,3,0),(0,0,0)],
        ![(100,3,1),(-12,4,0),(0,0,0)],
        ![(24,5,0),(0,0,0),(0,0,0)]]]]

def finitePTailCoeffWeight (kind side : Fin 2) (l : Fin 3) : ℕ :=
  ∑ t : Fin 3, (finitePTailCoeffTerms kind side l t).1.natAbs









end D1Bound5
end


