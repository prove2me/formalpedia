-- Prove2me | Definitions.Def_D1Bound5_FiniteMBennettIdentity_Definitions
-- name    : D1Bound5_FiniteMBennettIdentity_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-23T23:26:06.125284+00:00
-- url     : https://prove2.me/theorems/ee864353-d88f-4dea-9abc-3a54ee12d5b0
-- title:
--   Finite MBennett Identity
-- statement:
--   Definitions for finite mbennett identity in the argument bounding Diophantine D(1) sets in imaginary quadratic integer rings. The named objects in this bundle include `finiteMNodes`, `finiteMBennettEntry`.
-- source:
--   D1Bound5/FiniteMBennettIdentity.lean, lines 12-12, SHA-256 291fd6ba981541548cef4bed5210986ea71cc1c1e28ff467e85be78d671f7779; D1Bound5/FiniteMBennettIdentity.lean, lines 14-16, SHA-256 291fd6ba981541548cef4bed5210986ea71cc1c1e28ff467e85be78d671f7779. Project: https://github.com/tomislav-math/d1-bound5-lean

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.PartialFractions
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Polynomial
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_BennettClearedResidues_Definitions

section
open Finset Polynomial

namespace D1Bound5

variable {F : Type*} [Field F] [CharZero F]

def finiteMNodes (a b s : F) : Fin 4 → F := ![0,b*s,a*s,a*b]

noncomputable def finiteMBennettEntry (a b s c : F) (i j : Fin 4) : F :=
  (4*(a*b*s)^2*((a-b)*(a-s)*(b-s))^2)^2 *
    (bennettClearedResidue univ (finiteMNodes a b s) 2 (1/2 : F) i j).eval (a*b*s*c)













end D1Bound5
end


