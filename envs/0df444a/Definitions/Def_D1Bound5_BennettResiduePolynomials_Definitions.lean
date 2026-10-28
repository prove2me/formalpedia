-- Prove2me | Definitions.Def_D1Bound5_BennettResiduePolynomials_Definitions
-- name    : D1Bound5_BennettResiduePolynomials_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-24T00:42:19.67031+00:00
-- url     : https://prove2.me/theorems/859cf12f-36af-4e80-8b8f-c60087d6fef3
-- title:
--   Bennett Residue Polynomials
-- statement:
--   The original polynomial local residue, before the substitution x=1/N. The named objects in this bundle include `bennettResidueTaylor`, `bennettPolynomialResidue`.
-- source:
--   D1Bound5/BennettResiduePolynomials.lean, lines 9-15, SHA-256 5264fd8f08d4a6fb748bab8f101f05ca183c3e4658b02954972b81e086f0144d; D1Bound5/BennettResiduePolynomials.lean, lines 80-84, SHA-256 5264fd8f08d4a6fb748bab8f101f05ca183c3e4658b02954972b81e086f0144d. Project: https://github.com/tomislav-math/d1-bound5-lean

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_BennettClearedResidues_Definitions

section
open Finset

namespace D1Bound5

variable {F : Type*} [Field F] [CharZero F]

/-- The original polynomial local residue, before the substitution x=1/N. -/
noncomputable def bennettResidueTaylor (k r : ℕ) (ν a : F)
    (B : PowerSeries F) : Polynomial F :=
  ∑ ht ∈ Finset.antidiagonal r,
    Polynomial.C (Ring.choose ((k : F) + ν) ht.1 * PowerSeries.coeff ht.2 B) *
      (Polynomial.X ^ ht.1 *
        (1 + Polynomial.C a * Polynomial.X) ^ (k - ht.1))







section Nodes

variable {I : Type*} [DecidableEq I]

/-- The polynomial matrix entry P_ij(x) of arbitrary positive order. -/
noncomputable def bennettPolynomialResidue (s : Finset I) (a : I → F)
    (k : ℕ) (ν : F) (i j : I) : Polynomial F :=
  bennettResidueTaylor k (k + (if i = j then 1 else 0) - 1) ν (a j)
    (bennettOtherPoles s a k i j)





end Nodes

end D1Bound5
end


