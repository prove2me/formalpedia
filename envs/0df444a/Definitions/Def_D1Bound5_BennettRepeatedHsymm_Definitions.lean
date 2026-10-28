-- Prove2me | Definitions.Def_D1Bound5_BennettRepeatedHsymm_Definitions
-- name    : D1Bound5_BennettRepeatedHsymm_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-23T22:31:40.999833+00:00
-- url     : https://prove2.me/theorems/9ef80795-f409-4447-9fdc-780b1ecfe6b8
-- title:
--   Bennett Repeated Hsymm
-- statement:
--   The formal generating series of actual complete homogeneous symmetric polynomials. Values of the variables are allowed to coincide. The named objects in this bundle include `bennettHomogeneousSeries`, `BennettRepeatedNodes`.
-- source:
--   D1Bound5/BennettRepeatedHsymm.lean, lines 13-16, SHA-256 2c35125785b6ff0c9b69a4236b7a718a4b75a5a68706b7a3ada2c46efaddc905; D1Bound5/BennettRepeatedHsymm.lean, lines 81-82, SHA-256 2c35125785b6ff0c9b69a4236b7a718a4b75a5a68706b7a3ada2c46efaddc905. Project: https://github.com/tomislav-math/d1-bound5-lean

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.PartialFractions
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Sym.Basic
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_HomogeneousSymmetric_Definitions

section
open Finset

namespace D1Bound5

section Homogeneous

variable {R ι : Type*} [CommRing R] [DecidableEq ι]

/-- The formal generating series of actual complete homogeneous symmetric
polynomials. Values of the variables are allowed to coincide. -/
noncomputable def bennettHomogeneousSeries [Fintype ι] (a : ι → R) : PowerSeries R :=
  PowerSeries.mk (homogeneousMultisetSum a)







end Homogeneous

section Repeated

variable {F ι : Type*} [Field F] [CharZero F]
variable [Fintype ι] [DecidableEq ι]

/-- One copy of each pole node for each unit of its positive multiplicity. -/
abbrev BennettRepeatedNodes (e : ι → ℕ) := Σ i, Fin (e i + 1)











end Repeated

end D1Bound5
end


