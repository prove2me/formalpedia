-- Prove2me | Definitions.Def_D1Bound5_BennettResiduesAtInfinity_Definitions
-- name    : D1Bound5_BennettResiduesAtInfinity_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-23T22:25:35.261839+00:00
-- url     : https://prove2.me/theorems/48926015-9d07-4dd0-b860-b005264f1c27
-- title:
--   Bennett Residues At Infinity
-- statement:
--   The explicit power series of the reciprocal denominator at infinity. The named objects in this bundle include `bennettReciprocalInfinity`.
-- source:
--   D1Bound5/BennettResiduesAtInfinity.lean, lines 153-156, SHA-256 58386256effb45be605c396f13b3729aec81aaca34f62f0de6ccd21675f2e5ad. Project: https://github.com/tomislav-math/d1-bound5-lean

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.PartialFractions
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.Tactic.Ring

section
open Finset Polynomial

namespace D1Bound5

section Reverse

variable {F : Type*} [Field F]



end Reverse

section Residues

variable {F ι : Type*} [Field F] [CharZero F]
variable [Fintype ι] [DecidableEq ι]







/-- The explicit power series of the reciprocal denominator at infinity. -/
noncomputable def bennettReciprocalInfinity (a : ι → F) (e : ι → ℕ) : PowerSeries F :=
  ∏ i, PowerSeries.rescale (-a i)
    (PowerSeries.binomialSeries F (-((e i + 1 : ℕ) : F)))









end Residues

end D1Bound5
end


