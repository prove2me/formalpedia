-- Prove2me | Definitions.Def_D1Bound5_BennettLocalResidues_Definitions
-- name    : D1Bound5_BennettLocalResidues_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-24T01:26:44.68405+00:00
-- url     : https://prove2.me/theorems/e7f0cd45-c0b6-45ed-909c-e4a3ee9e149e
-- title:
--   Bennett Local Residues
-- statement:
--   Exact polynomial substitution at the local coordinate `b + X`. The named objects in this bundle include `bennettShiftToSeries`, `bennettLocalReciprocal`, `bennettLocalResidue`.
-- source:
--   D1Bound5/BennettLocalResidues.lean, lines 13-15, SHA-256 69884bc84f14bf065cb46a21f71bb9f253dca11c8d085058e033df4ac0004d31; D1Bound5/BennettLocalResidues.lean, lines 29-33, SHA-256 69884bc84f14bf065cb46a21f71bb9f253dca11c8d085058e033df4ac0004d31; D1Bound5/BennettLocalResidues.lean, lines 35-40, SHA-256 69884bc84f14bf065cb46a21f71bb9f253dca11c8d085058e033df4ac0004d31. Project: https://github.com/tomislav-math/d1-bound5-lean

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.PartialFractions
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_BennettPoleSeries_Definitions

section
open Finset

namespace D1Bound5

section Field

variable {F ι : Type*} [Field F] [CharZero F]
variable [Fintype ι] [DecidableEq ι]

/-- Exact polynomial substitution at the local coordinate `b + X`. -/
noncomputable def bennettShiftToSeries (b : F) : Polynomial F →+* PowerSeries F :=
  Polynomial.eval₂RingHom PowerSeries.C (PowerSeries.C b + PowerSeries.X)





/-- The explicit reciprocal of the product of the other local pole factors. -/
noncomputable def bennettLocalReciprocal (a : ι → F) (e : ι → ℕ) (i : ι) :
    PowerSeries F :=
  ∏ l ∈ (Finset.univ : Finset ι).erase i,
    bennettPoleSeries (a i - a l) (e l + 1)

/-- The algebraic residue defined by a concrete coefficient of explicit
negative-integer binomial series. -/
noncomputable def bennettLocalResidue (a : ι → F) (e : ι → ℕ)
    (f : Polynomial F) (i : ι) : F :=
  PowerSeries.coeff (e i)
    (bennettShiftToSeries (a i) f * bennettLocalReciprocal a e i)













end Field

end D1Bound5
end


