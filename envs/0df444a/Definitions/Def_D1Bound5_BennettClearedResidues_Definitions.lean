-- Prove2me | Definitions.Def_D1Bound5_BennettClearedResidues_Definitions
-- name    : D1Bound5_BennettClearedResidues_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-23T23:21:31.677909+00:00
-- url     : https://prove2.me/theorems/a2649323-692b-4753-89d2-a3a548d1e75e
-- title:
--   Bennett Cleared Residues
-- statement:
--   A cleared local residue polynomial. The coefficient index `r` is the pole order minus one, and will be either `k-1` or `k`. The named objects in this bundle include `bennettClearedTaylor`, `bennettOtherPoles`, `bennettClearedResidue`.
-- source:
--   D1Bound5/BennettClearedResidues.lean, lines 13-19, SHA-256 ec76df5d4e2c4d6b07d0919f3d7f1eca9b85a57c220d930e6ae87c93827d8f29; D1Bound5/BennettClearedResidues.lean, lines 86-89, SHA-256 ec76df5d4e2c4d6b07d0919f3d7f1eca9b85a57c220d930e6ae87c93827d8f29; D1Bound5/BennettClearedResidues.lean, lines 91-97, SHA-256 ec76df5d4e2c4d6b07d0919f3d7f1eca9b85a57c220d930e6ae87c93827d8f29. Project: https://github.com/tomislav-math/d1-bound5-lean

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_BennettPoleSeries_Definitions

section
open Finset

namespace D1Bound5

variable {F : Type*} [Field F] [CharZero F]

/-- A cleared local residue polynomial. The coefficient index `r` is the
pole order minus one, and will be either `k-1` or `k`. -/
noncomputable def bennettClearedTaylor (k r : ℕ) (ν a : F)
    (B : PowerSeries F) : Polynomial F :=
  ∑ ht ∈ Finset.antidiagonal r,
    Polynomial.C (Ring.choose ((k : F) + ν) ht.1 * PowerSeries.coeff ht.2 B) *
      (Polynomial.X + Polynomial.C a) ^ (k - ht.1)







section Nodes

variable {I : Type*} [DecidableEq I]

/-- All local pole factors except the pole whose residue is being extracted. -/
noncomputable def bennettOtherPoles (s : Finset I) (a : I → F)
    (k : ℕ) (i j : I) : PowerSeries F :=
  ∏ l ∈ s.erase j, bennettPoleSeries (a j - a l) (k + if i = l then 1 else 0)

/-- The actual arbitrary-order cleared Bennett residue polynomial.
For positive k this is exactly the finite residue construction in the paper,
with the reciprocal-pole multi-index sum grouped into a formal coefficient. -/
noncomputable def bennettClearedResidue (s : Finset I) (a : I → F)
    (k : ℕ) (ν : F) (i j : I) : Polynomial F :=
  bennettClearedTaylor k (k + (if i = j then 1 else 0) - 1) ν (a j)
    (bennettOtherPoles s a k i j)













end Nodes

end D1Bound5
end


