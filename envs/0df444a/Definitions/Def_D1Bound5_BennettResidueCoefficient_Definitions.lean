-- Prove2me | Definitions.Def_D1Bound5_BennettResidueCoefficient_Definitions
-- name    : D1Bound5_BennettResidueCoefficient_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-24T02:51:11.926979+00:00
-- url     : https://prove2.me/theorems/8e069b75-cf51-4288-8ad3-1254435e521a
-- title:
--   Bennett Residue Coefficient
-- statement:
--   The numerator obtained on clearing the pole at node `i`. The multiplicity at node `l` is `e l + 1`. The index `j = Fin.last (e i)` is the simple pole, in exactly the indexing used by mathlib partial fractions. The named objects in this bundle include `clearedPoleNumerator`.
-- source:
--   D1Bound5/BennettResidueCoefficient.lean, lines 14-20, SHA-256 8c207032d119b0629e3cee3a36cfe0f7dd94d73784c8b28b8cba78efa262f829. Project: https://github.com/tomislav-math/d1-bound5-lean

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.RingDivision

section
open Finset Polynomial

namespace D1Bound5

section CommRing

variable {R ι : Type*} [CommRing R] [Nontrivial R]
variable [Fintype ι] [DecidableEq ι]

/-- The numerator obtained on clearing the pole at node `i`.
The multiplicity at node `l` is `e l + 1`. The index `j = Fin.last (e i)`
is the simple pole, in exactly the indexing used by mathlib partial fractions. -/
noncomputable def clearedPoleNumerator (a : ι → R) (e : ι → ℕ)
    (i : ι) (j : Fin (e i + 1)) : R[X] :=
  (X - C (a i)) ^ j.val *
    ∏ l ∈ (Finset.univ : Finset ι).erase i, (X - C (a l)) ^ (e l + 1)











end CommRing

end D1Bound5
end


