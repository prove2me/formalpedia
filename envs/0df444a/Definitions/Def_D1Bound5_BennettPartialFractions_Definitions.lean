-- Prove2me | Definitions.Def_D1Bound5_BennettPartialFractions_Definitions
-- name    : D1Bound5_BennettPartialFractions_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-24T02:33:46.765009+00:00
-- url     : https://prove2.me/theorems/79e843f6-9fce-4211-ae43-ef6e46e62d44
-- title:
--   Bennett Partial Fractions
-- statement:
--   The common denominator with positive node multiplicities. The named objects in this bundle include `bennettPoleDenominator`.
-- source:
--   D1Bound5/BennettPartialFractions.lean, lines 20-22, SHA-256 010f048f17daf1a97c4058a3ed6d941a8ab25f1f4871529526b7412bcf71a21c. Project: https://github.com/tomislav-math/d1-bound5-lean

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.PartialFractions
import Mathlib.Algebra.Polynomial.RingDivision

section
open Finset Polynomial

namespace D1Bound5

/-!
This module proves existence of the exact cleared partial-fraction decomposition
used by the residue-sum argument. The decomposition is a conclusion, not an
assumption. Identifying its coefficients with the manuscript's explicit finite
binomial sums remains a separate obligation.
-/

section CommRing

variable {R ι : Type*} [CommRing R] [Nontrivial R]
variable [Fintype ι] [DecidableEq ι]

/-- The common denominator with positive node multiplicities. -/
noncomputable def bennettPoleDenominator (a : ι → R) (e : ι → ℕ) : R[X] :=
  ∏ i, (X - C (a i)) ^ (e i + 1)











end CommRing

section Field

variable {F ι : Type*} [Field F] [Fintype ι] [DecidableEq ι]





end Field

end D1Bound5
end


