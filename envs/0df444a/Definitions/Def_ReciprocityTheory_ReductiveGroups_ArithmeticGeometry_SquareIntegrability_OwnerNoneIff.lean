-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_OwnerNoneIff
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_OwnerNoneIff
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:09:20.631453+00:00
-- url     : https://prove2.me/theorems/89d01024-d906-4c2d-99e8-7f679c926b87
-- title:
--   Owner None Iff
-- statement:
--   Definitions and structural lemmas for Owner None Iff, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/OwnerNoneIff.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PolyDerivDeterminantPolyTensor
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.I2
noncomputable section
variable {E : Type} [Field E] [NumberField E] {n nb : ℕ}
section Cols
variable {dim : (E →+* ℂ) → ℕ} (bs : Fin nb → Block E n dim)
def colB (p : Σ j : Fin nb, Fin (bs j).i) : Fin n := (bs p.1).col p.2
variable {bs}
variable (bs)
open Classical in

def owner (k : Fin n) : Option (Σ j : Fin nb, Fin (bs j).i) :=
  if h : ∃ p, colB bs p = k then some h.choose else none
variable {bs}
end Cols
section Letters
variable (X : PT E) {bs : Fin nb → Block E n X.dim}
end Letters
end
end ReciprocityTheory.ChartRestriction.G.I2


