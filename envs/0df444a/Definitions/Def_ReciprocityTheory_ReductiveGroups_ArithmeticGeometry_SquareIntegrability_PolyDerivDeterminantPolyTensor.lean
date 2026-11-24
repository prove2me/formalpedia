-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PolyDerivDeterminantPolyTensor
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PolyDerivDeterminantPolyTensor
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:07:18.374081+00:00
-- url     : https://prove2.me/theorems/af437b38-4ff3-4b00-9178-4b68edee40c1
-- title:
--   Poly Deriv Determinant Poly Tensor
-- statement:
--   Definitions and structural lemmas for Poly Deriv Determinant Poly Tensor, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/PolyDerivDeterminantPolyTensor.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_L2NormFundamentalDomain
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.I2
open MvPolynomial
noncomputable section
variable {E : Type} [Field E] [NumberField E] {n nb : ℕ} {dim : (E →+* ℂ) → ℕ}
section Expand
variable (bs : Fin nb → Block E n dim)
abbrev Choice := ∀ j : Fin nb, Fin (bs j).c → Equiv.Perm (Fin (bs j).i)
abbrev Slot := Σ j : Fin nb, Fin (bs j).c × Fin (bs j).i
def sgnT (T : Choice bs) : ℂ := ∏ j, ∏ r, ((Equiv.Perm.sign (T j r) : ℤ) : ℂ)
def letter (T : Choice bs) (t : Slot bs) : Letter n dim :=
  ((bs t.1).col t.2.2, ⟨(bs t.1).τ, Fin.castLE (bs t.1).hi (T t.1 t.2.1 t.2.2)⟩)
end Expand
section PD
variable (X : PT E) (bs : Fin nb → Block E n X.dim)
open Classical in

def lst (T : Choice bs) : List (Fin n × Vsp X.dim) :=
  (Multiset.map (letter bs T) Finset.univ.val).toList.map
    (fun l => (l.1, EuclideanSpace.single l.2 (1 : ℂ)))
end PD
end
end ReciprocityTheory.ChartRestriction.G.I2


