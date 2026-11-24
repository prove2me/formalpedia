-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_IteratedDerivListBound
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_IteratedDerivListBound
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:11:40.209935+00:00
-- url     : https://prove2.me/theorems/7677511d-2057-4c20-b125-a1e1f8fe4ee1
-- title:
--   Iterated Deriv List Bound
-- statement:
--   Definitions and structural lemmas for Iterated Deriv List Bound, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/IteratedDerivListBound.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_OwnerNoneIff
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
section Col
variable {dim : (E →+* ℂ) → ℕ}
end Col
section Main
variable {dim : (E →+* ℂ) → ℕ} (bs : Fin nb → Block E n dim)
open Classical in

def eU (j : Fin nb) (a : Fin (bs j).i) : Vsp dim :=
  EuclideanSpace.single (⟨(bs j).τ, Fin.castLE (bs j).hi a⟩ : Idx dim) (1 : ℂ)
def idealA (μ : (Σ j : Fin nb, Fin (bs j).i) → ℂ) (y : (Σ j : Fin nb, Fin (bs j).i) → Vsp dim)
    (ee : Fin n → ℂ) (T : Choice bs) (k : Fin n) : ℂ :=
  match owner bs k with
  | some p => μ p * ∏ r, Hf (eU bs p.1 (T p.1 r p.2)) (y p)
  | none => ee k
def blockM (y : (Σ j : Fin nb, Fin (bs j).i) → Vsp dim) (j : Fin nb) :
    Matrix (Fin (bs j).i) (Fin (bs j).i) ℂ :=
  Matrix.of fun a b => Hf (eU bs j a) (y ⟨j, b⟩)
end Main
end
end ReciprocityTheory.ChartRestriction.G.I2


