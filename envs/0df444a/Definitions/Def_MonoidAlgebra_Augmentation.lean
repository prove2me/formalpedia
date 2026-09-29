-- Prove2me | Definitions.Def_MonoidAlgebra_Augmentation
-- name    : MonoidAlgebra_Augmentation
-- status  : Definition
-- author  : @davidloeffler
-- created : 2026-09-21T08:59:18.478685+00:00
-- url     : https://prove2.me/theorems/1f3336c0-5e55-4c32-ad1b-1b4fe4f6782e
-- title:
--   Augmentation of a monoid algebra and a valuation-subring equivalence
-- statement:
--   Define the augmentation ring homomorphism R[G] → R by summing coefficients. Also record the canonical ring equivalence between a valuation subring as a type and the subtype of its underlying Subring; this is used to transfer the local group-ring criterion to the coefficient-ring presentation occurring in the horizontal construction.
-- source:
--   Standard definitions for group rings and valuation subrings.

import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.RingTheory.Valuation.ValuationSubring

set_option autoImplicit false
noncomputable section

namespace MonoidAlgebra

/-- The augmentation homomorphism from a monoid algebra to its coefficient ring. -/
def augmentation (R : Type*) [CommRing R] (G : Type*) [Group G] :
    MonoidAlgebra R G →+* R :=
  (MonoidAlgebra.lift R R G 1).toRingHom

end MonoidAlgebra

namespace ValuationSubring

/-- The subtype of a valuation subring and the subtype of its underlying
`Subring` are canonically isomorphic as rings. -/
def subtypeToSubringEquiv {K : Type*} [Field K] (A : ValuationSubring K) :
    A.toSubring ≃+* A where
  toFun x := ⟨x.1, x.2⟩
  invFun x := ⟨x.1, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

end ValuationSubring


