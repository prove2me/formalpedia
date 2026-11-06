-- Prove2me | Definitions.Def_OAI_NumberTheory_DirichletL_ConductorBounds
-- name    : OAI_NumberTheory_DirichletL_ConductorBounds
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T19:33:47.44498+00:00
-- url     : https://prove2.me/theorems/e987ffc1-0dd7-412f-abf6-430752f746f5
-- title:
--   Conductor Bounds
-- statement:
--   Definitions and structural lemmas for Conductor Bounds, from LW56e2 and the credited OpenAI and dependency authors's pinned QRH LW56e2 refinement development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/ConductorBounds.lean

import Definitions.Def_OAI_NumberTheory_DirichletL_FiniteConductor
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
set_option autoImplicit false
namespace OAI
namespace SevenEighths.FiniteConductor
open SevenEighths.FiniteFourier
open scoped Classical
noncomputable section
section QuotientBounds
variable {R : Type*} [CommRing R]
noncomputable def quotientComapEquiv (M : Ideal R) (I : Ideal (R ⧸ M)) :
    R ⧸ I.comap (Ideal.Quotient.mk M) ≃+* (R ⧸ M) ⧸ I :=
  RingEquiv.ofBijective (Ideal.quotientMap I (Ideal.Quotient.mk M) le_rfl)
    ⟨Ideal.quotientMap_injective,
      Ideal.quotientMap_surjective Ideal.Quotient.mk_surjective⟩
end QuotientBounds
section FiniteRing
variable {R : Type*} [CommRing R] [Finite R]
end FiniteRing
variable {A : Type*} [CommRing A] [hDedekind : IsDedekindDomain A] [hInfinite : Infinite A]
include hDedekind hInfinite
end
end SevenEighths.FiniteConductor
end OAI


