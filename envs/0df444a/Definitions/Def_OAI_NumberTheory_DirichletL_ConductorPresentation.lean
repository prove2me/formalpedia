-- Prove2me | Definitions.Def_OAI_NumberTheory_DirichletL_ConductorPresentation
-- name    : OAI_NumberTheory_DirichletL_ConductorPresentation
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T19:34:33.94702+00:00
-- url     : https://prove2.me/theorems/2769202c-fdc8-417f-9521-9a6531e0e0ba
-- title:
--   Conductor Presentation
-- statement:
--   Definitions and structural lemmas for Conductor Presentation, from LW56e2 and the credited OpenAI and dependency authors's pinned QRH LW56e2 refinement development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/ConductorPresentation.lean

import Definitions.Def_OAI_NumberTheory_DirichletL_ConductorBounds
import Definitions.Def_OAI_NumberTheory_DirichletL_CharacterTransport
set_option autoImplicit false
namespace OAI
namespace SevenEighths
namespace FiniteConductor
variable {R : Type*} [CommRing R] [Finite R]
end FiniteConductor
namespace ConductorPresentation
open SevenEighths.FiniteFourier SevenEighths.FiniteConductor
open scoped Classical
noncomputable section
section Transport
variable {A : Type*} [CommRing A]
def quotientCharacter (M : Ideal A) (I : Ideal (A ⧸ M))
    (φ : MulChar ((A ⧸ M) ⧸ I) ℂ) : MulChar (A ⧸ I.comap (Ideal.Quotient.mk M)) ℂ :=
  CharacterTransport.pullback (quotientComapEquiv M I) φ
end Transport
variable {A : Type*} [CommRing A] [hDedekind : IsDedekindDomain A] [hInfinite : Infinite A]
include hDedekind hInfinite
end
end ConductorPresentation
end SevenEighths
end OAI


