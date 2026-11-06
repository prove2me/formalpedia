-- Prove2me | Definitions.Def_OAI_NumberTheory_DirichletL_ResidueCharacter
-- name    : OAI_NumberTheory_DirichletL_ResidueCharacter
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T19:40:57.716358+00:00
-- url     : https://prove2.me/theorems/233ab6b8-36da-4774-82a2-2023c5d0adf8
-- title:
--   Residue Character
-- statement:
--   Definitions and structural lemmas for Residue Character, from LW56e2 and the credited OpenAI and dependency authors's pinned QRH LW56e2 refinement development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/ResidueCharacter.lean

import Definitions.Def_OAI_NumberTheory_DirichletL_ConductorPresentation
set_option autoImplicit false
namespace OAI
namespace SevenEighths.ResidueCharacter
open SevenEighths.FiniteFourier SevenEighths.FiniteConductor
open SevenEighths.ConductorPresentation
open scoped Classical
noncomputable section
variable {A : Type*} [CommRing A]
def inflate {M L : Ideal A} (hML : M ≤ L) (χ : MulChar (A ⧸ L) ℂ) :
    MulChar (A ⧸ M) ℂ :=
  MulChar.ofUnitHom (χ.toUnitHom.comp
    (Units.map (Ideal.Quotient.factor hML).toMonoidHom))
def product (I J : Ideal A) (χ : MulChar (A ⧸ I) ℂ) (ψ : MulChar (A ⧸ J) ℂ) :
    MulChar (A ⧸ I ⊓ J) ℂ :=
  inflate inf_le_left χ * inflate inf_le_right ψ
section PrimitiveProduct
variable [hDedekind : IsDedekindDomain A] [hInfinite : Infinite A]
include hDedekind hInfinite
end PrimitiveProduct
end
end SevenEighths.ResidueCharacter
end OAI


