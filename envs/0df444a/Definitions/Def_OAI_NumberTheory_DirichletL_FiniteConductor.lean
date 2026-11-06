-- Prove2me | Definitions.Def_OAI_NumberTheory_DirichletL_FiniteConductor
-- name    : OAI_NumberTheory_DirichletL_FiniteConductor
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T19:33:28.496201+00:00
-- url     : https://prove2.me/theorems/629836f9-6b50-4e6f-a87f-3d361e09d6d2
-- title:
--   Finite Conductor
-- statement:
--   Definitions and structural lemmas for Finite Conductor, from LW56e2 and the credited OpenAI and dependency authors's pinned QRH LW56e2 refinement development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/FiniteConductor.lean

import Definitions.Def_OAI_NumberTheory_DirichletL_FiniteFourier
import Mathlib.NumberTheory.MulChar.Duality
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.Order.Preorder.Finite
import Mathlib.RingTheory.Ideal.Maps
set_option autoImplicit false
namespace OAI
namespace SevenEighths.FiniteConductor
open SevenEighths.FiniteFourier
open scoped Classical
noncomputable section
variable {R : Type*} [CommRing R] [Finite R]
def quotientUnits (I : Ideal R) : Rˣ →* (R ⧸ I)ˣ :=
  Units.map (Ideal.Quotient.mk I).toMonoidHom
def FactorsThroughIdeal (χ : MulChar R ℂ) (I : Ideal R) : Prop :=
  ∃ φ : MulChar (R ⧸ I) ℂ,
    φ.toUnitHom.comp (quotientUnits I) = χ.toUnitHom
end
end SevenEighths.FiniteConductor
end OAI


