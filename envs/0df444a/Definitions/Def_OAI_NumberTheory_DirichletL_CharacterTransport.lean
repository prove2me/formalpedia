-- Prove2me | Definitions.Def_OAI_NumberTheory_DirichletL_CharacterTransport
-- name    : OAI_NumberTheory_DirichletL_CharacterTransport
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T19:33:52.564301+00:00
-- url     : https://prove2.me/theorems/68cd9b60-a796-4bd7-b47f-85fce6c8db34
-- title:
--   Character Transport
-- statement:
--   Definitions and structural lemmas for Character Transport, from LW56e2 and the credited OpenAI and dependency authors's pinned QRH LW56e2 refinement development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/CharacterTransport.lean

import Definitions.Def_OAI_NumberTheory_DirichletL_FiniteConductor
set_option autoImplicit false
namespace OAI
namespace SevenEighths.CharacterTransport
open SevenEighths.FiniteFourier
noncomputable section
variable {R S : Type*} [CommRing R] [CommRing S]
def pullback (e : R ≃+* S) (χ : MulChar S ℂ) : MulChar R ℂ where
  toFun := fun x => χ (e x)
  map_one' := by simp
  map_mul' := by intro x y; simp
  map_nonunit' := by
    intro x hx
    apply χ.map_nonunit
    intro h
    apply hx
    simpa using h.map e.symm.toMonoidHom
end
end SevenEighths.CharacterTransport
end OAI


