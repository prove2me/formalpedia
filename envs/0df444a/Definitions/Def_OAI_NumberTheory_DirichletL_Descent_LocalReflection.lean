-- Prove2me | Definitions.Def_OAI_NumberTheory_DirichletL_Descent_LocalReflection
-- name    : OAI_NumberTheory_DirichletL_Descent_LocalReflection
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T19:33:54.534924+00:00
-- url     : https://prove2.me/theorems/da85d826-648c-4004-af7f-d5f0b6d7838d
-- title:
--   Local Reflection
-- statement:
--   Definitions and structural lemmas for Local Reflection, from LW56e2 and the credited OpenAI and dependency authors's pinned QRH LW56e2 refinement development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Descent/LocalReflection.lean

import Mathlib.NumberTheory.GaussSum
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Ring
set_option autoImplicit false
namespace OAI
namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
noncomputable section
variable {F : Type*} [Field F] [Fintype F]
def zeroMark (x : F) : ℂ := if x = 0 then 1 else 0
def localFourier (f : F → ℂ) (ψ : AddChar F ℂ) (h : F) : ℂ :=
  ∑ t : F, f t * ψ (-(h * t))
def localReflectionActive (f : F → ℂ) (χ : MulChar F ℂ)
    (ψ : AddChar F ℂ) (σ ε : Fˣ) (x : F) : ℂ :=
  (Fintype.card F : ℂ)⁻¹ * ∑ h : Fˣ,
    localFourier f ψ h * ((χ⁻¹) ^ 2) (σ * h) *
      ψ (((ε : F) * x) * ((h⁻¹ : Fˣ) : F))
end
end SevenEighths.InverseMoment
end OAI


