-- Prove2me | Definitions.Def_OAI_NumberTheory_DirichletL_Moments_PrimePower
-- name    : OAI_NumberTheory_DirichletL_Moments_PrimePower
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T19:33:36.584338+00:00
-- url     : https://prove2.me/theorems/e84d1dc3-a9b6-46ff-92ac-e8bb2fcb3961
-- title:
--   Prime Power
-- statement:
--   Definitions and structural lemmas for Prime Power, from LW56e2 and the credited OpenAI and dependency authors's pinned QRH LW56e2 refinement development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Moments/PrimePower.lean

import Definitions.Def_OAI_NumberTheory_DirichletL_Moments_Correlation
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.RingTheory.Ideal.Quotient.PowTransition
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
set_option autoImplicit false
namespace OAI
open scoped BigOperators Classical
open NumberField
namespace SevenEighths.CenteredMomentCorrelation
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
local instance _p2m_local_instance_3727eb8614_14 : Infinite (𝓞 K) := Module.Free.infinite ℤ (𝓞 K)
def primePowerReduction (P : Ideal (𝓞 K)) {c : ℕ} (hc : 1 ≤ c) :
    (𝓞 K ⧸ P ^ c) →+* (𝓞 K ⧸ P) :=
  Ideal.Quotient.factor (by simpa using Ideal.pow_le_pow_right (I := P) hc)
def primePowerCharacter (P : Ideal (𝓞 K)) {c : ℕ} (hc : 1 ≤ c)
    (χ : MulChar (𝓞 K ⧸ P) ℂ) : MulChar (𝓞 K ⧸ P ^ c) ℂ where
  __ := χ.toMonoidHom.comp (primePowerReduction P hc).toMonoidHom
  map_nonunit' := by
    intro x hx
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    change χ (Ideal.Quotient.mk P a) = 0
    apply χ.map_nonunit
    intro ha
    exact hx ((Ideal.Quotient.isUnit_mk_pow_iff_isUnit_mk P (by omega)).mpr ha)
section Local
variable (P : Ideal (𝓞 K)) [P.IsMaximal] {c : ℕ} (hc : 1 ≤ c)
variable [Fintype (𝓞 K ⧸ P ^ c)] [Fintype (𝓞 K ⧸ P)]
local instance _p2m_local_instance_3727eb8614_57 : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
end Local
end
end SevenEighths.CenteredMomentCorrelation
end OAI


