-- Prove2me | Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_CharacterAnalytic
-- name    : OAI_NumberTheory_DirichletL_Hecke_CharacterAnalytic
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T22:16:11.250075+00:00
-- url     : https://prove2.me/theorems/c4ed30a9-9f26-4129-a48e-2cfeb6751b1b
-- title:
--   Character Analytic
-- statement:
--   Definitions and structural lemmas for Character Analytic, from LW56e2 and the credited OpenAI and dependency authors's pinned QRH LW56e2 refinement development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Hecke/CharacterAnalytic.lean

import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_Coordinates
import Theorems.Thm_OAI_SevenEighths_EisensteinTheta_parityPair_k
import Theorems.Thm_OAI_SevenEighths_HeckeCoordinates_coordinateQuotientHom_intCast
import Theorems.Thm_OAI_SevenEighths_HeckeFamily_elementCoeff_one
import Theorems.Thm_OAI_SevenEighths_HeckeTheta_pair_k
import Theorems.Thm_OAI_SevenEighths_ThetaProduct_rectangularPair_k
attribute [local simp] OAI.SevenEighths.EisensteinTheta.parityPair_k
attribute [local simp] OAI.SevenEighths.HeckeCoordinates.coordinateQuotientHom_intCast
attribute [local simp] OAI.SevenEighths.HeckeFamily.elementCoeff_one
attribute [local simp] OAI.SevenEighths.HeckeTheta.pair_k
attribute [local simp] OAI.SevenEighths.ThetaProduct.rectangularPair_k


set_option autoImplicit false
namespace OAI
noncomputable section
open scoped BigOperators
namespace SevenEighths.HeckeCharacterAnalytic
def additiveFiberEquiv {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (π : A →+ B) (hπ : Function.Surjective π) : A ≃ B × π.ker := by
  classical
  let r : B → A := fun b => (hπ b).choose
  have hr : ∀ b, π (r b) = b := fun b => (hπ b).choose_spec
  exact {
    toFun := fun a => (π a, ⟨a - r (π a), by simp [AddMonoidHom.mem_ker, hr]⟩)
    invFun := fun p => p.2 + r p.1
    left_inv := by intro a; simp
    right_inv := by
      rintro ⟨b, k⟩
      have hk : π k = 0 := k.property
      apply Prod.ext
      · simp [hr, hk]
      · apply Subtype.ext
        simp [hr, hk] }
def finCastEquiv (N : ℕ) [NeZero N] : Fin N ≃ ZMod N where
  toFun a := (a : ℕ)
  invFun z := ⟨z.val, ZMod.val_lt z⟩
  left_inv a := Fin.ext (ZMod.val_natCast_of_lt a.isLt)
  right_inv z := ZMod.natCast_zmod_val z
end SevenEighths.HeckeCharacterAnalytic
end
end OAI


