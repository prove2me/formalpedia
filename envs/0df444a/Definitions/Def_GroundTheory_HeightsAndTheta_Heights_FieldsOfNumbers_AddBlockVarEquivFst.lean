-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_AddBlockVarEquivFst
-- name    : GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_AddBlockVarEquivFst
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:30:48.804734+00:00
-- url     : https://prove2.me/theorems/a7609a1b-bcbb-496a-9395-3f7d27acc87f
-- title:
--   Add Block Var Equiv Fst
-- statement:
--   Definitions and structural lemmas for Add Block Var Equiv Fst, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/AddBlockVarEquivFst.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PfContractedHypothesesExample
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.FieldNumbers
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u
namespace AddBlockFunctionField
section Projection
variable {F : Type u} [Field F] {K L : Type} {ι : K → Type} {ι₂ : L → Type}
example : MRing (fun k => Sum.elim ι ι₂ ((Function.Embedding.inl : K ↪ K ⊕ L) k)) F =
    MRing ι F := rfl
end Projection
section NewBlock
variable {F : Type u} [Field F] {K : Type} {ι : K → Type}
abbrev blockEquiv (K : Type) : Option K ≃ K ⊕ Unit := Equiv.optionEquivSumPUnit K
def addBlockVarEquiv (ι : K → Type) (N : ℕ) :
    (Σ o, addBlock ι N o) ≃ (Σ s, Sum.elim ι (fun _ : Unit => Fin (N + 1)) s) where
  toFun v := match v with
    | ⟨none, i⟩ => ⟨Sum.inr (), i⟩
    | ⟨some k, x⟩ => ⟨Sum.inl k, x⟩
  invFun v := match v with
    | ⟨Sum.inl k, x⟩ => ⟨some k, x⟩
    | ⟨Sum.inr (), i⟩ => ⟨none, i⟩
  left_inv v := by rcases v with ⟨_ | k, x⟩ <;> rfl
  right_inv v := by rcases v with ⟨k | ⟨⟩, x⟩ <;> rfl
def addBlockRingEquiv (ι : K → Type) (N : ℕ) :
    MRing (addBlock ι N) F ≃ₐ[F] MRing (Sum.elim ι (fun _ : Unit => Fin (N + 1))) F :=
  renameEquiv F (addBlockVarEquiv ι N)
end NewBlock
end AddBlockFunctionField
end
end GroundTheory.Heights₂.Heights.FieldNumbers


