-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PTwinJoinPointModel
-- name    : GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PTwinJoinPointModel
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:11:39.746318+00:00
-- url     : https://prove2.me/theorems/06ea4cef-7de8-4cd1-8fc0-73861db03749
-- title:
--   PTwin Join Point Model
-- statement:
--   Definitions and structural lemmas for PTwin Join Point Model, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PTwinJoinPointModel.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ImportsTerMore
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ClassListMapDomainPerm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PGenericProjClosureDim
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
set_option linter.unusedSectionVars false
namespace GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (ptIdx ptCoord joinCoord mcMap)
namespace JoinPointModel
section Split
variable {K : Type} {ι : K → Type}
def varEquiv : (Σ k : K ⊕ Unit, Sum.elim ι ptIdx k) ≃ Option (Σ k, ι k) where
  toFun
    | ⟨.inl k, i⟩ => some ⟨k, i⟩
    | ⟨.inr _, _⟩ => none
  invFun
    | some p => ⟨.inl p.1, p.2⟩
    | none => ⟨.inr (), (0 : Fin 1)⟩
  left_inv := by
    rintro ⟨k | u, i⟩
    · rfl
    · cases u
      change Fin 1 at i
      have hi : i = 0 := Subsingleton.elim _ _
      subst hi
      rfl
  right_inv := by
    rintro (_ | ⟨k, i⟩) <;> rfl
variable (K) (Ω : Type*) [CommRing Ω]
def tgtEquiv : MvPolynomial (K ⊕ Unit) Ω ≃ₐ[Ω] Polynomial (MvPolynomial K Ω) :=
  (renameEquiv Ω (Equiv.optionEquivSumPUnit.{0, 0} K).symm).trans (optionEquivLeft Ω K)
variable {K} (O : Type*) [CommRing O]
def srcEquiv : MvPolynomial (Σ k : K ⊕ Unit, Sum.elim ι ptIdx k) O ≃ₐ[O]
    Polynomial (MvPolynomial (Σ k, ι k) O) :=
  (renameEquiv O varEquiv).trans (optionEquivLeft O _)
end Split
section Cone
variable {O : Type*} [CommRing O] {Ω : Type*} [Field Ω] [Algebra O Ω]
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
end Cone
end JoinPointModel
end GroundTheory.Heights₂.Heights.NumbersDVR


