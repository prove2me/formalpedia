-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PHilbAddBlock
-- name    : GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PHilbAddBlock
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:40:52.807069+00:00
-- url     : https://prove2.me/theorems/9d7a7821-5abc-4973-bb15-63850b802df9
-- title:
--   PHilb Add Block
-- statement:
--   Definitions and structural lemmas for PHilb Add Block, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PHilbAddBlock.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsAddBlock
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PGradedFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PIntNumBaseChange
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_coeff_coeffForm_479fc53ecb0b
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] P2M_GroundTheory_Heights__Heights_FieldNumbers_coeff_coeffForm_479fc53ecb0b


set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.FieldNumbers
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u
namespace HilbAddBlock
variable {K : Type} [DecidableEq K] {ι : K → Type} {N : ℕ}
def varSplit (ι : K → Type) (N : ℕ) : (Σ o, addBlock ι N o) ≃ Fin (N + 1) ⊕ (Σ k, ι k) where
  toFun v := match v with
    | ⟨none, j⟩ => Sum.inl j
    | ⟨some k, i⟩ => Sum.inr ⟨k, i⟩
  invFun w := match w with
    | Sum.inl j => ⟨none, j⟩
    | Sum.inr v => addBlockIncl ι N v
  left_inv := by rintro ⟨_ | k, i⟩ <;> rfl
  right_inv := by rintro (j | ⟨k, i⟩) <;> rfl
def newVar (ι : K → Type) (N : ℕ) : Fin (N + 1) → (Σ o, addBlock ι N o) := fun j => ⟨none, j⟩
omit [DecidableEq K] in
theorem addBlockIncl_injective : Function.Injective (addBlockIncl ι N) := by
  intro v w h
  simp only [addBlockIncl] at h
  obtain ⟨h1, h2⟩ := Sigma.mk.inj h
  exact Sigma.ext (Option.some.inj h1) h2
omit [DecidableEq K] in
theorem newVar_injective : Function.Injective (newVar ι N) := by
  intro i j h
  simp only [newVar] at h
  exact eq_of_heq (Sigma.mk.inj h).2
def splitEquiv (F : Type u) [Field F] (ι : K → Type) (N : ℕ) :
    MRing (addBlock ι N) F ≃ₐ[F] MvPolynomial (Fin (N + 1)) (MRing ι F) :=
  (renameEquiv F (varSplit ι N)).trans (sumAlgEquiv F (Fin (N + 1)) (Σ k, ι k))
variable {F : Type u} [Field F]
def comb (d : (Σ k, ι k) →₀ ℕ) (a : Fin (N + 1) →₀ ℕ) : (Σ o, addBlock ι N o) →₀ ℕ :=
  Finsupp.mapDomain (addBlockIncl ι N) d + Finsupp.mapDomain (newVar ι N) a
variable [Fintype K] [∀ k, Fintype (ι k)]
end HilbAddBlock
end
end GroundTheory.Heights₂.Heights.FieldNumbers


