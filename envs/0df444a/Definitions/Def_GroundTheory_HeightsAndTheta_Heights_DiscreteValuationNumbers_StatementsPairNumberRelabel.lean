-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsPairNumberRelabel
-- name    : GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsPairNumberRelabel
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:43:46.637367+00:00
-- url     : https://prove2.me/theorems/f7efb562-6a36-424d-857c-9182adc12b07
-- title:
--   Statements Pair Number Relabel
-- statement:
--   Definitions and structural lemmas for Statements Pair Number Relabel, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/StatementsPairNumberRelabel.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_BundleObjects
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
noncomputable section
def PairNumberRelabel.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O)
    (K₁ : Type) [Fintype K₁] [DecidableEq K₁] (ι₁ : K₁ → Type) [∀ k, Fintype (ι₁ k)]
    (K₂ : Type) [Fintype K₂] [DecidableEq K₂] (ι₂ : K₂ → Type) [∀ k, Fintype (ι₂ k)]
    (e : K₁ ≃ K₂) (σ : (Σ k, ι₁ k) ≃ (Σ k, ι₂ k)), (∀ v, (σ v).1 = e v.1) →
    ∀ P : Ideal (MRing ι₁ O),
      (∀ d : ℕ, IsModelOver P d → IsModelOver (P.map (rename σ)) d) ∧
      (∀ (b : K₂ → ℤ) (f g : MRing ι₁ O), IsVerticalDivisor P ϖ (b ∘ e) f g →
        IsVerticalDivisor (P.map (rename σ)) ϖ b (rename σ f) (rename σ g)) ∧
      (∀ (n : ℕ) (x x' : Fin n → K₂ → ℤ) (f g : Fin n → MRing ι₁ O)
        (Gs : Fin n → MvPolynomial (Fin n ⊕ Fin n) ℤ) (Q : List (K₂ → ℤ)),
        pairNum (P.map (rename σ)) x x' (fun i => rename σ (f i)) (fun i => rename σ (g i)) Gs Q =
          pairNum P (fun i => x i ∘ e) (fun i => x' i ∘ e) f g Gs (Q.map (· ∘ e)))
section Examples
def swapFactors : (Σ _ : Fin 2, Fin 2) ≃ (Σ _ : Fin 2, Fin 2) where
  toFun v := ⟨Equiv.swap 0 1 v.1, v.2⟩
  invFun v := ⟨Equiv.swap 0 1 v.1, v.2⟩
  left_inv := by
    rintro ⟨a, b⟩
    simp
  right_inv := by
    rintro ⟨a, b⟩
    simp
end Examples
end
end GroundTheory.Heights₂.Heights.NumbersDVR


