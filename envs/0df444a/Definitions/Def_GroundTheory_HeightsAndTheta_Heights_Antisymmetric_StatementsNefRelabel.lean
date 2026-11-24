-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_StatementsNefRelabel
-- name    : GroundTheory_HeightsAndTheta_Heights_Antisymmetric_StatementsNefRelabel
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:18:17.17087+00:00
-- url     : https://prove2.me/theorems/d9e203fe-0279-46fc-93ae-628022bc983e
-- title:
--   Statements Nef Relabel
-- statement:
--   Definitions and structural lemmas for Statements Nef Relabel, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Antisymmetric/StatementsNefRelabel.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ArithmeticHilbertSamuelLowerBound
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
namespace GroundTheory.Heights₂.Heights
open ReciprocityTheory.ChartRestriction.G.Geo
def relabelBlocks {K K' : Type} {ι : K → Type} {ι' : K' → Type} (ε : K ≃ K')
    (h : ∀ k, ι k = ι' (ε k)) : (Σ k, ι k) ≃ (Σ k', ι' k') :=
  Equiv.sigmaCongr ε fun k => Equiv.cast (h k)
def NefOnFibresRelabel.Statement : Prop :=
  ∀ (K K' : Type) [Fintype K] [Fintype K'] (ι : K → Type) (ι' : K' → Type)
    [∀ k, Fintype (ι k)] [∀ k, Fintype (ι' k)] (ε : K ≃ K') (h : ∀ k, ι k = ι' (ε k))
    (Ω : Type) [Field Ω] (y : (Σ k', ι' k') → Ω) (a : K' → ℤ),
    NefOnFibres (mCoordIdeal (y ∘ relabelBlocks ε h)) (a ∘ ε) ↔ NefOnFibres (mCoordIdeal y) a
section Inhabitants
def optionToSum (K : Type) : Option K ≃ K ⊕ Unit where
  toFun
    | none => Sum.inr ()
    | some k => Sum.inl k
  invFun
    | Sum.inl k => some k
    | Sum.inr () => none
  left_inv := by rintro (_ | k) <;> rfl
  right_inv := by rintro (k | ⟨⟩) <;> rfl
theorem optionToSum_idx {K : Type} (ι : K → Type) (κ : Type) :
    ∀ o, (fun o : Option K => Option.elim o κ ι) o =
      Sum.elim ι (fun _ : Unit => κ) (optionToSum K o) := by
  rintro (_ | k) <;> rfl
example : relabelBlocks (optionToSum Unit) (optionToSum_idx (fun _ : Unit => Fin 2) (Fin 2))
    ⟨none, (1 : Fin 2)⟩ = ⟨Sum.inr (), (1 : Fin 2)⟩ := rfl
end Inhabitants
end GroundTheory.Heights₂.Heights


