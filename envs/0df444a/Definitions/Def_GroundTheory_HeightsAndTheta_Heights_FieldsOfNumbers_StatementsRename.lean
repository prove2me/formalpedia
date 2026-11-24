-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsRename
-- name    : GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsRename
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:20:07.66124+00:00
-- url     : https://prove2.me/theorems/02846a4f-910e-4635-9c92-d40724a6e16c
-- title:
--   Statements Rename
-- statement:
--   Definitions and structural lemmas for Statements Rename, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/StatementsRename.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
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
section Split
variable {K K' : Type}
abbrev blockCompl (j : K ↪ K') : Type := {k' : K' // k' ∉ Set.range j}
abbrev splitCoord (j : K ↪ K') (ι' : K' → Type) : K ⊕ blockCompl j → Type :=
  Sum.elim (fun k => ι' (j k)) (fun l => ι' l.1)
def splitVar (j : K ↪ K') (ι' : K' → Type) : (Σ s, splitCoord j ι' s) → (Σ k', ι' k')
  | ⟨Sum.inl k, i⟩ => ⟨j k, i⟩
  | ⟨Sum.inr l, i⟩ => ⟨l.1, i⟩
def splitPrime {F : Type u} [Field F] (j : K ↪ K') {ι' : K' → Type} (P' : Ideal (MRing ι' F)) :
    Ideal (MRing (splitCoord j ι') F) :=
  P'.comap (rename (splitVar j ι'))
instance splitPrime.isPrime {F : Type u} [Field F] (j : K ↪ K') {ι' : K' → Type}
    (P' : Ideal (MRing ι' F)) [P'.IsPrime] : (splitPrime j P').IsPrime :=
  Ideal.comap_isPrime _ _
end Split
def RenameMultiHomog.Statement : Prop :=
  ∀ (R : Type u) [CommRing R] (K K' : Type) [DecidableEq K] [DecidableEq K'] (j : K ↪ K')
    (ι : K → Type) (ι' : K' → Type) (g : (Σ k, ι k) → (Σ k', ι' k')), (∀ v, (g v).1 = j v.1) →
    ∀ (f : MRing ι R) (d : K → ℕ), IsMultiHomog f d →
      IsMultiHomog (rename g f) (Function.extend j d 0)
def RenameHilbFn.Statement : Prop :=
  ∀ (F : Type u) [Field F] (S K' : Type) [DecidableEq S] [DecidableEq K'] (κ : S → Type)
    (ι' : K' → Type) (E : S ≃ K') (σ : (Σ s, κ s) ≃ (Σ k', ι' k')), (∀ v, (σ v).1 = E v.1) →
    ∀ (P : Ideal (MRing ι' F)) (m : S → ℤ),
      hilbFn (P.comap (rename σ)) m = hilbFn P (m ∘ E.symm)
def RenameIntNum.Statement : Prop :=
  ∀ (F : Type u) [Field F] (S K' : Type) [DecidableEq S] [DecidableEq K'] (κ : S → Type)
    (ι' : K' → Type) (E : S ≃ K') (σ : (Σ s, κ s) ≃ (Σ k', ι' k')), (∀ v, (σ v).1 = E v.1) →
    ∀ (P : Ideal (MRing ι' F)) (n : ℕ) (bs : Fin n → S → ℤ),
      intNum F (P.comap (rename σ)) bs = intNum F P (fun i => bs i ∘ E.symm)
def RenameMultiProjPrime.Statement : Prop :=
  ∀ (R : Type u) [CommRing R] (S K' : Type) [DecidableEq S] [DecidableEq K'] (κ : S → Type)
    (ι' : K' → Type) (E : S ≃ K') (σ : (Σ s, κ s) ≃ (Σ k', ι' k')), (∀ v, (σ v).1 = E v.1) →
    ∀ P : Ideal (MRing ι' R), IsMultiProjPrime P → IsMultiProjPrime (P.comap (rename σ))
def SplitRelDeg.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K K' : Type) [DecidableEq K] [DecidableEq K'] (j : K ↪ K')
    (ι' : K' → Type) (P' : Ideal (MRing ι' F)) [P'.IsPrime],
      relDeg j P' = relDeg (Function.Embedding.inl : K ↪ K ⊕ blockCompl j) (splitPrime j P')
abbrev swapVar : (Σ _ : Bool, Fin 2) ≃ (Σ _ : Bool, Fin 2) :=
  Equiv.sigmaCongrLeft (β := fun _ : Bool => Fin 2) (Equiv.swap true false)
end
end GroundTheory.Heights₂.Heights.FieldNumbers


