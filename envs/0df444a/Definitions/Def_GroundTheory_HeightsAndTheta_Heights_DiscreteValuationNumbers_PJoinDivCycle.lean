-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PJoinDivCycle
-- name    : GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PJoinDivCycle
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T04:27:36.603214+00:00
-- url     : https://prove2.me/theorems/7be57298-af39-5726-bfc1-f39399e9c262
-- title:
--   PJoin Div Cycle
-- statement:
--   Definitions and structural lemmas for PJoin Div Cycle, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PJoinDivCycle.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsJoinDivCycle
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PPolynomialLocalizedLength
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PExistsUniqueRelabel
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
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (ptIdx liftVar)
noncomputable section
namespace JoinDivCycle
variable {R : Type} [CommRing R] {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
def joinIdxEquiv : (Σ k : K ⊕ Unit, Sum.elim ι ptIdx k) ≃ Option (Σ k, ι k) where
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
      have : i = (0 : Fin 1) := Subsingleton.elim (α := Fin 1) _ _
      subst this
      rfl
  right_inv := by
    rintro (_ | ⟨k, i⟩) <;> rfl
def joinPolyEquiv : MvPolynomial (Σ k : K ⊕ Unit, Sum.elim ι ptIdx k) R ≃+* Polynomial (MRing ι R) :=
  ((renameEquiv R (joinIdxEquiv (ι := ι))).trans (optionEquivLeft R (Σ k, ι k))).toRingEquiv
set_option hygiene false in

local notation "ψ" => joinPolyEquiv (R := R) (ι := ι)
set_option hygiene false in

local notation "ε" => rename (R := R) (liftVar (ι := ι) ptIdx)
end JoinDivCycle
end
end GroundTheory.Heights₂.Heights.NumbersDVR


