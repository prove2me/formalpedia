-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsBlowUpVerticalFibre
-- name    : GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsBlowUpVerticalFibre
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:40:55.110055+00:00
-- url     : https://prove2.me/theorems/ef2ee7dd-f0b2-4473-b484-ea7b9bbeaaa0
-- title:
--   Statements Blow Up Vertical Fibre
-- statement:
--   Definitions and structural lemmas for Statements Blow Up Vertical Fibre, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/StatementsBlowUpVerticalFibre.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_BlowUpPushHypothesesExample
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
universe u
section Lemmas
def BlowUpVerticalFibre.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (J : Type) [Fintype J] (P : Ideal (MRing ι O)) (n : ℕ), IsModelOver P n →
    ∀ (N : K → ℕ) (u : J → MRing ι O), (∀ j, IsMultiHomog (u j) N) → (∃ j, u j ∉ P) →
    ∀ (c : K → ℕ) (x : MRing ι O), IsMultiHomog x c → x ∉ P →
    ∀ (a : Fin n → K → ℤ) (W : Ideal (MRing ι O)), (C ϖ : MRing ι O) ∈ W →
      (open Classical in
        ∑ᶠ W' : Ideal (MRing (extIdx ι J) O),
          if W'.comap (liftForm (ι := ι) (J := J) (R := O)) = W then
            divCycle (blowUpOf P u) (liftForm x) W' * vNum W' (liftDegs a)
          else 0) =
        divCycle P x W * vNum W a
end Lemmas
section Examples
end Examples
end
end GroundTheory.Heights₂.Heights.NumbersDVR


