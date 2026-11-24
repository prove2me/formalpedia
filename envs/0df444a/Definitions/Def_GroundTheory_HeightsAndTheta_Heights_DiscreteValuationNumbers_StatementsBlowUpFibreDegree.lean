-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsBlowUpFibreDegree
-- name    : GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsBlowUpFibreDegree
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:46:55.456487+00:00
-- url     : https://prove2.me/theorems/f2ee1aec-ca89-4326-963e-3c778a6f6ad4
-- title:
--   Statements Blow Up Fibre Degree
-- statement:
--   Definitions and structural lemmas for Statements Blow Up Fibre Degree, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/StatementsBlowUpFibreDegree.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsBlowUpVerticalFibre
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
namespace GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
noncomputable section
universe u
section Objects
variable {K : Type} [DecidableEq K] {ι : K → Type} {J : Type}
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
open Classical in

def specialRelDeg (W' : Ideal (MRing (extIdx ι J) O)) : ℕ :=
  if h : (specialIdeal W').IsPrime then
    haveI := h
    FieldNumbers.relDeg Function.Embedding.some (specialIdeal W')
  else 0
end Objects
section Lemmas
def BlowUpFibreDegree.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (J : Type) [Fintype J] (P : Ideal (MRing ι O)) (n : ℕ), IsModelOver P n →
    ∀ (N : K → ℕ) (u : J → MRing ι O), (∀ j, IsMultiHomog (u j) N) → (∃ j, u j ∉ P) →
    ∀ (c : K → ℕ) (x : MRing ι O), IsMultiHomog x c → x ∉ P →
    ∀ W : Ideal (MRing ι O), (C ϖ : MRing ι O) ∈ W → divCycle P x W ≠ 0 →
      (open Classical in
        ∑ᶠ W' : Ideal (MRing (extIdx ι J) O),
          if W'.comap (liftForm (ι := ι) (J := J) (R := O)) = W then
            divCycle (blowUpOf P u) (liftForm x) W' * (specialRelDeg W' : ℤ)
          else 0) =
        divCycle P x W
end Lemmas
section Examples
end Examples
end
end GroundTheory.Heights₂.Heights.NumbersDVR


