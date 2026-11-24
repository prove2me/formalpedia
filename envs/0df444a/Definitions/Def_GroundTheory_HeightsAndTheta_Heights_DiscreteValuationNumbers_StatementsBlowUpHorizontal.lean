-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsBlowUpHorizontal
-- name    : GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsBlowUpHorizontal
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:48:35.501995+00:00
-- url     : https://prove2.me/theorems/ce4ae55e-ee30-4f63-986b-e0d39ba47e1b
-- title:
--   Statements Blow Up Horizontal
-- statement:
--   Definitions and structural lemmas for Statements Blow Up Horizontal, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/StatementsBlowUpHorizontal.lean

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
def BlowUpHorizontalSat.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (J : Type) [Fintype J] (P : Ideal (MRing ι O)) (n : ℕ), IsModelOver P n →
    ∀ (N : K → ℕ) (u : J → MRing ι O), (∀ j, IsMultiHomog (u j) N) → (∃ j, u j ∉ P) →
    (∀ W : Ideal (MRing ι O), W.IsPrime → P ≤ W → IsRelevant W → (C ϖ : MRing ι O) ∉ W →
      ∃ j, ∀ j', ∃ v w : MRing ι O, v ∉ W ∧ v * u j' - w * u j ∈ P) →
    ∀ (c : K → ℕ) (x : MRing ι O), IsMultiHomog x c → x ∉ P →
    ∀ W : Ideal (MRing (extIdx ι J) O), divCycle (blowUpOf P u) (liftForm x) W ≠ 0 →
      (C ϖ : MRing (extIdx ι J) O) ∉ W →
      ∀ F : MRing (extIdx ι J) O, F ∈ W ↔ ∃ s : MRing ι O, s ∉ W.comap (liftForm (ι := ι) (J := J) (R := O)) ∧
        (liftForm (ι := ι) (J := J) (R := O)) s * F ∈ blowUpOf P u ⊔ Ideal.map (liftForm (ι := ι) (J := J) (R := O)) (W.comap (liftForm (ι := ι) (J := J) (R := O)))
def BlowUpHorizontalMult.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (J : Type) [Fintype J] (P : Ideal (MRing ι O)) (n : ℕ), IsModelOver P n →
    ∀ (N : K → ℕ) (u : J → MRing ι O), (∀ j, IsMultiHomog (u j) N) → (∃ j, u j ∉ P) →
    (∀ W : Ideal (MRing ι O), W.IsPrime → P ≤ W → IsRelevant W → (C ϖ : MRing ι O) ∉ W →
      ∃ j, ∀ j', ∃ v w : MRing ι O, v ∉ W ∧ v * u j' - w * u j ∈ P) →
    ∀ (c : K → ℕ) (x : MRing ι O), IsMultiHomog x c → x ∉ P →
    ∀ W : Ideal (MRing (extIdx ι J) O), divCycle (blowUpOf P u) (liftForm x) W ≠ 0 →
      (C ϖ : MRing (extIdx ι J) O) ∉ W →
      divCycle P x (W.comap (liftForm (ι := ι) (J := J) (R := O))) = divCycle (blowUpOf P u) (liftForm x) W
def BlowUpHorizontalLift.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (J : Type) [Fintype J] (P : Ideal (MRing ι O)) (n : ℕ), IsModelOver P n →
    ∀ (N : K → ℕ) (u : J → MRing ι O), (∀ j, IsMultiHomog (u j) N) → (∃ j, u j ∉ P) →
    (∀ W : Ideal (MRing ι O), W.IsPrime → P ≤ W → IsRelevant W → (C ϖ : MRing ι O) ∉ W →
      ∃ j, ∀ j', ∃ v w : MRing ι O, v ∉ W ∧ v * u j' - w * u j ∈ P) →
    ∀ (c : K → ℕ) (x : MRing ι O), IsMultiHomog x c → x ∉ P →
    ∀ W : Ideal (MRing ι O), divCycle P x W ≠ 0 → (C ϖ : MRing ι O) ∉ W →
      ∃ W' : Ideal (MRing (extIdx ι J) O), divCycle (blowUpOf P u) (liftForm x) W' ≠ 0 ∧
        (C ϖ : MRing (extIdx ι J) O) ∉ W' ∧ W'.comap (liftForm (ι := ι) (J := J) (R := O)) = W
def BlowUpHorizontalStrict.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (J : Type) [Fintype J] (P : Ideal (MRing ι O)) (n : ℕ), IsModelOver P n →
    ∀ (N : K → ℕ) (u : J → MRing ι O), (∀ j, IsMultiHomog (u j) N) → (∃ j, u j ∉ P) →
    (∀ W : Ideal (MRing ι O), W.IsPrime → P ≤ W → IsRelevant W → (C ϖ : MRing ι O) ∉ W →
      ∃ j, ∀ j', ∃ v w : MRing ι O, v ∉ W ∧ v * u j' - w * u j ∈ P) →
    ∀ (c : K → ℕ) (x : MRing ι O), IsMultiHomog x c → x ∉ P →
    ∀ W : Ideal (MRing (extIdx ι J) O), divCycle (blowUpOf P u) (liftForm x) W ≠ 0 →
      (C ϖ : MRing (extIdx ι J) O) ∉ W →
      (∃ j, u j ∉ W.comap (liftForm (ι := ι) (J := J) (R := O))) → W = blowUpOf (W.comap (liftForm (ι := ι) (J := J) (R := O))) u
end Lemmas
section Examples
end Examples
end
end GroundTheory.Heights₂.Heights.NumbersDVR


