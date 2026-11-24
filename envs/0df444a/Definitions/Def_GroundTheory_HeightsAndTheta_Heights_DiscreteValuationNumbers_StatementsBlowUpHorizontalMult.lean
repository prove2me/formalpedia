-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsBlowUpHorizontalMult
-- name    : GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsBlowUpHorizontalMult
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:50:37.446294+00:00
-- url     : https://prove2.me/theorems/ba8684cf-536f-460e-bd46-8dbcb1116364
-- title:
--   Statements Blow Up Horizontal Mult
-- statement:
--   Definitions and structural lemmas for Statements Blow Up Horizontal Mult, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/StatementsBlowUpHorizontalMult.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsBlowUpHorizontal
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
def BlowUpHorizontalMinimal.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (J : Type) [Fintype J] (P : Ideal (MRing ι O)) (n : ℕ), IsModelOver P n →
    ∀ (N : K → ℕ) (u : J → MRing ι O), (∀ j, IsMultiHomog (u j) N) → (∃ j, u j ∉ P) →
    (∀ W : Ideal (MRing ι O), W.IsPrime → P ≤ W → IsRelevant W → (C ϖ : MRing ι O) ∉ W →
      ∃ j, ∀ j', ∃ v w : MRing ι O, v ∉ W ∧ v * u j' - w * u j ∈ P) →
    ∀ (c : K → ℕ) (x : MRing ι O), IsMultiHomog x c → x ∉ P →
    ∀ W : Ideal (MRing (extIdx ι J) O), divCycle (blowUpOf P u) (liftForm x) W ≠ 0 →
      (C ϖ : MRing (extIdx ι J) O) ∉ W →
      W.comap (liftForm (ι := ι) (J := J) (R := O)) ∈ (P ⊔ Ideal.span {x}).minimalPrimes
def BlowUpHorizontalChartLength.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (J : Type) [Fintype J] (P : Ideal (MRing ι O)) (n : ℕ), IsModelOver P n →
    ∀ (N : K → ℕ) (u : J → MRing ι O), (∀ j, IsMultiHomog (u j) N) → (∃ j, u j ∉ P) →
    (∀ W : Ideal (MRing ι O), W.IsPrime → P ≤ W → IsRelevant W → (C ϖ : MRing ι O) ∉ W →
      ∃ j, ∀ j', ∃ v w : MRing ι O, v ∉ W ∧ v * u j' - w * u j ∈ P) →
    ∀ (c : K → ℕ) (x : MRing ι O), IsMultiHomog x c → x ∉ P →
    ∀ W : Ideal (MRing (extIdx ι J) O), divCycle (blowUpOf P u) (liftForm x) W ≠ 0 →
      (C ϖ : MRing (extIdx ι J) O) ∉ W →
      ∀ hW : W.IsPrime,
      haveI := hW
      multAt (blowUpOf P u ⊔ Ideal.span {liftForm x}) W =
        Module.length
          (Localization.AtPrime ((W.comap (liftForm (ι := ι) (J := J) (R := O))).map
            (Polynomial.C : MRing ι O →+* Polynomial (MRing ι O))))
          (LocalizedModule ((W.comap (liftForm (ι := ι) (J := J) (R := O))).map
              (Polynomial.C : MRing ι O →+* Polynomial (MRing ι O))).primeCompl
            (Polynomial (MRing ι O) ⧸
              (P ⊔ Ideal.span {x}).map (Polynomial.C : MRing ι O →+* Polynomial (MRing ι O))))
def PolynomialLocalizedLength.Statement : Prop :=
  ∀ (R : Type u) [CommRing R] (q : Ideal R) [q.IsPrime] (I : Ideal R),
    Module.length (Localization.AtPrime (q.map (Polynomial.C : R →+* Polynomial R)))
        (LocalizedModule (q.map (Polynomial.C : R →+* Polynomial R)).primeCompl
          (Polynomial R ⧸ I.map (Polynomial.C : R →+* Polynomial R))) =
      Module.length (Localization.AtPrime q) (LocalizedModule q.primeCompl (R ⧸ I))
end Lemmas
section Examples
end Examples
end
end GroundTheory.Heights₂.Heights.NumbersDVR


