-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsBlowUpFibreDegreeCut
-- name    : GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsBlowUpFibreDegreeCut
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:08:03.896793+00:00
-- url     : https://prove2.me/theorems/092d2e19-9c72-46fb-b462-fb2970fb666c
-- title:
--   Statements Blow Up Fibre Degree Cut
-- statement:
--   Definitions and structural lemmas for Statements Blow Up Fibre Degree Cut, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/StatementsBlowUpFibreDegreeCut.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsBlowUpFibreDegree
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
variable {K : Type*} [DecidableEq K] {ι : K → Type*} {R : Type*} [CommRing R]
def homLocRing (P W : Ideal (MRing ι R)) [P.IsPrime] : Subring (FractionRing (MRing ι R ⧸ P)) :=
  Subring.closure {z | ∃ (b : K → ℕ) (f g : MRing ι R), IsMultiHomog f b ∧ IsMultiHomog g b ∧ g ∉ W ∧
    z = algebraMap (MRing ι R ⧸ P) (FractionRing (MRing ι R ⧸ P)) (Ideal.Quotient.mk P f) /
      algebraMap (MRing ι R ⧸ P) (FractionRing (MRing ι R ⧸ P)) (Ideal.Quotient.mk P g)}
end Objects
section Lemmas
def HomLocRingLocal.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (P : Ideal (MRing ι O)) (hP : IsMultiProjPrime P) (c : K → ℕ) (x : MRing ι O),
    IsMultiHomog x c → x ∉ P →
    ∀ W : Ideal (MRing ι O), W ∈ (P ⊔ Ideal.span {x}).minimalPrimes → IsRelevant W →
      haveI := hP.isPrime
      IsLocalRing (homLocRing P W) ∧ IsNoetherianRing (homLocRing P W) ∧
        ringKrullDim (homLocRing P W) = 1
def DivCycleHomLoc.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (P : Ideal (MRing ι O)) (hP : IsMultiProjPrime P) (c : K → ℕ) (x : MRing ι O),
    IsMultiHomog x c → x ∉ P →
    ∀ (W : Ideal (MRing ι O)) (hW : W ∈ (P ⊔ Ideal.span {x}).minimalPrimes), IsRelevant W →
    ∀ g : MRing ι O, IsMultiHomog g c → g ∉ W →
      haveI := hP.isPrime
      ∀ hz : algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (Ideal.Quotient.mk P x) /
          algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (Ideal.Quotient.mk P g) ∈
            homLocRing P W,
      haveI : W.IsPrime := hW.1.1
      multAt (P ⊔ Ideal.span {x}) W =
        Module.length (homLocRing P W) (homLocRing P W ⧸ Ideal.span {(⟨_, hz⟩ : homLocRing P W)})
def FiniteBirationalLength.Statement : Prop :=
  ∀ (A B : Type u) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [CommRing B]
    [IsDomain B] [Algebra A B] [Module.Finite A B], ringKrullDim A = 1 →
    Function.Injective (algebraMap A B) → Module.finrank A B = 1 → ∀ z : A, z ≠ 0 →
      Finite {𝔫 : Ideal B // 𝔫.IsMaximal} ∧
      Module.length A (A ⧸ Ideal.span {z}) =
        ∑ᶠ 𝔫 : {𝔫 : Ideal B // 𝔫.IsMaximal},
          (haveI := 𝔫.2.isPrime
           Module.length (Localization.AtPrime 𝔫.1)
             (Localization.AtPrime 𝔫.1 ⧸
               Ideal.span {algebraMap B (Localization.AtPrime 𝔫.1) (algebraMap A B z)})) *
            (𝔫.1.inertiaDeg A : ℕ∞)
def BlowUpFibreSemilocal.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (J : Type) [Fintype J] (P : Ideal (MRing ι O)) (n : ℕ) (hP : IsModelOver P n),
    ∀ (N : K → ℕ) (u : J → MRing ι O), (∀ j, IsMultiHomog (u j) N) → (∃ j, u j ∉ P) →
    ∀ (c : K → ℕ) (x : MRing ι O), IsMultiHomog x c → x ∉ P →
    ∀ W : Ideal (MRing ι O), (C ϖ : MRing ι O) ∈ W → W ∈ (P ⊔ Ideal.span {x}).minimalPrimes →
      IsRelevant W →
    ∀ g : MRing ι O, IsMultiHomog g c → g ∉ W →
      haveI := hP.multiProj.isPrime
      ∀ hz : algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (Ideal.Quotient.mk P x) /
          algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (Ideal.Quotient.mk P g) ∈
            homLocRing P W,
      ∃ (B : Type u) (_ : CommRing B) (_ : IsDomain B) (_ : Algebra (homLocRing P W) B),
        Module.Finite (homLocRing P W) B ∧ Function.Injective (algebraMap (homLocRing P W) B) ∧
        Module.finrank (homLocRing P W) B = 1 ∧
        ∃ e : {𝔫 : Ideal B // 𝔫.IsMaximal} ≃ {W' : Ideal (MRing (extIdx ι J) O) //
            W' ∈ (blowUpOf P u ⊔ Ideal.span {liftForm x}).minimalPrimes ∧ IsRelevant W' ∧
              W'.comap (liftForm (ι := ι) (J := J) (R := O)) = W},
          ∀ 𝔫 : {𝔫 : Ideal B // 𝔫.IsMaximal},
            (haveI := 𝔫.2.isPrime
             Module.length (Localization.AtPrime 𝔫.1)
               (Localization.AtPrime 𝔫.1 ⧸ Ideal.span {algebraMap B (Localization.AtPrime 𝔫.1)
                 (algebraMap (homLocRing P W) B ⟨_, hz⟩)})) =
              ((divCycle (blowUpOf P u) (liftForm x) (e 𝔫).1).toNat : ℕ∞) ∧
            𝔫.1.inertiaDeg (homLocRing P W) = specialRelDeg (e 𝔫).1
end Lemmas
section Examples
end Examples
end
end GroundTheory.Heights₂.Heights.NumbersDVR


