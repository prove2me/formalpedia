-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_DivisorIdealBotUniformiser
-- name    : GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_DivisorIdealBotUniformiser
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:45:02.984922+00:00
-- url     : https://prove2.me/theorems/245c5416-2875-438c-bf3d-55c3e1b826de
-- title:
--   Divisor Ideal Bot Uniformiser
-- statement:
--   Definitions and structural lemmas for Divisor Ideal Bot Uniformiser, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/DivisorIdealBotUniformiser.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_SpanTwoIsPrimeRelevant
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSpecialQuotDim
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
section Defs
variable {K : Type*} {ι : K → Type*} {R : Type*} [CommRing R]
def divisorIdeal (P : Ideal (MRing ι R)) (f g : MRing ι R) : Ideal (MRing ι R) :=
  (P ⊔ Ideal.span {f}).colon {g}
end Defs
section Lemmas
def VNumCut.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (G : Ideal (MRing ι O)) (n : ℕ), G.IsPrime → IsMultiHomogIdeal G → (C ϖ : MRing ι O) ∈ G →
    ringKrullDim (MRing ι O ⧸ G) < ((n + 2 + Fintype.card K : ℕ) : WithBot ℕ∞) →
    ∀ (s : MRing ι O) (c : K → ℕ), IsMultiHomog s c → s ∉ G →
    ∀ bs : Fin n → K → ℤ,
      vNum G (Matrix.vecCons (fun k => (c k : ℤ)) bs) = cycEval (fun U => vNum U bs) (divCycle G s)
def DivisorIdealCycle.Statement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] (K : Type) [Fintype K] [DecidableEq K]
    (ι : K → Type) [∀ k, Fintype (ι k)] (P W : Ideal (MRing ι R)) (f g u v : MRing ι R),
    P.IsPrime → W.IsPrime → P ≤ W → g ∉ P →
    (∀ U : Ideal (MRing ι R), U.IsPrime → W ≤ U → IsRelevant U →
      ∃ u' v' : MRing ι R, u' ∉ U ∧ u' * f - v' * g ∈ P) →
    u ∉ W → v ∉ W → u * f - v * g ∈ P →
    ratDiv W v u = idealCycle (W ⊔ divisorIdeal P f g)
def VertCutEff.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (P : Ideal (MRing ι O)) (n : ℕ), IsModelOver P (n + 1) →
    ∀ (b : K → ℤ) (f g : MRing ι O), IsEffectiveVertical P ϖ b f g →
    ∀ (W : Ideal (MRing ι O)) (x : MRing ι O), x ∉ P → W ∈ (P ⊔ Ideal.span {x}).minimalPrimes →
      IsRelevant W → IsMultiHomogIdeal W → (C ϖ : MRing ι O) ∈ W → ratDiv P f g W = 0 →
    ∀ L : Fin n → K → ℤ,
      vNum W (Matrix.vecCons b L) =
        cycEval (fun U => vNum U L) (idealCycle (W ⊔ divisorIdeal P f g))
def LeftExpansion.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (P : Ideal (MRing ι O)) (d : ℕ), IsModelOver P (d + 1) →
    ∀ (b : K → ℤ) (f g : MRing ι O), IsVerticalDivisor P ϖ b f g →
    ∀ (c : K → ℕ) (s : MRing ι O), IsMultiHomog s c → s ∉ P →
    (∀ G, (C ϖ : MRing ι O) ∈ G → divCycle P s G ≠ 0 → ratDiv P f g G = 0) →
    ∀ L : Fin d → K → ℤ,
      cycEval (fun G => vNum G (Matrix.vecCons (fun k => (c k : ℤ)) L)) (ratDiv P f g) =
        cycEval (fun U => vNum U L) (fun U => cycEval (fun G => divCycle G s U) (ratDiv P f g))
open Classical in

def RightExpansion.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (P : Ideal (MRing ι O)) (d : ℕ), IsModelOver P (d + 1) →
    ∀ (b : K → ℤ) (f g : MRing ι O), IsEffectiveVertical P ϖ b f g →
    ∀ (c : K → ℕ) (s : MRing ι O), IsMultiHomog s c → s ∉ P →
    (∀ H, divCycle P s H ≠ 0 → (C ϖ : MRing ι O) ∉ H → IsVerticalDivisor H ϖ b f g) →
    (∀ G, (C ϖ : MRing ι O) ∈ G → divCycle P s G ≠ 0 → ratDiv P f g G = 0) →
    ∀ L : Fin d → K → ℤ,
      cycEval (fun W => if (C ϖ : MRing ι O) ∈ W then vNum W (Matrix.vecCons b L)
          else cycEval (fun G => vNum G L) (ratDiv W f g)) (divCycle P s) =
        cycEval (fun U => vNum U L)
          (fun U => cycEval (fun W => idealCycle (W ⊔ divisorIdeal P f g) U) (divCycle P s))
def LocalCoefficient.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (P : Ideal (MRing ι O)) (d : ℕ), IsModelOver P (d + 1) →
    ∀ (b : K → ℤ) (f g : MRing ι O), IsEffectiveVertical P ϖ b f g →
    ∀ (c : K → ℕ) (s : MRing ι O), IsMultiHomog s c → s ∉ P →
    (∀ H, divCycle P s H ≠ 0 → (C ϖ : MRing ι O) ∉ H → IsVerticalDivisor H ϖ b f g) →
    (∀ G, (C ϖ : MRing ι O) ∈ G → divCycle P s G ≠ 0 → ratDiv P f g G = 0) →
    ∀ U : Ideal (MRing ι O),
      (U.IsPrime → IsMultiHomogIdeal U → IsRelevant U → (C ϖ : MRing ι O) ∈ U →
        ((d + Fintype.card K : ℕ) : WithBot ℕ∞) ≤ ringKrullDim (MRing ι O ⧸ U)) →
      cycEval (fun G => divCycle G s U) (ratDiv P f g) =
        cycEval (fun W => idealCycle (W ⊔ divisorIdeal P f g) U) (divCycle P s)
end Lemmas
section Examples
end Examples
end
end GroundTheory.Heights₂.Heights.NumbersDVR


