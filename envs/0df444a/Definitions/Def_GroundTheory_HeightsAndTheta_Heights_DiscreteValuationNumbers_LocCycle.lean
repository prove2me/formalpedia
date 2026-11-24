-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_LocCycle
-- name    : GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_LocCycle
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:47:17.395622+00:00
-- url     : https://prove2.me/theorems/3220889a-aee4-4d50-8f91-e0ec28374f4c
-- title:
--   Loc Cycle
-- statement:
--   Definitions and structural lemmas for Loc Cycle, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/LocCycle.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_DivisorIdealBotUniformiser
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
variable {R : Type*} [CommRing R]
open Classical in

def locCycle (J W : Ideal R) : ℤ :=
  if h : W ∈ J.minimalPrimes then
    haveI : W.IsPrime := h.1.1
    ((Module.length (Localization.AtPrime W) (LocalizedModule W.primeCompl (R ⧸ J))).toNat : ℤ)
  else 0
end Defs
section Lemmas
def LeftTermSupport.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O)
    (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (P : Ideal (MRing ι O)), IsMultiHomogIdeal P →
    ∀ (b : K → ℤ) (f g : MRing ι O), IsVerticalDivisor P ϖ b f g →
    ∀ (c : K → ℕ) (s : MRing ι O), IsMultiHomog s c →
    ∀ G U : Ideal (MRing ι O),
      ¬ (U.IsPrime ∧ IsMultiHomogIdeal U ∧ IsRelevant U ∧ (C ϖ : MRing ι O) ∈ U ∧ P ≤ U) →
      ratDiv P f g G * divCycle G s U = 0
def RightTermSupport.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O)
    (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (P : Ideal (MRing ι O)), IsMultiHomogIdeal P →
    ∀ (b : K → ℤ) (f g : MRing ι O), IsEffectiveVertical P ϖ b f g →
    ∀ (c : K → ℕ) (s : MRing ι O), IsMultiHomog s c →
    (∀ H, divCycle P s H ≠ 0 → (C ϖ : MRing ι O) ∉ H → IsVerticalDivisor H ϖ b f g) →
    ∀ W U : Ideal (MRing ι O),
      ¬ (U.IsPrime ∧ IsMultiHomogIdeal U ∧ IsRelevant U ∧ (C ϖ : MRing ι O) ∈ U ∧ P ≤ U) →
      divCycle P s W * idealCycle (W ⊔ divisorIdeal P f g) U = 0
def LocalCoeffRing.Statement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] (P U : Ideal R), P.IsPrime → U.IsPrime → P ≤ U →
    (∀ Q₁ Q₂ : Ideal R, Q₁.IsPrime → Q₂.IsPrime → P < Q₁ → Q₁ < Q₂ → Q₂ < U → False) →
    ∀ f g s u v : R, f ∉ P → g ∉ P → s ∉ P → u ∉ U → u * f - v * g ∈ P →
    (∀ W : Ideal R, W ≤ U → locCycle (P ⊔ Ideal.span {s}) W ≠ 0 →
      locCycle (P ⊔ Ideal.span {f}) W = locCycle (P ⊔ Ideal.span {g}) W) →
    ∑ᶠ G, (locCycle (P ⊔ Ideal.span {f}) G - locCycle (P ⊔ Ideal.span {g}) G) *
        locCycle (G ⊔ Ideal.span {s}) U =
      ∑ᶠ W, locCycle (P ⊔ Ideal.span {s}) W *
        locCycle (W ⊔ (P ⊔ Ideal.span {f}).colon {g}) U
end Lemmas
section Examples
end Examples
end
end GroundTheory.Heights₂.Heights.NumbersDVR


