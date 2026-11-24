-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_LocalizedQuotientIsSimpleModuleOfMul
-- name    : GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_LocalizedQuotientIsSimpleModuleOfMul
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:36:11.736007+00:00
-- url     : https://prove2.me/theorems/268d7919-08a5-42f4-bfbc-57f83ee6095e
-- title:
--   Localized Quotient Is Simple Module Of Mul
-- statement:
--   Definitions and structural lemmas for Localized Quotient Is Simple Module Of Mul, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/LocalizedQuotientIsSimpleModuleOfMul.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_CutIdentityRightSideCongrOfSubMem
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
def ResidualComparison.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (P : Ideal (MRing ι O)) (d : ℕ), IsModelOver P (d + 1) →
    ∀ (b : K → ℤ) (f g : MRing ι O), IsEffectiveVertical P ϖ b f g →
    ∀ (c : K → ℕ) (s : MRing ι O), IsMultiHomog s c → s ∉ P →
    (∀ H, divCycle P s H ≠ 0 → (C ϖ : MRing ι O) ∉ H → IsVerticalDivisor H ϖ b f g) →
    ∀ e : K → ℕ, (∀ k, (c k : ℤ) = b k + e k) →
    ∀ m : MRing ι O, IsMultiHomog m e → m ∉ P →
    (∀ H, divCycle P s H ≠ 0 → (C ϖ : MRing ι O) ∉ H → m ∉ H) →
    ∀ G' : Ideal (MRing (extIdx ι (BlowUpIdx ι)) O),
      (C ϖ : MRing (extIdx ι (BlowUpIdx ι)) O) ∈ G' →
      0 < divCycle (blowUpOf P (blowUpGens s g f m e)) (liftForm s) G' →
      0 < ratDiv (blowUpOf P (blowUpGens s g f m e)) (newVar (some none)) (liftForm m) G' →
      ∃ G : Ideal (MRing ι O), (C ϖ : MRing ι O) ∈ G ∧
        divCycle (blowUpOf P (blowUpGens s g f m e)) (liftForm s) G' ≤ divCycle P s G ∧
        divCycle (blowUpOf P (blowUpGens s g f m e)) (liftForm s) G' +
            ratDiv (blowUpOf P (blowUpGens s g f m e)) (newVar (some none)) (liftForm m) G' ≤
          ratDiv P f g G
def ExceptionalComparison.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (P : Ideal (MRing ι O)) (d : ℕ), IsModelOver P (d + 1) →
    ∀ (b : K → ℤ) (f g : MRing ι O), IsEffectiveVertical P ϖ b f g →
    ∀ (c : K → ℕ) (s : MRing ι O), IsMultiHomog s c → s ∉ P →
    (∀ H, divCycle P s H ≠ 0 → (C ϖ : MRing ι O) ∉ H → IsVerticalDivisor H ϖ b f g) →
    ∀ e : K → ℕ, (∀ k, (c k : ℤ) = b k + e k) →
    ∀ m : MRing ι O, IsMultiHomog m e → m ∉ P →
    (∀ H, divCycle P s H ≠ 0 → (C ϖ : MRing ι O) ∉ H → m ∉ H) →
    ∀ G' : Ideal (MRing (extIdx ι (BlowUpIdx ι)) O),
      (C ϖ : MRing (extIdx ι (BlowUpIdx ι)) O) ∈ G' →
      0 < divCycle (blowUpOf P (blowUpGens s g f m e)) (newVar none) G' →
      0 < ratDiv (blowUpOf P (blowUpGens s g f m e)) (liftForm (f * m))
        (liftForm g * newVar (some none)) G' →
      ∃ G : Ideal (MRing ι O), (C ϖ : MRing ι O) ∈ G ∧
        divCycle (blowUpOf P (blowUpGens s g f m e)) (newVar none) G' +
            ratDiv (blowUpOf P (blowUpGens s g f m e)) (liftForm (f * m))
              (liftForm g * newVar (some none)) G' ≤ divCycle P s G ∧
        ratDiv (blowUpOf P (blowUpGens s g f m e)) (liftForm (f * m))
            (liftForm g * newVar (some none)) G' ≤ ratDiv P f g G
end Lemmas
section Examples
section Simple
variable {A : Type*} [CommRing A]
end Simple
section Constants
set_option linter.unusedSectionVars false
variable {K : Type} {ι : K → Type} {J : Type} {O : Type*} [CommRing O] [IsDomain O]
def constChart (ϖ : O) (n : J → ℕ) (j₀ : J) : MRing (extIdx ι J) O →ₐ[O] MRing (extIdx ι J) O :=
  aeval fun v => match v with
    | ⟨none, j⟩ => C (ϖ ^ (n j - n j₀)) * X (⟨none, j₀⟩ : Σ o, extIdx ι J o)
    | ⟨some k, i⟩ => X ⟨some k, i⟩
def constChartPrime (ϖ : O) (n : J → ℕ) (j₀ : J) : Ideal (MRing (extIdx ι J) O) :=
  RingHom.ker ((MvPolynomial.map (Ideal.Quotient.mk (Ideal.span {ϖ}))).comp
    (constChart ϖ n j₀).toRingHom)
end Constants
end Examples
end
end GroundTheory.Heights₂.Heights.NumbersDVR


