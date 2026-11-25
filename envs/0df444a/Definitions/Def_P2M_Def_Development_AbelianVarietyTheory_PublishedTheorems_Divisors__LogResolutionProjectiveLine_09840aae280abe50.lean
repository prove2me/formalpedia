-- Prove2me | Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__LogResolutionProjectiveLine_09840aae280abe50
-- name    : P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__LogResolutionProjectiveLine_09840aae280abe50
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T12:23:11.48658+00:00
-- url     : https://prove2.me/theorems/d5d087c7-d6a2-43bf-a45d-d317c3dc8a62
-- title:
--   Log Resolution Projective Line
-- statement:
--   Definitions and structural lemmas for Log Resolution Projective Line, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/Divisors₂/LogResolutionProjectiveLine.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffFubiniStudyRatioCompChart0
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PushAFinsumInter
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AnalyticLogResolution
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GlobalTheory
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.IndefiniteRowSideFullHecke.BoundaryPolynomialFunctions GlobalTheory.LogResInt
namespace Published
def AnalyticLogResolution : Prop :=
  ∀ (d : ℕ) (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas d X),
    IsProjective A →
  ∀ (Z : Set X) (n : ℕ), IsIrreducibleAnalytic A Z → (regularLocus A Z n).Nonempty →
  ∀ (q : ℕ) (L : Fin q → LocPot X) (t : Fin q → X → X → ℂ),
    (∀ i, IsPotential A (L i) ∧ IsSection A (L i) (t i) ∧ ∃ y ∈ Z, t i y y ≠ 0) →
  ∃ (Y : Type) (_ : TopologicalSpace Y) (_ : CompactSpace Y) (_ : T2Space Y) (B : FinHolAtlas n Y)
    (μ : Y → X) (_ : HoloMap B A μ) (S : Set X) (r : ℕ) (W : Fin r → Set Y) (e : Fin q → Fin r → ℕ)
    (J : Finset (Fin r)),
    IsProjective B ∧ Set.range μ = Z ∧ A.IsAnalyticSubset S ∧ Z \ S ⊆ regularLocus A Z n ∧
    Z ⊆ closure (Z \ S) ∧ Set.InjOn μ (μ ⁻¹' S)ᶜ ∧
    (∀ y, y ∉ μ ⁻¹' S → ∀ j, y ∈ (B.chart j).source → ∀ v : Fin n → ℂ,
      fderiv ℂ (fun w => A.chart (chartIdx A (μ y)) (μ ((B.chart j).symm w))) (B.chart j y) v = 0 →
        v = 0) ∧
    μ ⁻¹' S = ⋃ k ∈ J, W k ∧ IsJointSNC B μ L t W e
end Published
namespace AnLogRes
variable {d : ℕ} {X : Type} [TopologicalSpace X]
end AnLogRes
end GlobalTheory


