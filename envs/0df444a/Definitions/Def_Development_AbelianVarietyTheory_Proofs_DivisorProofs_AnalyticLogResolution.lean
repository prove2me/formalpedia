-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AnalyticLogResolution
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_AnalyticLogResolution
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:54:18.583803+00:00
-- url     : https://prove2.me/theorems/ba703103-e62b-4272-a3db-319fbc5a10b8
-- title:
--   Analytic Log Resolution
-- statement:
--   Definitions and structural lemmas for Analytic Log Resolution, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AnalyticLogResolution.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_BoundaryPolynomialFunctions
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GlobalTheory.LogResInt
open MeasureTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.IndefiniteRowSideFullHecke.BoundaryPolynomialFunctions
open scoped ENNReal
noncomputable section
variable {d n : ℕ} {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
def chartSumInt (B : FinHolAtlas n Y) (Φ : LocPot Y) (U : Set Y) (f : Y → ℝ≥0∞) : ℝ≥0∞ :=
  ∑ j, ∫⁻ w in (B.chart j).target ∩ (B.chart j).symm ⁻¹' U,
    f ((B.chart j).symm w) * ‖locDens B (fun _ => Φ) j w‖ₑ
def IsJointSNC (B : FinHolAtlas n Y) (μ : Y → X) {q r : ℕ} (L : Fin q → LocPot X)
    (t : Fin q → X → X → ℂ) (W : Fin r → Set Y) (e : Fin q → Fin r → ℕ) : Prop :=
  ∀ y, ∃ χ : OpenPartialHomeomorph Y (Fin n → ℂ), IsCompatChart B χ ∧ y ∈ χ.source ∧
    ∃ κ : Fin r → Option (Fin n), (∀ k k' a, κ k = some a → κ k' = some a → k = k') ∧
      (∀ k, W k ∩ χ.source = {w ∈ χ.source | ∃ a, κ k = some a ∧ χ w a = 0}) ∧
      ∀ i, χ.source ⊆ μ ⁻¹' (L i).U (μ y) ∧ ∃ u : Y → ℂ, B.HoloOn χ.source u ∧
        (∀ w ∈ χ.source, u w ≠ 0) ∧
        ∀ w ∈ χ.source, t i (μ y) (μ w) = u w * ∏ k, (match κ k with
          | some a => χ w a ^ e i k
          | none => 1)
def RankDropAlong (A : FinHolAtlas d X) (μ : Y → X) (B : FinHolAtlas n Y) (V : Set Y) : Prop :=
  ∀ w ∈ V, ∀ (χ : OpenPartialHomeomorph Y (Fin n → ℂ)) (a : Fin n), IsCompatChart B χ → w ∈ χ.source →
    V ∩ χ.source = {w' ∈ χ.source | χ w' a = 0} →
    Module.finrank ℂ (LinearMap.range
      (((fderiv ℂ (fun z => A.chart (chartIdx A (μ w)) (μ (χ.symm z))) (χ w) :
          (Fin n → ℂ) →L[ℂ] (Fin d → ℂ)) : (Fin n → ℂ) →ₗ[ℂ] (Fin d → ℂ)).comp
        (LinearMap.ker (LinearMap.proj a : (Fin n → ℂ) →ₗ[ℂ] ℂ)).subtype)) < n - 1
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
end
end GlobalTheory.LogResInt


