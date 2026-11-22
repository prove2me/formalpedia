-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_HaarTransversals_PoincareSeriesSquareIntegrable
-- name    : Formalism_LocalToGlobal_SiegelLatticeTheory_HaarTransversals_PoincareSeriesSquareIntegrable
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:30:08.089868+00:00
-- url     : https://prove2.me/theorems/2fd54c6d-63b7-4206-b58c-4ac9a8e603c4
-- title:
--   Poincare Series Square Integrable
-- statement:
--   Definitions and structural lemmas for Poincare Series Square Integrable, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/HaarTransversals/PoincareSeriesSquareIntegrable.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_HaarTransversals_FoldBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.dupNamespace false
noncomputable section
open MeasureTheory
open scoped ENNReal NNReal ComplexConjugate
namespace Formalism.L2.SG.PoincareSeriesSquareIntegrable
open Formalism.L2.SG.FoldBound
def IsFoldDatum {G : Type*} [Group G] [MeasurableSpace G] (μ : Measure G) (S : Subgroup G)
    (Ω : Set G) (a : ℝ≥0) (Ph : G → ℂ) : Prop :=
  Measurable Ph ∧ (∀ s ∈ S, ∀ y : G, Ph (s * y) = Ph y) ∧
    ∀ y : G, ‖Ph y‖ₑ ≤ (a : ℝ≥0∞) * ∫⁻ ω in Ω, ‖Ph (y * ω)‖ₑ ∂μ
def multiplicityLIntegral {G : Type*} [Group G] [MeasurableSpace G] (μ : Measure G) (Γ : Subgroup G)
    (Ω : Set G) (F : Set G) (Ph : G → ℂ) : ℝ≥0∞ :=
  ∫⁻ y in F, mult Γ Ω y * ‖Ph y‖ₑ ∂μ
def poinc {G : Type*} [Group G] (D : Set G) (Ph : G → ℂ) (x : G) : ℂ :=
  ∑' δ : D, Ph ((δ : G) * x)
def stab {G : Type*} [Group G] (S S' : Subgroup G) (γ : G) : Subgroup G :=
  S ⊓ S'.comap (MulAut.conj γ⁻¹).toMonoidHom
def IsDoubleTransversal {G : Type*} [Group G] (Γ S S' : Subgroup G) (R : Set G) : Prop :=
  R ⊆ (Γ : Set G) ∧
    ∀ γ ∈ Γ, ∃! r : R, ∃ s ∈ S, ∃ s' ∈ S', s * (r : G) * s' = γ
def PoincareSeriesFinite (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G]
    [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] : Prop :=
  ∀ (Γ S : Subgroup G), DiscreteTopology Γ → S ≤ Γ →
  ∀ (Ω : Set G), IsCompact Ω → (1 : G) ∈ Ω →
  ∀ (a : ℝ≥0) (Ph : G → ℂ), IsFoldDatum μ S Ω a Ph →
  ∀ (F : Set G), IsFundamentalDomain S F μ → multiplicityLIntegral μ Γ Ω F Ph < ⊤ →
  ∀ (D : Set G), IsRightTransversal Γ S D →
  ∀ x : G, (∑' δ : D, ‖Ph ((δ : G) * x)‖ₑ) < ⊤
def PoincareSeriesMemLp (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G]
    [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] : Prop :=
  ∀ (Γ S : Subgroup G), DiscreteTopology Γ → S ≤ Γ →
  ∀ (Ω : Set G), IsCompact Ω → (1 : G) ∈ Ω →
  ∀ (a : ℝ≥0) (Ph : G → ℂ), IsFoldDatum μ S Ω a Ph →
  ∀ (F : Set G), IsFundamentalDomain S F μ → multiplicityLIntegral μ Γ Ω F Ph < ⊤ →
  ∀ (D : Set G), IsRightTransversal Γ S D →
  ∀ (FΓ : Set G), IsFundamentalDomain Γ FΓ μ →
    MemLp (poinc D Ph) 2 (μ.restrict FΓ) ∧
    (∫⁻ x in FΓ, ‖poinc D Ph x‖ₑ ^ 2 ∂μ) ≤ (a : ℝ≥0∞) * quotientLIntegral μ F Ph * multiplicityLIntegral μ Γ Ω F Ph ∧
    (a : ℝ≥0∞) * quotientLIntegral μ F Ph * multiplicityLIntegral μ Γ Ω F Ph ≤ (a : ℝ≥0∞) * multiplicityLIntegral μ Γ Ω F Ph ^ 2
def PoincareSeriesInner (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G]
    [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] : Prop :=
  ∀ (Γ S S' : Subgroup G), DiscreteTopology Γ → S ≤ Γ → S' ≤ Γ →
  ∀ (Ω : Set G), IsCompact Ω → (1 : G) ∈ Ω →
  ∀ (a a' : ℝ≥0) (Ph Ph' : G → ℂ), IsFoldDatum μ S Ω a Ph → IsFoldDatum μ S' Ω a' Ph' →
  ∀ (F F' : Set G), IsFundamentalDomain S F μ → IsFundamentalDomain S' F' μ →
    multiplicityLIntegral μ Γ Ω F Ph < ⊤ → multiplicityLIntegral μ Γ Ω F' Ph' < ⊤ →
  ∀ (D D' : Set G), IsRightTransversal Γ S D → IsRightTransversal Γ S' D' →
  ∀ (R : Set G), IsDoubleTransversal Γ S S' R →
  ∀ (Fs : G → Set G), (∀ r ∈ R, IsFundamentalDomain (stab S S' r) (Fs r) μ) →
  ∀ (FΓ : Set G), IsFundamentalDomain Γ FΓ μ →
    (∫⁻ x in F', ‖Ph' x‖ₑ * ∑' δ : D, ‖Ph ((δ : G) * x)‖ₑ ∂μ)
        ≤ (a : ℝ≥0∞) * quotientLIntegral μ F Ph * multiplicityLIntegral μ Γ Ω F' Ph' ∧
    (∑' r : R, ∫⁻ x in Fs r, ‖Ph x‖ₑ * ‖Ph' ((r : G)⁻¹ * x)‖ₑ ∂μ) < ⊤ ∧
    (∀ r ∈ R, IntegrableOn (fun x => Ph x * conj (Ph' (r⁻¹ * x))) (Fs r) μ) ∧
    IntegrableOn (fun x => poinc D Ph x * conj (poinc D' Ph' x)) FΓ μ ∧
    (∫ x in FΓ, poinc D Ph x * conj (poinc D' Ph' x) ∂μ)
      = ∑' r : R, ∫ x in Fs r, Ph x * conj (Ph' ((r : G)⁻¹ * x)) ∂μ
def PoincareSeriesSquareIntegrable (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G]
    [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] : Prop :=
  PoincareSeriesFinite G μ ∧ PoincareSeriesMemLp G μ ∧ PoincareSeriesInner G μ
end Formalism.L2.SG.PoincareSeriesSquareIntegrable


