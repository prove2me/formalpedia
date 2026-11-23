-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_KerPNonzero
-- name    : Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_KerPNonzero
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:10:01.031997+00:00
-- url     : https://prove2.me/theorems/709b9429-221f-44d5-b907-62a802e9eefa
-- title:
--   Ker PNonzero
-- statement:
--   Definitions and structural lemmas for Ker PNonzero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/QuadraticSemicharacters/KerPNonzero.lean

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_UnitaryConstant
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
open MeasureTheory
namespace Formalism.L2.Th1.H
section Objects
variable {V : Type*} [AddCommGroup V] [Module ℂ V]
def wt (H : Sesq V) (z : V) : ℝ := Real.exp (-Real.pi * (H z z).re)
def kerK (H : Sesq V) (w z : V) : ℂ := Complex.exp ((Real.pi : ℂ) * H z w)
def kerP (H : Sesq V) (α : V → ℂ) (Λ : AddSubgroup V) (z w : V) : ℂ :=
  ∑' x : Λ, α (x : V) * opU H (x : V) (kerK H w) z
def termT (H : Sesq V) (α : V → ℂ) (δ : V ≃ₗ[ℂ] V) (x z : V) : ℂ :=
  α x * opU H x (kerK H z) (δ.symm z) * (wt H z : ℂ)
def gq (H : Sesq V) (Ae : V ≃ₗ[ℂ] V) (z : V) : ℂ := Complex.exp (-(Real.pi : ℂ) * H (Ae z) z)
end Objects
def DiagTerm : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (H : Sesq V), IsHerm H → ∀ v z : V,
    opU H v (kerK H z) z * (wt H z : ℂ)
      = Complex.exp (-(Real.pi : ℂ) * H v v / 2) * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (altE H v z : ℂ))
def TermShift : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (H : Sesq V), IsHerm H → ∀ (α : V → ℂ) (δ Ae : V ≃ₗ[ℂ] V),
    IsIsom H H (δ : V →ₗ[ℂ] V) → (∀ x, Ae x = x - δ.symm x) →
    (∀ x z, termT H α δ x z = phiC H α Ae x * gq H Ae (z - Ae.symm x)) ∧
    ∀ z, ‖gq H Ae z‖ = Real.exp (-(Real.pi / 2) * (H (Ae z) (Ae z)).re)
def FormNorm : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] (H : Sesq V), IsHerm H →
    IsPosDef H → ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ z, c * ‖z‖ ^ 2 ≤ (H z z).re ∧ (H z z).re ≤ C * ‖z‖ ^ 2
def LatGaussSummable : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] (Λ : AddSubgroup V),
    IsLat Λ → ∀ c r : ℝ, 0 < c → ∃ u : Λ → ℝ, Summable u ∧
      ∀ (x : Λ) (z₀ : V), ‖z₀‖ ≤ r → Real.exp (-c * ‖(x : V) - z₀‖ ^ 2) ≤ u x
def GaussIntegrable : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] [MeasurableSpace V]
    [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (H : Sesq V), IsHerm H → IsPosDef H →
    ∀ c : ℝ, 0 < c → Integrable (fun z => Real.exp (-c * (H z z).re)) μ ∧
      0 < ∫ z, Real.exp (-c * (H z z).re) ∂μ
def ExpSeriesEntire : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (X : Type) (c : X → ℂ) (ℓ : X → V →L[ℂ] ℂ),
    (∀ r : ℝ, Summable fun x => ‖c x‖ * Real.exp (r * ‖ℓ x‖)) →
    AnalyticOnNhd ℂ (fun z => ∑' x, c x * Complex.exp (ℓ x z)) Set.univ
def KerPTh : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] (H : Sesq V)
    (Λ : AddSubgroup V) (α : V → ℂ), IsHerm H → IsPosDef H → IsLat Λ → IsSemiChar H Λ α →
    ∀ w : V, (∀ z, Summable fun x : Λ => α (x : V) * opU H (x : V) (kerK H w) z) ∧
      (fun z => kerP H α Λ z w) ∈ Th H α Λ
def FundDomain : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] [MeasurableSpace V]
    [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (Λ : AddSubgroup V), IsLat Λ →
    ∃ D : Set V, IsAddFundamentalDomain Λ D μ ∧ Bornology.IsBounded D ∧ 0 < (μ D).toReal ∧
      ∀ Λ' : AddSubgroup V, Λ' ≤ Λ → relIdx Λ' Λ ≠ 0 →
        ∃ D' : Set V, IsAddFundamentalDomain Λ' D' μ ∧ Bornology.IsBounded D' ∧
          (μ D').toReal = relIdx Λ' Λ * (μ D).toReal
def CharIntegral : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] [MeasurableSpace V]
    [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (H : Sesq V), IsHerm H → IsPosDef H →
    ∀ (Λ' : AddSubgroup V) (D' : Set V), IsAddFundamentalDomain Λ' D' μ → ∀ v ∈ dualLat H Λ', v ≠ 0 →
      ∫ z in D', Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (altE H v z : ℂ)) ∂μ = 0
def GaussQuad : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] [MeasurableSpace V]
    [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (H : Sesq V), IsHerm H → IsPosDef H →
    ∀ δ Ae : V ≃ₗ[ℂ] V, IsIsom H H (δ : V →ₗ[ℂ] V) → (∀ x, Ae x = x - δ.symm x) →
    Integrable (gq H Ae) μ ∧
    ∫ z, gq H Ae z ∂μ = ((∫ z, wt H z ∂μ : ℝ) : ℂ) / LinearMap.det (Ae : V →ₗ[ℂ] V)
def DiagIntegral : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] [MeasurableSpace V]
    [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (H : Sesq V) (Λ Λ₂ : AddSubgroup V) (α : V → ℂ),
    IsHerm H → IsPosDef H → IsLat Λ → IsSelfDual H Λ → IsSelfDual H Λ₂ → IsSemiChar H Λ α →
    IsSemiChar H Λ₂ α → ∀ D' : Set V, IsAddFundamentalDomain (Λ ⊓ Λ₂ : AddSubgroup V) D' μ →
    Bornology.IsBounded D' → ∀ y ∈ Λ₂,
      ∫ z in D', α y * opU H y (fun v => kerP H α Λ v z) z * (wt H z : ℂ) ∂μ
        = by classical exact if y ∈ Λ then ((μ D').toReal : ℂ) else 0
def UnfoldIntegral : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] [MeasurableSpace V]
    [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (H : Sesq V) (Λ : AddSubgroup V) (α : V → ℂ)
    (δ Ae : V ≃ₗ[ℂ] V), IsLat Λ → UnitaryData H Λ α δ Ae → ∀ D' : Set V,
    IsAddFundamentalDomain (Λ ⊓ imgLat (δ : V →ₗ[ℂ] V) Λ : AddSubgroup V) D' μ → Bornology.IsBounded D' →
    ∀ S : Finset V, IsReps (latA Λ δ Ae) Λ S →
      ∫ z in D', kerP H α Λ (δ.symm z) z * (wt H z : ℂ) ∂μ = (∑ x ∈ S, phiC H α Ae x) * ∫ z, gq H Ae z ∂μ
def SelfDualCovolume : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] [MeasurableSpace V]
    [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (H : Sesq V) (Λ : AddSubgroup V) (α : V → ℂ),
    IsHerm H → IsPosDef H → IsLat Λ → IsSelfDual H Λ → IsSemiChar H Λ α → AtMostLine H α Λ →
    ∀ D : Set V, IsAddFundamentalDomain Λ D μ → Bornology.IsBounded D → (μ D).toReal = ∫ z, wt H z ∂μ
def KerPNonzero : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] (H : Sesq V)
    (Λ : AddSubgroup V) (α : V → ℂ), IsHerm H → IsPosDef H → IsLat Λ → IsSelfDual H Λ → IsSemiChar H Λ α →
    ∃ w z : V, kerP H α Λ z w ≠ 0
end Formalism.L2.Th1.H


