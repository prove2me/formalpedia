-- Prove2me | Definitions.Def_CompanionTheory_AutomorphicTheory_LocalBesselUniqueness_BesselModels_AtFormAdmOneOfSteps
-- name    : CompanionTheory_AutomorphicTheory_LocalBesselUniqueness_BesselModels_AtFormAdmOneOfSteps
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T02:37:45.306446+00:00
-- url     : https://prove2.me/theorems/13738688-cbdf-4d42-a1a8-d2c05d45e546
-- title:
--   At Form Adm One Of Steps
-- statement:
--   Definitions and structural lemmas for At Form Adm One Of Steps, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/LocalBesselUniqueness/BesselModels/AtFormAdmOneOfSteps.lean

import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_BesselOrbitConvolutions_BesselNonvanishingReduction
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_L2NormScaling
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix Finset
open scoped InnerProductSpace ENNReal NNReal ComplexConjugate
noncomputable section
set_option maxHeartbeats 1600000
namespace CompanionTheory.Lime.BM
open Formalism.FourierDecayAlt.ThreeDimData Formalism.FourierDecayAlt.P.DDSmoothness
def UniqGap : Prop :=
  ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (H : Type)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Mx k r → (H →L[ℂ] H))
    (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (u : Fin k → ℝ) (Wp : Type) [NormedAddCommGroup Wp]
    [InnerProductSpace ℂ Wp] (π : Mx k r → (Wp →L[ℂ] Wp)),
    1 ≤ k → Formalism.QuantumDeterminants.GapAtLeast ε lam h → 120 * ((2 * r + k + 1 : ℕ) : ℝ) ^ 3 ≤ h →
    Formalism.QuantumDeterminants.IsHCParam lam → PI.UpqRep.IsDSHpk k r ε lam σ → Formalism.QuantumDeterminants.inWb k r z → 0 < Formalism.QuantumDeterminants.Tz k r z →
    (∀ a, c a ≠ 0) → PI.UpqRep.IsHCTypeW k r z u π →
    ∀ B₁ B₂ : H → Wp,
      PI.BesselMapUniq.IsBesselMapSm (k := k) (r := r) z (PI.BesselMapUniq.psiGen k r z c) σ π B₁ →
      PI.BesselMapUniq.IsBesselMapSm (k := k) (r := r) z (PI.BesselMapUniq.psiGen k r z c) σ π B₂ →
      ∃ a b : ℂ, (a ≠ 0 ∨ b ≠ 0) ∧ ∀ v ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ, a • B₁ v + b • B₂ v = 0
def Shape : Prop :=
  CompanionTheory.D.Upq.BesselFunctionalConstruction.Inputs → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ) (h : ℝ)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mx k r → (H →L[ℂ] H)) (w0 : H)
    (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp]
    (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (u : Fin k → ℝ) (π : Mx k r → (Wp →L[ℂ] Wp))
    (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)),
    Side k r ε lam h σ w0 z c u π μW μN μG νq →
    (∃ x ∈ DDsp σ w0, ∃ y ∈ DDsp σ w0, be z c π σ μW μN x y ≠ 0) →
    ∃ l : H → Wp, PI.BesselMapUniq.IsBesselMapSm (k := k) (r := r) z (Formalism.QuantumDeterminants.psi k r z c) σ π l ∧
      (∃ x ∈ DDsp σ w0, l x ≠ 0) ∧
      ∀ x ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ, ∀ v ∈ DDsp σ w0, be z c π σ μW μN x v = (innerSL ℂ (l v)).smulRight (l x)
def DDFormOne : Prop :=
  CompanionTheory.D.Upq.BesselFunctionalConstruction.Inputs → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ) (h : ℝ)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mx k r → (H →L[ℂ] H)) (w0 : H)
    (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp]
    (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (u : Fin k → ℝ) (π : Mx k r → (Wp →L[ℂ] Wp))
    (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)),
    Side k r ε lam h σ w0 z c u π μW μN μG νq →
    DDForm z c π μW μN μG νq σ w0
def AtFormOne : Prop :=
  CompanionTheory.D.Upq.BesselFunctionalConstruction.Inputs → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ) (h : ℝ)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mx k r → (H →L[ℂ] H)) (w0 : H)
    (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp]
    (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (u : Fin k → ℝ) (π : Mx k r → (Wp →L[ℂ] Wp))
    (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)),
    Side k r ε lam h σ w0 z c u π μW μN μG νq →
    AtForm z c π μW μN μG νq σ
def AtFormAdmOne : Prop :=
  CompanionTheory.D.Upq.BesselFunctionalConstruction.Inputs → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ) (h : ℝ)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mx k r → (H →L[ℂ] H)) (w0 : H)
    (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp]
    (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (u : Fin k → ℝ) (π : Mx k r → (Wp →L[ℂ] Wp))
    (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)),
    Side k r ε lam h σ w0 z c u π μW μN μG νq →
    AtFormAdm z c π μW μN μG νq σ w0
def DDFormOneOfSteps : Prop :=
  PsiConst → SchurH → NormInv → GrowthS → GrowthG → CompanionTheory.D.Upq.BesselFunctionalConstruction.DecDD → CompanionTheory.D.Upq.BesselFunctionalConstruction.BeConv → CompanionTheory.D.Upq.BesselFunctionalConstruction.NormIdSm → CompanionTheory.D.Upq.BesselFunctionalConstruction.BeBessel → Shape → DDFormOne
def AtFormOneOfSteps : Prop :=
  SchurH → CompanionTheory.D.Upq.BesselFunctionalConstruction.BeConv → CompanionTheory.D.Upq.BesselFunctionalConstruction.NormIdSm → CompanionTheory.D.Upq.BesselFunctionalConstruction.BeBessel → Shape → CompanionTheory.D.Upq.BesselFunctionalConstruction.KFinForm → CompanionTheory.D.Upq.BesselFunctionalConstruction.ZeroCase → AtFormOne
def AtFormAdmOneOfSteps : Prop :=
  SchurH → CompanionTheory.D.Upq.BesselFunctionalConstruction.BeConv → CompanionTheory.D.Upq.BesselFunctionalConstruction.NormIdSm → CompanionTheory.D.Upq.BesselFunctionalConstruction.BeBessel → Shape → CompanionTheory.D.Upq.BesselFunctionalConstruction.KFinForm → CompanionTheory.D.Upq.BesselFunctionalConstruction.ZeroCase → CompanionTheory.D.Upq.BesselFunctionalConstruction.ZeroCaseDD → AtFormAdmOne
end CompanionTheory.Lime.BM


