-- Prove2me | Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_BesselOrbitConvolutions_AtFormAdmOneOfSteps
-- name    : CompanionTheory_HarishChandraModules_BesselParameterIntegrals_BesselOrbitConvolutions_AtFormAdmOneOfSteps
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T02:37:28.878951+00:00
-- url     : https://prove2.me/theorems/2a27eeb3-c166-4147-a20c-31623d0b935f
-- title:
--   At Form Adm One Of Steps
-- statement:
--   Definitions and structural lemmas for At Form Adm One Of Steps, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/BesselOrbitConvolutions/AtFormAdmOneOfSteps.lean

import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_BesselOrbitConvolutions_BesselNonvanishingReduction
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix Finset
open scoped InnerProductSpace ENNReal NNReal
noncomputable section
namespace CompanionTheory.D.Upq.BesselFunctionalConstruction.C
open Formalism.FourierDecayAlt.ThreeDimData
def Shape : Prop :=
  Inputs → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ) (h : ℝ)
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
  Inputs → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ) (h : ℝ)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mx k r → (H →L[ℂ] H)) (w0 : H)
    (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp]
    (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (u : Fin k → ℝ) (π : Mx k r → (Wp →L[ℂ] Wp))
    (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)),
    Side k r ε lam h σ w0 z c u π μW μN μG νq →
    DDForm z c π μW μN μG νq σ w0
def AtFormOne : Prop :=
  Inputs → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ) (h : ℝ)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mx k r → (H →L[ℂ] H)) (w0 : H)
    (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp]
    (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (u : Fin k → ℝ) (π : Mx k r → (Wp →L[ℂ] Wp))
    (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)),
    Side k r ε lam h σ w0 z c u π μW μN μG νq →
    AtForm z c π μW μN μG νq σ
def AtFormAdmOne : Prop :=
  Inputs → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ) (h : ℝ)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mx k r → (H →L[ℂ] H)) (w0 : H)
    (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp]
    (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (u : Fin k → ℝ) (π : Mx k r → (Wp →L[ℂ] Wp))
    (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)),
    Side k r ε lam h σ w0 z c u π μW μN μG νq →
    AtFormAdm z c π μW μN μG νq σ w0
def DDFormOneOfSteps : Prop :=
  PsiConst → SchurH → NormInv → GrowthS → GrowthG → DecDD → BeConv → NormIdSm → BeBessel → Shape → DDFormOne
def AtFormOneOfSteps : Prop :=
  SchurH → BeConv → NormIdSm → BeBessel → Shape → KFinForm → ZeroCase → AtFormOne
def AtFormAdmOneOfSteps : Prop :=
  SchurH → BeConv → NormIdSm → BeBessel → Shape → KFinForm → ZeroCase → ZeroCaseDD → AtFormAdmOne
end CompanionTheory.D.Upq.BesselFunctionalConstruction.C


