-- Prove2me | Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_BesselOrbitConvolutions_BesselNonvanishingReduction
-- name    : CompanionTheory_HarishChandraModules_BesselParameterIntegrals_BesselOrbitConvolutions_BesselNonvanishingReduction
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T02:27:57.069261+00:00
-- url     : https://prove2.me/theorems/0d1469f8-11c6-4763-bb16-2510b44b0043
-- title:
--   Bessel Nonvanishing Reduction
-- statement:
--   Definitions and structural lemmas for Bessel Nonvanishing Reduction, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/BesselOrbitConvolutions/BesselNonvanishingReduction.lean

import Definitions.Def_Formalism_HermitianCurvature_BesselNonvanishingReduction
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
namespace CompanionTheory.D.Upq.BesselFunctionalConstruction
open Formalism.FourierDecayAlt.ThreeDimData
def Inputs : Prop := DecLow ∧ DecInf ∧ PI.KFinSmooth ∧ True
def DecDD : Prop :=
  Inputs → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ) (h : ℝ)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mx k r → (H →L[ℂ] H)) (w0 : H)
    (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp]
    (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (u : Fin k → ℝ) (π : Mx k r → (Wp →L[ℂ] Wp))
    (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)),
    Side k r ε lam h σ w0 z c u π μW μN μG νq →
    ∀ x ∈ DDsp σ w0, ∀ y ∈ DDsp σ w0, ∃ C : ℝ, ∀ g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r),
      ‖⟪y, σ g x⟫_ℂ‖ ≤ C * Formalism.FourierDecayAlt.B.gN g ^ (-aOf r h)
def BeConv : Prop :=
  Inputs → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ) (h : ℝ)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mx k r → (H →L[ℂ] H)) (w0 : H)
    (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp]
    (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (u : Fin k → ℝ) (π : Mx k r → (Wp →L[ℂ] Wp))
    (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)),
    Side k r ε lam h σ w0 z c u π μW μN μG νq →
    (∀ x ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ, ∀ v : H, IsAdm σ w0 v → Integrable (beInt z c π σ x v) (μW.prod μN)) ∧
    (∀ v : H, IsAdm σ w0 v → ∀ g ∈ Formalism.QuantumDeterminants.UWset k r z, ∀ m ∈ Formalism.QuantumDeterminants.Nset k r, ∀ x ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ,
      be z c π σ μW μN (σ (g * m) x) v = Formalism.QuantumDeterminants.psi k r z c m • (π g).comp (be z c π σ μW μN x v)) ∧
    (∀ x ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ, ∀ v : H, IsAdm σ w0 v →
      ContinuousOn (fun g => be z c π σ μW μN (σ g x) v) (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r))) ∧
    (∀ x ∈ DDsp σ w0, ∀ v : H, IsAdm σ w0 v →
      Integrable (beInt z c π σ v x) (μW.prod μN) ∧
      ContinuousLinearMap.adjoint (be z c π σ μW μN x v) = be z c π σ μW μN v x)
def NormIdSm : Prop :=
  Inputs → SchurH → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ) (h : ℝ)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mx k r → (H →L[ℂ] H)) (w0 : H)
    (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp]
    (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (u : Fin k → ℝ) (π : Mx k r → (Wp →L[ℂ] Wp))
    (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)),
    Side k r ε lam h σ w0 z c u π μW μN μG νq →
    ∀ x ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ, ∀ v : H, IsAdm σ w0 v → ∀ ξ : Wp,
      PI.BesselPeriodGGP.l2SG νq (fun g => be z c π σ μW μN (σ g x) v ξ) =
        ENNReal.ofReal (‖x‖ ^ 2 * (⟪ξ, be z c π σ μW μN v v ξ⟫_ℂ).re / PI.BesselPeriodGGP.fdegH μG σ w0) ∧
      (⟪ξ, be z c π σ μW μN v v ξ⟫_ℂ).im = 0 ∧ 0 ≤ (⟪ξ, be z c π σ μW μN v v ξ⟫_ℂ).re
def BeBessel : Prop :=
  Inputs → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ) (h : ℝ)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mx k r → (H →L[ℂ] H)) (w0 : H)
    (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp]
    (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (u : Fin k → ℝ) (π : Mx k r → (Wp →L[ℂ] Wp))
    (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)),
    Side k r ε lam h σ w0 z c u π μW μN μG νq →
    ∀ v : H, IsAdm σ w0 v → ∀ ξ : Wp,
      PI.BesselMapUniq.IsBesselMapSm (k := k) (r := r) z (Formalism.QuantumDeterminants.psi k r z c) σ π (fun x => be z c π σ μW μN x v ξ)
def Shape : Prop :=
  Inputs → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ) (h : ℝ)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mx k r → (H →L[ℂ] H)) (w0 : H)
    (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp]
    (z : Fin (2 * r + k + 1) → ℂ) (u : Fin k → ℝ) (π : Mx k r → (Wp →L[ℂ] Wp))
    (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)),
    Side k r ε lam h σ w0 z Formalism.QuantumDeterminants.cStd u π μW μN μG νq →
    (∃ x ∈ DDsp σ w0, ∃ y ∈ DDsp σ w0, be z Formalism.QuantumDeterminants.cStd π σ μW μN x y ≠ 0) →
    ∃ l : H → Wp, PI.BesselMapUniq.IsBesselMapSm (k := k) (r := r) z (Formalism.QuantumDeterminants.psi k r z Formalism.QuantumDeterminants.cStd) σ π l ∧
      (∃ x ∈ DDsp σ w0, l x ≠ 0) ∧
      ∀ x ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ, ∀ v ∈ DDsp σ w0, be z Formalism.QuantumDeterminants.cStd π σ μW μN x v = (innerSL ℂ (l v)).smulRight (l x)
def KFinForm : Prop :=
  Inputs → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ) (h : ℝ)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mx k r → (H →L[ℂ] H)) (w0 : H)
    (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp]
    (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (u : Fin k → ℝ) (π : Mx k r → (Wp →L[ℂ] Wp))
    (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)),
    Side k r ε lam h σ w0 z c u π μW μN μG νq →
    ∀ l : H → Wp, PI.BesselMapUniq.IsBesselMapSm (k := k) (r := r) z (Formalism.QuantumDeterminants.psi k r z c) σ π l →
      (∃ x ∈ DDsp σ w0, l x ≠ 0) →
      (∀ x ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ, ∀ v ∈ DDsp σ w0, be z c π σ μW μN x v = (innerSL ℂ (l v)).smulRight (l x)) →
      ∀ v : H, PI.UpqRep.IsKFinHpk (k := k) (r := r) σ v → ∀ x ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ,
        be z c π σ μW μN x v = (innerSL ℂ (l v)).smulRight (l x)
def ZeroCase : Prop :=
  Inputs → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ) (h : ℝ)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mx k r → (H →L[ℂ] H)) (w0 : H)
    (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp]
    (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (u : Fin k → ℝ) (π : Mx k r → (Wp →L[ℂ] Wp))
    (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)),
    Side k r ε lam h σ w0 z c u π μW μN μG νq →
    (∀ x ∈ DDsp σ w0, ∀ y ∈ DDsp σ w0, be z c π σ μW μN x y = 0) →
    ∀ v : H, PI.UpqRep.IsKFinHpk (k := k) (r := r) σ v → ∀ x ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ,
      be z c π σ μW μN x v = 0
def ZeroCaseDD : Prop :=
  Inputs → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ) (h : ℝ)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mx k r → (H →L[ℂ] H)) (w0 : H)
    (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp]
    (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (u : Fin k → ℝ) (π : Mx k r → (Wp →L[ℂ] Wp))
    (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)),
    Side k r ε lam h σ w0 z c u π μW μN μG νq →
    (∀ x ∈ DDsp σ w0, ∀ y ∈ DDsp σ w0, be z c π σ μW μN x y = 0) →
    ∀ v ∈ DDsp σ w0, ∀ x ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ,
      be z c π σ μW μN x v = 0
def DDFormOne : Prop :=
  Inputs → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ) (h : ℝ)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mx k r → (H →L[ℂ] H)) (w0 : H)
    (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp]
    (z : Fin (2 * r + k + 1) → ℂ) (u : Fin k → ℝ) (π : Mx k r → (Wp →L[ℂ] Wp))
    (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)),
    Side k r ε lam h σ w0 z Formalism.QuantumDeterminants.cStd u π μW μN μG νq →
    DDForm z Formalism.QuantumDeterminants.cStd π μW μN μG νq σ w0
def AtFormOne : Prop :=
  Inputs → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ) (h : ℝ)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mx k r → (H →L[ℂ] H)) (w0 : H)
    (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp]
    (z : Fin (2 * r + k + 1) → ℂ) (u : Fin k → ℝ) (π : Mx k r → (Wp →L[ℂ] Wp))
    (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)),
    Side k r ε lam h σ w0 z Formalism.QuantumDeterminants.cStd u π μW μN μG νq →
    AtForm z Formalism.QuantumDeterminants.cStd π μW μN μG νq σ
def AtFormAdmOne : Prop :=
  Inputs → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ) (h : ℝ)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mx k r → (H →L[ℂ] H)) (w0 : H)
    (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp]
    (z : Fin (2 * r + k + 1) → ℂ) (u : Fin k → ℝ) (π : Mx k r → (Wp →L[ℂ] Wp))
    (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)),
    Side k r ε lam h σ w0 z Formalism.QuantumDeterminants.cStd u π μW μN μG νq →
    AtFormAdm z Formalism.QuantumDeterminants.cStd π μW μN μG νq σ w0
def OrbConvDD : Prop :=
  Inputs → ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp]
    [FiniteDimensional ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [CompleteSpace Wq]
    [FiniteDimensional ℂ Wq] (D : Formalism.FourierDecayAlt.B.RealPlaceData k r Wp Wq)
    (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ) (h : ℝ)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mx k r → (H →L[ℂ] H)) (w0 : H)
    (u u' : Fin k → ℝ) (νq νq' : Measure (Formalism.QuantumDeterminants.Mt k r)),
    Side k r ε lam h σ w0 D.z Formalism.QuantumDeterminants.cStd u D.π D.μW D.μN D.μG νq →
    Side k r ε lam h σ w0 D.z' Formalism.QuantumDeterminants.cStd u' D.π' D.μW' D.μN D.μG νq' →
    ∀ x ∈ DDsp σ w0, ∀ y ∈ DDsp σ w0,
      (∀ γ ∈ Formalism.FourierDecayAlt.JF.Om k r D.z D.z',
        Integrable (fun p => ⟪x, σ (Formalism.FourierDecayAlt.B.sgs p γ) y⟫_ℂ) D.μSS) ∧
      ∀ K : Set (Mx k r), IsCompact K → K ⊆ Formalism.FourierDecayAlt.JF.Om k r D.z D.z' →
        ∃ b : Formalism.FourierDecayAlt.B.SS k r → ℝ, Integrable b D.μSS ∧
          ∀ γ ∈ K, ∀ᵐ p ∂D.μSS, ‖⟪x, σ (Formalism.FourierDecayAlt.B.sgs p γ) y⟫_ℂ‖ ≤ b p
def JFDD : Prop :=
  Inputs → SchurH → ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp]
    [FiniteDimensional ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [CompleteSpace Wq]
    [FiniteDimensional ℂ Wq] (D : Formalism.FourierDecayAlt.B.RealPlaceData k r Wp Wq)
    (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ) (h : ℝ)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mx k r → (H →L[ℂ] H)) (w0 : H)
    (u u' : Fin k → ℝ) (νq νq' : Measure (Formalism.QuantumDeterminants.Mt k r)),
    Side k r ε lam h σ w0 D.z Formalism.QuantumDeterminants.cStd u D.π D.μW D.μN D.μG νq →
    Side k r ε lam h σ w0 D.z' Formalism.QuantumDeterminants.cStd u' D.π' D.μW' D.μN D.μG νq' →
    ∀ (l : H → Wp) (l' : H → Wq),
      (∀ x ∈ DDsp σ w0, ∀ y ∈ DDsp σ w0,
        be D.z Formalism.QuantumDeterminants.cStd D.π σ D.μW D.μN x y = (innerSL ℂ (l y)).smulRight (l x)) →
      (∀ x ∈ DDsp σ w0, ∀ y ∈ DDsp σ w0,
        be D.z' Formalism.QuantumDeterminants.cStd D.π' σ D.μW' D.μN x y = (innerSL ℂ (l' y)).smulRight (l' x)) →
      ∀ x ∈ DDsp σ w0, ∀ y ∈ DDsp σ w0, ∀ X0 : Wq →L[ℂ] Wp, ∃ cc : ℂ, ∀ γ ∈ Formalism.FourierDecayAlt.JF.Om k r D.z D.z',
        Formalism.FourierDecayAlt.B.JF D (fun g => ⟪x, σ g y⟫_ℂ • X0) γ = cc • Mop D.μG σ w0 l l' γ
def BesselNonvanishingL2 : Prop :=
  Inputs → SchurH → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ) (h : ℝ)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mx k r → (H →L[ℂ] H)) (w0 : H)
    (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp]
    (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (u : Fin k → ℝ) (π : Mx k r → (Wp →L[ℂ] Wp))
    (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)),
    Side k r ε lam h σ w0 z c u π μW μN μG νq →
    ∀ W : Mx k r → Wp, ContinuousOn W (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) →
      PI.BesselPeriodGGP.IsSPsiEquiv z (Formalism.QuantumDeterminants.psi k r z c) π W →
      (∀ x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r),
        Integrable (fun y : Formalism.QuantumDeterminants.Mt k r => PI.BesselPeriodGGP.eFun μG σ w0 (Matrix.of y) • W (x * Matrix.of y)) μG ∧
        PI.BesselPeriodGGP.rconv μG (PI.BesselPeriodGGP.eFun μG σ w0) W x = W x) →
      0 < PI.BesselPeriodGGP.l2SG νq W → PI.BesselPeriodGGP.l2SG νq W < ⊤ →
      ∃ x ∈ DDsp σ w0, ∃ y ∈ DDsp σ w0, be z c π σ μW μN x y ≠ 0
def DDFormOneOfSteps : Prop :=
  PsiConst → SchurH → NormInv → GrowthS → GrowthG → DecDD → BeConv → NormIdSm → BeBessel → Shape → DDFormOne
def AtFormOneOfSteps : Prop :=
  SchurH → BeConv → NormIdSm → BeBessel → Shape → KFinForm → ZeroCase → AtFormOne
def AtFormAdmOneOfSteps : Prop :=
  SchurH → BeConv → NormIdSm → BeBessel → Shape → KFinForm → ZeroCase → ZeroCaseDD → AtFormAdmOne
def JFDDOfSteps : Prop :=
  NormInv → GrowthS → GrowthG → DecDD → BeConv → OrbConvDD → JFDD
def Repro : Prop :=
  Inputs → SchurH → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ) (h : ℝ)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mx k r → (H →L[ℂ] H)) (w0 : H)
    (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp]
    (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (u : Fin k → ℝ) (π : Mx k r → (Wp →L[ℂ] Wp))
    (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)),
    Side k r ε lam h σ w0 z c u π μW μN μG νq →
    ∀ Bm : H → Wp, PI.BesselMapUniq.IsBesselMapSm (k := k) (r := r) z (Formalism.QuantumDeterminants.psi k r z c) σ π Bm →
      (∀ x ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ, ∀ v ∈ DDsp σ w0,
        be z c π σ μW μN x v = (innerSL ℂ (Bm v)).smulRight (Bm x)) →
      ∀ x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r),
        Integrable (fun y : Formalism.QuantumDeterminants.Mt k r =>
          ((PI.BesselPeriodGGP.fdegH μG σ w0 : ℂ) * star ⟪w0, σ (Matrix.of y) w0⟫_ℂ) •
            Bm (σ (x * Matrix.of y) w0)) μG ∧
        ∫ y, ((PI.BesselPeriodGGP.fdegH μG σ w0 : ℂ) * star ⟪w0, σ (Matrix.of y) w0⟫_ℂ) •
            Bm (σ (x * Matrix.of y) w0) ∂μG = Bm (σ x w0)
def PhiReg : Prop :=
  Inputs → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ) (h : ℝ)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mx k r → (H →L[ℂ] H)) (w0 : H)
    (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp]
    (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (u : Fin k → ℝ) (π : Mx k r → (Wp →L[ℂ] Wp))
    (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)),
    Side k r ε lam h σ w0 z c u π μW μN μG νq →
    ∀ l : H → Wp, (∀ x ∈ DDsp σ w0, ∀ y ∈ DDsp σ w0,
        be z c π σ μW μN x y = (innerSL ℂ (l y)).smulRight (l x)) →
      ∀ x ∈ DDsp σ w0,
        ContinuousOn (fun g => l (σ g x)) (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) ∧
        ∫⁻ g, ((‖l (σ (Matrix.of g) x)‖₊ : ℝ≥0) : ℝ≥0∞) ∂νq < ⊤ ∧
        PI.BesselPeriodGGP.l2SG νq (fun g => l (σ g x)) < ⊤
def OOConv : Prop :=
  Inputs → ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp]
    [FiniteDimensional ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [CompleteSpace Wq]
    [FiniteDimensional ℂ Wq] (D : Formalism.FourierDecayAlt.B.RealPlaceData k r Wp Wq)
    (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ) (h : ℝ)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mx k r → (H →L[ℂ] H)) (w0 : H)
    (u u' : Fin k → ℝ) (νq νq' : Measure (Formalism.QuantumDeterminants.Mt k r)),
    Side k r ε lam h σ w0 D.z Formalism.QuantumDeterminants.cStd u D.π D.μW D.μN D.μG νq →
    Side k r ε lam h σ w0 D.z' Formalism.QuantumDeterminants.cStd u' D.π' D.μW' D.μN D.μG νq' →
    ∀ (l : H → Wp) (l' : H → Wq),
      (∀ x ∈ DDsp σ w0, ∀ y ∈ DDsp σ w0,
        be D.z Formalism.QuantumDeterminants.cStd D.π σ D.μW D.μN x y = (innerSL ℂ (l y)).smulRight (l x)) →
      (∀ x ∈ DDsp σ w0, ∀ y ∈ DDsp σ w0,
        be D.z' Formalism.QuantumDeterminants.cStd D.π' σ D.μW' D.μN x y = (innerSL ℂ (l' y)).smulRight (l' x)) →
      ∀ γ ∈ Formalism.FourierDecayAlt.JF.Om k r D.z D.z',
        Integrable (fun x : Formalism.QuantumDeterminants.Mt k r =>
          (innerSL ℂ (l' (σ (γ⁻¹ * Matrix.of x) w0))).smulRight (l (σ (Matrix.of x) w0))) D.μG
def QuadConv : Prop :=
  Inputs → ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp]
    [FiniteDimensional ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [CompleteSpace Wq]
    [FiniteDimensional ℂ Wq] (D : Formalism.FourierDecayAlt.B.RealPlaceData k r Wp Wq)
    (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ) (h : ℝ)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mx k r → (H →L[ℂ] H)) (w0 : H)
    (u u' : Fin k → ℝ) (νq νq' : Measure (Formalism.QuantumDeterminants.Mt k r)),
    Side k r ε lam h σ w0 D.z Formalism.QuantumDeterminants.cStd u D.π D.μW D.μN D.μG νq →
    Side k r ε lam h σ w0 D.z' Formalism.QuantumDeterminants.cStd u' D.π' D.μW' D.μN D.μG νq' →
    ∀ (l : H → Wp) (l' : H → Wq),
      (∀ x ∈ DDsp σ w0, ∀ y ∈ DDsp σ w0,
        be D.z Formalism.QuantumDeterminants.cStd D.π σ D.μW D.μN x y = (innerSL ℂ (l y)).smulRight (l x)) →
      (∀ x ∈ DDsp σ w0, ∀ y ∈ DDsp σ w0,
        be D.z' Formalism.QuantumDeterminants.cStd D.π' σ D.μW' D.μN x y = (innerSL ℂ (l' y)).smulRight (l' x)) →
      (∀ γ ∈ Formalism.FourierDecayAlt.JF.Om k r D.z D.z',
        ∫⁻ zz, ∫⁻ zz', ∫⁻ s, ∫⁻ s',
          ((‖⟪σ (Matrix.of zz) w0, σ (Matrix.of s * γ * (Matrix.of s')⁻¹) (σ (Matrix.of zz') w0)⟫_ℂ‖₊ : ℝ≥0) : ℝ≥0∞) *
            ((‖l (σ (Matrix.of zz) w0)‖₊ : ℝ≥0) : ℝ≥0∞) * ((‖l' (σ (Matrix.of zz') w0)‖₊ : ℝ≥0) : ℝ≥0∞)
          ∂(muSof D.μW' D.μN) ∂(muSof D.μW D.μN) ∂νq' ∂νq < ⊤) ∧
      ∫⁻ zz, ∫⁻ zz', ∫⁻ s,
          ((‖⟪σ (Matrix.of zz) w0, σ (Matrix.of s) (σ (Matrix.of zz') w0)⟫_ℂ‖₊ : ℝ≥0) : ℝ≥0∞) *
            ((‖l (σ (Matrix.of zz) w0)‖₊ : ℝ≥0) : ℝ≥0∞) * ((‖l (σ (Matrix.of zz') w0)‖₊ : ℝ≥0) : ℝ≥0∞)
          ∂(muSof D.μW D.μN) ∂νq ∂νq < ⊤
def ReproOfSteps : Prop := SchurH → NormInv → GrowthS → GrowthG → DecDD → BeConv → Repro
def BesselNonvanishingReduction : Prop := SchurH → NormInv → GrowthS → GrowthG → DecDD → BeConv → BesselNonvanishingL2
def MoreOfSteps : Prop :=
  SchurH → NormIdSm → NormInv → GrowthS → GrowthG → DecDD → BeConv → OrbConvDD → (PhiReg ∧ OOConv ∧ QuadConv)
end CompanionTheory.D.Upq.BesselFunctionalConstruction


