-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_BesselNonvanishingReduction
-- name    : Formalism_HermitianCurvature_BesselNonvanishingReduction
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-24T14:46:21.465254+00:00
-- url     : https://prove2.me/theorems/50cfc604-22a0-4de4-99f4-978ef62cdd2f
-- title:
--   Bessel Nonvanishing Reduction
-- statement:
--   Definitions and structural lemmas for Bessel Nonvanishing Reduction, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/BesselNonvanishingReduction.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UpqRep
import Definitions.Def_Formalism_PeriodIntegrals_IsLowUnitH
import Definitions.Def_Formalism_PeriodIntegrals_LowCyc
import Definitions.Def_Formalism_PeriodIntegrals_KFinSmooth
import Definitions.Def_Formalism_PeriodIntegrals_BesselPeriodGGP
import Definitions.Def_Formalism_PeriodIntegrals_BesselMapUniq
import Definitions.Def_Formalism_FormalDegreeBessel_StatementG
import Definitions.Def_Formalism_FormalDegreeBessel_StatementDS
import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_StatementJF
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix Finset
open scoped InnerProductSpace ENNReal
noncomputable section
namespace Formalism.FourierDecayAlt.ThreeDimData
abbrev Mx (k r : ℕ) := Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ
def aOf (r : ℕ) (h : ℝ) : ℝ := h / (8 * Real.sqrt (2 * ((r : ℝ) + 1)))
def AG (k r : ℕ) : ℝ := 4 * ((k : ℝ) + r) * ((r : ℝ) + 1)
def dN (k r : ℕ) : ℝ := (r : ℝ) * ((r : ℝ) - 1) + 2 * (r : ℝ) * ((k : ℝ) + 1) + (r : ℝ) ^ 2
def AS (k r : ℕ) : ℝ := ((2 * r + k : ℕ) : ℝ) * dN k r
def Mexp (r : ℕ) : ℝ := 2 * ((r : ℝ) ^ 2 + r + 1)
def GapOK (k r : ℕ) (h : ℝ) : Prop :=
  1 ≤ k ∧ 120 * ((2 * r + k + 1 : ℕ) : ℝ) ^ 3 ≤ h ∧ 2 * Mexp r * (AS k r + AG k r) + AG k r + 3 ≤ aOf r h ∧
    9 * ((r : ℝ) + 1) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 + 3 * AG k r + 3 ≤ aOf r h
def DDsp {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Mx k r → (H →L[ℂ] H)) (w0 : H) : Submodule ℂ H :=
  Submodule.span ℂ ((fun g => σ g w0) '' Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r))
def beInt {k r : ℕ} {H Wp : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (σ : Mx k r → (H →L[ℂ] H))
    (u v : H) (p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r) : Wp →L[ℂ] Wp :=
  (⟪v, σ (Matrix.of p.1 * Matrix.of p.2) u⟫_ℂ * star (Formalism.QuantumDeterminants.psi k r z c (Matrix.of p.2))) •
    π (Matrix.of p.1)⁻¹
def be {k r : ℕ} {H Wp : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp]
    (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (σ : Mx k r → (H →L[ℂ] H))
    (μW μN : Measure (Formalism.QuantumDeterminants.Mt k r)) (u v : H) : Wp →L[ℂ] Wp :=
  ∫ p, beInt z c π σ u v p ∂(μW.prod μN)
def muSof {k r : ℕ} (μW μN : Measure (Formalism.QuantumDeterminants.Mt k r)) : Measure (Formalism.QuantumDeterminants.Mt k r) :=
  (μW.prod μN).map (fun p => fun i j => (Matrix.of p.1 * Matrix.of p.2) i j)
def IsAdm {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Mx k r → (H →L[ℂ] H)) (w0 v : H) : Prop :=
  v ∈ DDsp σ w0 ∨ PI.UpqRep.IsKFinHpk (k := k) (r := r) σ v
def DDForm {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp]
    (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (π : Mx k r → (Wp →L[ℂ] Wp))
    (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)) (σ : Mx k r → (H →L[ℂ] H)) (w0 : H) : Prop :=
  ∃ l : H → Wp, PI.BesselMapUniq.IsBesselMapSm (k := k) (r := r) z (Formalism.QuantumDeterminants.psi k r z c) σ π l ∧
    (∀ u ∈ DDsp σ w0, ∀ v ∈ DDsp σ w0,
      Integrable (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r =>
        (⟪v, σ (Matrix.of p.1 * Matrix.of p.2) u⟫_ℂ * star (Formalism.QuantumDeterminants.psi k r z c (Matrix.of p.2))) •
          π (Matrix.of p.1)⁻¹) (μW.prod μN) ∧
      ∫ p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r,
        (⟪v, σ (Matrix.of p.1 * Matrix.of p.2) u⟫_ℂ * star (Formalism.QuantumDeterminants.psi k r z c (Matrix.of p.2))) •
          π (Matrix.of p.1)⁻¹ ∂(μW.prod μN) = (innerSL ℂ (l v)).smulRight (l u)) ∧
    ∀ u ∈ DDsp σ w0, u ≠ 0 → ∀ v ∈ DDsp σ w0,
      ENNReal.ofReal (‖l v‖ ^ 2) * PI.BesselPeriodGGP.l2SG νq (fun g => l (σ g u)) =
        ENNReal.ofReal (‖u‖ ^ 2 * ‖l v‖ ^ 2 / PI.BesselPeriodGGP.fdegH μG σ u)
def AtForm {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp]
    (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (π : Mx k r → (Wp →L[ℂ] Wp))
    (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)) (σ : Mx k r → (H →L[ℂ] H)) : Prop :=
  ∃ l : H → Wp, PI.BesselMapUniq.IsBesselMapSm (k := k) (r := r) z (Formalism.QuantumDeterminants.psi k r z c) σ π l ∧
    (∀ w ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ, ∀ v : H, PI.UpqRep.IsKFinHpk (k := k) (r := r) σ v →
      Integrable (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r =>
        (⟪v, σ (Matrix.of p.1 * Matrix.of p.2) w⟫_ℂ * star (Formalism.QuantumDeterminants.psi k r z c (Matrix.of p.2))) •
          π (Matrix.of p.1)⁻¹) (μW.prod μN) ∧
      ∫ p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r,
        (⟪v, σ (Matrix.of p.1 * Matrix.of p.2) w⟫_ℂ * star (Formalism.QuantumDeterminants.psi k r z c (Matrix.of p.2))) •
          π (Matrix.of p.1)⁻¹ ∂(μW.prod μN) = (innerSL ℂ (l v)).smulRight (l w)) ∧
    ∀ w ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ, w ≠ 0 → ∀ v : H,
      PI.UpqRep.IsKFinHpk (k := k) (r := r) σ v →
      ENNReal.ofReal (‖l v‖ ^ 2) * PI.BesselPeriodGGP.l2SG νq (fun g => l (σ g w)) =
        ENNReal.ofReal (‖w‖ ^ 2 * ‖l v‖ ^ 2 / PI.BesselPeriodGGP.fdegH μG σ w)
def AtFormAdm {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp]
    (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (π : Mx k r → (Wp →L[ℂ] Wp))
    (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)) (σ : Mx k r → (H →L[ℂ] H)) (w0 : H) : Prop :=
  ∃ l : H → Wp, PI.BesselMapUniq.IsBesselMapSm (k := k) (r := r) z (Formalism.QuantumDeterminants.psi k r z c) σ π l ∧
    (∀ w ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ, ∀ v : H, IsAdm σ w0 v →
      Integrable (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r =>
        (⟪v, σ (Matrix.of p.1 * Matrix.of p.2) w⟫_ℂ * star (Formalism.QuantumDeterminants.psi k r z c (Matrix.of p.2))) •
          π (Matrix.of p.1)⁻¹) (μW.prod μN) ∧
      ∫ p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r,
        (⟪v, σ (Matrix.of p.1 * Matrix.of p.2) w⟫_ℂ * star (Formalism.QuantumDeterminants.psi k r z c (Matrix.of p.2))) •
          π (Matrix.of p.1)⁻¹ ∂(μW.prod μN) = (innerSL ℂ (l v)).smulRight (l w)) ∧
    ∀ w ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ, w ≠ 0 → ∀ v : H, IsAdm σ w0 v →
      ENNReal.ofReal (‖l v‖ ^ 2) * PI.BesselPeriodGGP.l2SG νq (fun g => l (σ g w)) =
        ENNReal.ofReal (‖w‖ ^ 2 * ‖l v‖ ^ 2 / PI.BesselPeriodGGP.fdegH μG σ w)
def Side (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ) (h : ℝ)
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Mx k r → (H →L[ℂ] H)) (w0 : H)
    {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (u : Fin k → ℝ) (π : Mx k r → (Wp →L[ℂ] Wp))
    (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)) : Prop :=
  Formalism.QuantumDeterminants.IsHCParam lam ∧ PI.UpqRep.IsDSHpk k r ε lam σ ∧ Formalism.QuantumDeterminants.GapAtLeast ε lam h ∧ GapOK k r h ∧
    PI.UpqRep.IsLowUnitH k r ε lam σ w0 ∧ Formalism.QuantumDeterminants.inWb k r z ∧ 0 < Formalism.QuantumDeterminants.Tz k r z ∧ c ≠ 0 ∧
    PI.UpqRep.IsHCTypeW k r z u π ∧
    PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.UWset k r z) μW ∧
    PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μN ∧
    PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) μG ∧
    PI.BesselPeriodGGP.IsQuotMeas μG (muSof μW μN) νq
def DecLow : Prop :=
  ∀ (k r : ℕ), 1 ≤ k → ∀ (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ) (h : ℝ)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mx k r → (H →L[ℂ] H)),
    Formalism.QuantumDeterminants.IsHCParam lam → PI.UpqRep.IsDSHpk k r ε lam σ → Formalism.QuantumDeterminants.GapAtLeast ε lam h →
    120 * ((2 * r + k + 1 : ℕ) : ℝ) ^ 3 ≤ h →
    ∀ P, PI.UpqRep.IsCayleyU k r ε P → ∀ w₁ w₂ : H,
      w₁ ∈ PI.UpqRep.lowKSub ε lam (fun g => σ (P⁻¹ * g * P)) →
      w₂ ∈ PI.UpqRep.lowKSub ε lam (fun g => σ (P⁻¹ * g * P)) →
      ∃ C : ℝ, ∀ x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r),
        ‖⟪w₂, σ x w₁⟫_ℂ‖ ≤ C * Formalism.FourierDecayAlt.B.gN x ^ (-(h / (8 * Real.sqrt (2 * ((r : ℝ) + 1)))))
def DecInf : Prop :=
  ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ) (h : ℝ)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mx k r → (H →L[ℂ] H)),
    Formalism.QuantumDeterminants.IsHCParam lam → PI.UpqRep.IsDSHpk k r ε lam σ → Formalism.QuantumDeterminants.GapAtLeast ε lam h → GapOK k r h →
    ∀ v0 : H, PI.UpqRep.IsKFinHpk (k := k) (r := r) σ v0 →
      ∃ (C : ℝ) (Ws : List (List (Mx k r))), (∀ W ∈ Ws, ∀ X ∈ W, PI.UpqRep.InLieHpk k r X) ∧
        ∀ w ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ, ∀ x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r),
          ‖⟪v0, σ x w⟫_ℂ‖ ≤
            C * (Ws.map fun W => ‖PI.UpqRep.dsigW (k := k) (r := r) σ W w‖).sum * Formalism.FourierDecayAlt.B.gN x ^ (1 - aOf r h)
def Inputs : Prop := DecLow ∧ DecInf ∧ PI.KFinSmooth ∧ PI.BesselMapUniq.BesselMapUniq
def PsiConst : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (g : Mx k r),
    Formalism.QuantumDeterminants.psi k r z c g = PI.BesselMapUniq.psiGen k r z (fun _ => c) g
def SchurH : Prop :=
  ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mx k r → (H →L[ℂ] H))
    (μG : Measure (Formalism.QuantumDeterminants.Mt k r)),
    Formalism.QuantumDeterminants.IsHCParam lam → PI.UpqRep.IsDSHpk k r ε lam σ →
    PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) μG →
    ∃ d : ℝ, 0 < d ∧ ∀ v w v' w' : H,
      Integrable (fun x : Formalism.QuantumDeterminants.Mt k r => ⟪w, σ (Matrix.of x) v⟫_ℂ * star ⟪w', σ (Matrix.of x) v'⟫_ℂ) μG ∧
      ∫ x, ⟪w, σ (Matrix.of x) v⟫_ℂ * star ⟪w', σ (Matrix.of x) v'⟫_ℂ ∂μG = ⟪v', v⟫_ℂ * ⟪w, w'⟫_ℂ / (d : ℂ)
def NormInv : Prop :=
  ∀ k r : ℕ, (∀ x y : Mx k r, Formalism.FourierDecayAlt.B.gN (x * y) ≤ Formalism.FourierDecayAlt.B.gN x * Formalism.FourierDecayAlt.B.gN y) ∧
    ∀ x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), Formalism.FourierDecayAlt.B.gN x⁻¹ = Formalism.FourierDecayAlt.B.gN x ∧ 1 ≤ Formalism.FourierDecayAlt.B.gN x
def GrowthS : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)) (A : ℝ),
    Formalism.QuantumDeterminants.inWb k r z → 0 < Formalism.QuantumDeterminants.Tz k r z →
    PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.UWset k r z) μW → PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μN →
    PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) μG →
    PI.BesselPeriodGGP.IsQuotMeas μG (muSof μW μN) νq →
    AG k r < A →
    Integrable (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r =>
      Formalism.FourierDecayAlt.B.gN (Matrix.of p.1 * Matrix.of p.2) ^ (-A)) (μW.prod μN)
def GrowthG : Prop :=
  ∀ (k r : ℕ) (μG : Measure (Formalism.QuantumDeterminants.Mt k r)) (A : ℝ),
    PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) μG → AG k r < A →
    Integrable (fun x : Formalism.QuantumDeterminants.Mt k r => Formalism.FourierDecayAlt.B.gN (Matrix.of x) ^ (-A)) μG
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
    (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (u : Fin k → ℝ) (π : Mx k r → (Wp →L[ℂ] Wp))
    (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)),
    Side k r ε lam h σ w0 z c u π μW μN μG νq →
    (∃ x ∈ DDsp σ w0, ∃ y ∈ DDsp σ w0, be z c π σ μW μN x y ≠ 0) →
    ∃ l : H → Wp, PI.BesselMapUniq.IsBesselMapSm (k := k) (r := r) z (Formalism.QuantumDeterminants.psi k r z c) σ π l ∧
      (∃ x ∈ DDsp σ w0, l x ≠ 0) ∧
      ∀ x ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ, ∀ v ∈ DDsp σ w0, be z c π σ μW μN x v = (innerSL ℂ (l v)).smulRight (l x)
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
def DDNz : Prop :=
  PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mx k r → (H →L[ℂ] H)) (w0 : H)
    (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)),
    Formalism.QuantumDeterminants.IsHCParam lam → PI.UpqRep.IsDSHpk k r ε lam σ → PI.UpqRep.IsLowUnitH k r ε lam σ w0 →
    ∀ Bm : H → Wp, PI.BesselMapUniq.IsBesselMapSm (k := k) (r := r) z (Formalism.QuantumDeterminants.psi k r z c) σ π Bm →
      (∀ x ∈ DDsp σ w0, Bm x = 0) → ∀ x ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ, Bm x = 0
def DDNzOfCyc : Prop := PI.SmoothCyc → DDNz
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
def Mop {k r : ℕ} {H Wp Wq : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    (μG : Measure (Formalism.QuantumDeterminants.Mt k r)) (σ : Mx k r → (H →L[ℂ] H)) (w0 : H) (l : H → Wp) (l' : H → Wq)
    (γ : Mx k r) : Wq →L[ℂ] Wp :=
  (PI.BesselPeriodGGP.fdegH μG σ w0 : ℂ) •
    ∫ x, (innerSL ℂ (l' (σ (γ⁻¹ * Matrix.of x) w0))).smulRight (l (σ (Matrix.of x) w0)) ∂μG
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
def IntCommute : Prop :=
  ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mx k r → (H →L[ℂ] H))
    (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp]
    (μG : Measure (Formalism.QuantumDeterminants.Mt k r)) (Bm : H → Wp),
    Formalism.QuantumDeterminants.IsHCParam lam → PI.UpqRep.IsDSHpk k r ε lam σ →
    PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) μG →
    (∀ x ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ, ∀ y ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ, Bm (x + y) = Bm x + Bm y) →
    (∀ (a : ℂ), ∀ x ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ, Bm (a • x) = a • Bm x) →
    PI.BesselMapUniq.IsCWCont (k := k) (r := r) σ Bm →
    ∀ x ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ, ∀ f : Formalism.QuantumDeterminants.Mt k r → ℂ, Continuous f → HasCompactSupport f →
      (∫ g, f g • σ (Matrix.of g) x ∂μG) ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ ∧
      Bm (∫ g, f g • σ (Matrix.of g) x ∂μG) = ∫ g, f g • Bm (σ (Matrix.of g) x) ∂μG
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
namespace More
open scoped NNReal
open Formalism.FourierDecayAlt.ThreeDimData
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
end More
end Formalism.FourierDecayAlt.ThreeDimData


