-- Prove2me | Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_IsLawOfLog
-- name    : Formalism_ThetaLogCoordinates_UniformThetaSubstitution_IsLawOfLog
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T22:45:45.006741+00:00
-- url     : https://prove2.me/theorems/e93bbae9-3a40-4b21-8841-8e2f53a40511
-- title:
--   Is Law Of Log
-- statement:
--   Definitions and structural lemmas for Is Law Of Log, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/IsLawOfLog.lean

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_CyclicPowerClassOfExpEquiv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
namespace Formalism.InvariantFactorPaths.G7
open Formalism.DworkPowerSeriesWeights (Integral mvExp)
def UnrOK (K : Type) [NormedField K] (p : ℕ) (σ : K →+* K) : Prop :=
  p.Prime ∧ 2 < p ∧ ‖(p : K)‖ = (p : ℝ)⁻¹ ∧ (∀ a : K, a ≠ 0 → ∃ k : ℤ, ‖a‖ = (p : ℝ) ^ k) ∧
    ∀ a : K, ‖a‖ ≤ 1 → ‖σ a - a ^ p‖ ≤ (p : ℝ)⁻¹
section Defs
variable {K : Type} [Field K]
def cob (F : MvPowerSeries (Fin 2) K) (f : PowerSeries K) : MvPowerSeries (Fin 2) K :=
  PowerSeries.subst F f - at1 0 f - at1 1 f
def swap2 (H : MvPowerSeries (Fin 2) K) : MvPowerSeries (Fin 2) K :=
  MvPowerSeries.subst ![(MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K), MvPowerSeries.X 0] H
def in3 (f : MvPowerSeries (Fin 2) K) : MvPowerSeries (Fin 3) K :=
  MvPowerSeries.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 3) K), MvPowerSeries.X 1] f
def d1 (F H : MvPowerSeries (Fin 2) K) : MvPowerSeries (Fin 3) K :=
  MvPowerSeries.subst ![in3 F, MvPowerSeries.X 2] H -
    MvPowerSeries.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 3) K), MvPowerSeries.X 2] H -
    MvPowerSeries.subst ![(MvPowerSeries.X 1 : MvPowerSeries (Fin 3) K), MvPowerSeries.X 2] H
def DivAB (H : MvPowerSeries (Fin 2) K) : Prop :=
  ∀ n : Fin 2 →₀ ℕ, n 0 = 0 ∨ n 1 = 0 → MvPowerSeries.coeff n H = 0
end Defs
def IsLawOfLog {K : Type} [NormedField K] (p : ℕ) (F : MvPowerSeries (Fin 2) K) : Prop :=
  MvPowerSeries.constantCoeff F = 0 ∧ Integral F ∧ cob F (lgF K p) = 0
def LawExists : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (p : ℕ), p.Prime →
    ‖(p : K)‖ = (p : ℝ)⁻¹ →
    (∃ F : MvPowerSeries (Fin 2) K, IsLawOfLog p F) ∧
    ∀ F F' : MvPowerSeries (Fin 2) K, MvPowerSeries.constantCoeff F = 0 →
      MvPowerSeries.constantCoeff F' = 0 → cob F (lgF K p) = 0 → cob F' (lgF K p) = 0 → F = F'
def DivDeriv : Prop :=
  ∀ (K ι κ : Type) [Finite ι] [DecidableEq ι] [NormedField K] [IsUltrametricDist K] [CharZero K]
    (p : ℕ), p.Prime → ‖(p : K)‖ = (p : ℝ)⁻¹ →
    ∀ (x : ι) (Φ : MvPowerSeries ι K) (φ : ι → MvPowerSeries κ K) (Y : MvPowerSeries κ K),
      Integral (MvPowerSeries.pderiv (R := K) x Φ) →
      (∀ i, MvPowerSeries.constantCoeff (φ i) = 0) → (∀ i, Integral (φ i)) →
      MvPowerSeries.constantCoeff Y = 0 → Integral Y →
      ∀ n, ‖MvPowerSeries.coeff n
        (MvPowerSeries.subst (Function.update φ x (φ x + MvPowerSeries.C (p : K) * Y)) Φ -
          MvPowerSeries.subst φ Φ)‖ ≤ (p : ℝ)⁻¹
def DeIntegral : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (p : ℕ) (σ : K →+* K), p.Prime →
    ‖(p : K)‖ = (p : ℝ)⁻¹ → (∀ a : K, ‖a‖ ≤ 1 → ‖σ a - a ^ p‖ ≤ (p : ℝ)⁻¹) →
    ∀ F : MvPowerSeries (Fin 2) K, IsLawOfLog p F → Integral (cob F (g0F K p))
def DerivA : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (p : ℕ), p.Prime →
    ‖(p : K)‖ = (p : ℝ)⁻¹ →
    Integral (MvPowerSeries.pderiv (R := K) 0 (Aser K p) -
      at1 0 (PowerSeries.derivative K (lgF K p)) * at1 1 (g0F K p)) ∧
    Integral (MvPowerSeries.pderiv (R := K) 0 (Aser' K p))
def LemmaOne : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] [CompleteSpace K] (p : ℕ)
    (σ : K →+* K), UnrOK K p σ →
    ∀ F : MvPowerSeries (Fin 2) K, IsLawOfLog p F →
    ∀ f : PowerSeries K, PowerSeries.constantCoeff f = 0 → Integral (cob F f) →
      ∃ (α β : K) (R : PowerSeries K), ‖α‖ ≤ 1 ∧ (∀ n, ‖PowerSeries.coeff n R‖ ≤ 1) ∧
        f = PowerSeries.C α * g0F K p + PowerSeries.C β * lgF K p + R
def LemmaTwo : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] [CompleteSpace K] (p : ℕ)
    (σ : K →+* K), UnrOK K p σ →
    ∀ F : MvPowerSeries (Fin 2) K, IsLawOfLog p F →
    ∀ H : MvPowerSeries (Fin 2) K, DivAB H → Integral (d1 F H) → Integral (d1 F (swap2 H)) →
      ∃ (β : K) (R : MvPowerSeries (Fin 2) K), Integral R ∧
        H = MvPowerSeries.C β * (at1 0 (lgF K p) * at1 1 (lgF K p)) + R
def BetaHyp {K : Type} [NormedField K] [CharZero K] (p : ℕ) (F be : MvPowerSeries (Fin 2) K) :
    Prop :=
  DivAB be ∧ Simeq (d1 F be) 0 ∧ Simeq (d1 F (swap2 be)) 0 ∧
    ∀ ζ : K, ζ ^ (p ^ 2 - 1) = 1 →
      Simeq (MvPowerSeries.subst ![MvPowerSeries.C ζ * (MvPowerSeries.X 0 :
          MvPowerSeries (Fin 2) K), MvPowerSeries.X 1] be)
        (MvPowerSeries.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K),
          MvPowerSeries.C (ζ ^ p) * MvPowerSeries.X 1] be)
def BetaIsG : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] [CompleteSpace K] (p : ℕ)
    (σ : K →+* K), UnrOK K p σ → (∃ ζ : K, IsPrimitiveRoot ζ (p ^ 2 - 1)) →
    ∀ F : MvPowerSeries (Fin 2) K, IsLawOfLog p F →
    ∀ be : MvPowerSeries (Fin 2) K, BetaHyp p F be →
      ∃ c : K, ‖c‖ ≤ 1 ∧ σ (σ c) = c ∧ Simeq be (Gser p c (σ c))
def ThmSFull : Prop :=
  ∀ (K0 K : Type) [NormedField K0] [IsUltrametricDist K0] [CharZero K0] [CompleteSpace K0]
    [NormedField K] [IsUltrametricDist K] [CharZero K] (j : K0 →+* K) (p ν r0 r1 : ℕ) [NeZero ν]
    (σ : K0 →+* K0), (∀ a, ‖j a‖ = ‖a‖) → UnrOK K0 p σ →
    (∃ ζ : K0, IsPrimitiveRoot ζ (p ^ 2 - 1)) →
    ∀ F : MvPowerSeries (Fin 2) K0, IsLawOfLog p F →
    ∀ be : MvPowerSeries (Fin 2) K0, BetaHyp p F be →
    ∃ c : K0, ‖c‖ ≤ 1 ∧ σ (σ c) = c ∧
    ∀ (om oms : Fin ν → ZMod (2 * ν) → K) (ϖ : K) (μ : PowerSeries K)
      (U0 Φ : MvPowerSeries (Bool × EV ν r0 r1) K),
      ϖ ^ (p ^ 2 - 1) = (p : K) → OmOK p ν om oms →
      PowerSeries.constantCoeff μ = 0 →
      (PowerSeries.subst μ (lamF p ϖ) : PowerSeries K) = PowerSeries.X → Integral U0 →
      MvPowerSeries.constantCoeff Φ = 0 →
      Simeq Φ (∑ e : EV ν r0 r1, MvPowerSeries.subst
        (fun a : Fin 2 => (MvPowerSeries.X (if a = 0 then (false, e) else (true, e)) :
          MvPowerSeries (Bool × EV ν r0 r1) K)) (MvPowerSeries.map j be)) →
      InClass (p : K) (hhS p (uS (j c) (j (σ c))))
        (MvPowerSeries.subst (fun x => MvPowerSeries.C ϖ * sSub om oms μ x) (mvExp (-Φ) * U0))
end Formalism.InvariantFactorPaths.G7


