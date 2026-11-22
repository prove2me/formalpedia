-- Prove2me | Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FirstDeriv
-- name    : Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FirstDeriv
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T22:48:29.032079+00:00
-- url     : https://prove2.me/theorems/6e98987b-ff92-4c2a-9b0f-a26ca599b577
-- title:
--   First Deriv
-- statement:
--   Definitions and structural lemmas for First Deriv, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FirstDeriv.lean

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_IsLawOfLog
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
section Defs
variable {K : Type} [Field K]
def SuppOK (p : ℕ) (G : MvPowerSeries (Fin 2) K) : Prop :=
  ∀ n : Fin 2 →₀ ℕ, MvPowerSeries.coeff n G ≠ 0 →
    1 ≤ n 0 ∧ 1 ≤ n 1 ∧ n 0 ≡ p * n 1 [MOD p ^ 2 - 1]
def fLin (G : MvPowerSeries (Fin 2) K) : PowerSeries K :=
  PowerSeries.mk fun j => MvPowerSeries.coeff (Finsupp.single 0 1 + Finsupp.single 1 j) G
def DeS (p : ℕ) (σ : K →+* K) (G : MvPowerSeries (Fin 2) K) : MvPowerSeries (Fin 2) K :=
  MvPowerSeries.C ((p : K)⁻¹) *
    (frobVar p (MvPowerSeries.map σ G) - MvPowerSeries.C (p : K) * G)
def Hser (p : ℕ) (σ : K →+* K) (G : MvPowerSeries (Fin 2) K) (γ γ' : K) :
    MvPowerSeries (Fin 2) K :=
  DeS p σ G - MvPowerSeries.C γ * (at1 0 (g0F K p) * at1 1 (lgF K p)) -
    MvPowerSeries.C γ' * (at1 0 (lgF K p) * at1 1 (g0F K p))
def DerivIs {K : Type} [NormedField K] (p : ℕ) (G : MvPowerSeries (Fin 2) K) (c : K) : Prop :=
  Integral (MvPowerSeries.pderiv (R := K) 0 G -
    MvPowerSeries.C c * (at1 0 (PowerSeries.derivative K (lgF K p)) * at1 1 (g0F K p)))
end Defs
def LawSymm : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (p : ℕ), p.Prime →
    ‖(p : K)‖ = (p : ℝ)⁻¹ →
    ∀ F : MvPowerSeries (Fin 2) K, IsLawOfLog p F →
      (∀ σ : K →+* K, MvPowerSeries.map σ F = F) ∧
      (∀ ζ : K, ζ ^ (p ^ 2 - 1) = 1 →
        MvPowerSeries.subst (fun a : Fin 2 => MvPowerSeries.C ζ *
          (MvPowerSeries.X a : MvPowerSeries (Fin 2) K)) F = MvPowerSeries.C ζ * F) ∧
      (∀ n : Fin 2 →₀ ℕ, n.degree = 1 → MvPowerSeries.coeff n F = 1) ∧
      MvPowerSeries.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K), 0] F =
        MvPowerSeries.X 0
def LamModule : Prop :=
  ∀ (K ι : Type) [Finite ι] [NormedField K] [IsUltrametricDist K] [CharZero K] (p : ℕ)
    (σ : K →+* K), p.Prime → ‖(p : K)‖ = (p : ℝ)⁻¹ →
    (∀ a : K, ‖a‖ ≤ 1 → ‖σ a - a ^ p‖ ≤ (p : ℝ)⁻¹) →
    ∀ (h : MvPowerSeries ι K) (N : ℕ), ¬ p ∣ N → Simeq h 0 →
      Simeq (MvPowerSeries.C ((N : K)⁻¹) * h) 0
def StepZero : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (p : ℕ)
    (σ : K →+* K), UnrOK K p σ → (∃ ζ : K, IsPrimitiveRoot ζ (p ^ 2 - 1)) →
    ∀ F : MvPowerSeries (Fin 2) K, IsLawOfLog p F →
    ∀ be : MvPowerSeries (Fin 2) K, BetaHyp p F be →
      ∃ G : MvPowerSeries (Fin 2) K, SuppOK p G ∧ Simeq G be ∧ Simeq (d1 F G) 0 ∧
        Simeq (d1 F (swap2 G)) 0
def FirstDeriv : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (p : ℕ), p.Prime →
    ‖(p : K)‖ = (p : ℝ)⁻¹ →
    ∀ F : MvPowerSeries (Fin 2) K, IsLawOfLog p F →
    ∀ G : MvPowerSeries (Fin 2) K, DivAB G → Simeq (d1 F G) 0 →
      Integral (MvPowerSeries.pderiv (R := K) 0 G -
        at1 0 (PowerSeries.derivative K (lgF K p)) * at1 1 (fLin G))
def CobLin : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (p : ℕ), p.Prime →
    ‖(p : K)‖ = (p : ℝ)⁻¹ →
    ∀ F : MvPowerSeries (Fin 2) K, IsLawOfLog p F →
    ∀ G : MvPowerSeries (Fin 2) K, DivAB G → Simeq (d1 F (swap2 G)) 0 →
      Integral (cob F (fLin G))
def StepI : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] [CompleteSpace K] (p : ℕ)
    (σ : K →+* K), UnrOK K p σ →
    ∀ F : MvPowerSeries (Fin 2) K, IsLawOfLog p F →
    ∀ G : MvPowerSeries (Fin 2) K, SuppOK p G → Simeq (d1 F G) 0 → Simeq (d1 F (swap2 G)) 0 →
      ∃ c : K, ‖c‖ ≤ 1 ∧ DerivIs p G c
def StepII : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (p : ℕ)
    (σ : K →+* K), UnrOK K p σ →
    ∀ F : MvPowerSeries (Fin 2) K, IsLawOfLog p F →
    ∀ (G : MvPowerSeries (Fin 2) K) (c : K), DivAB G → Simeq (d1 F G) 0 → ‖c‖ ≤ 1 →
      DerivIs p G c →
      Integral (d1 F (DeS p σ G) -
        MvPowerSeries.C (σ c) * (in3 (cob F (g0F K p)) * at1 2 (lgF K p)))
def StepH : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] [CompleteSpace K] (p : ℕ)
    (σ : K →+* K), UnrOK K p σ →
    ∀ F : MvPowerSeries (Fin 2) K, IsLawOfLog p F →
    ∀ (G : MvPowerSeries (Fin 2) K) (γ γ' : K), SuppOK p G →
      Integral (d1 F (DeS p σ G) -
        MvPowerSeries.C γ * (in3 (cob F (g0F K p)) * at1 2 (lgF K p))) →
      Integral (d1 F (DeS p σ (swap2 G)) -
        MvPowerSeries.C γ' * (in3 (cob F (g0F K p)) * at1 2 (lgF K p))) →
      Integral (Hser p σ G γ γ')
def StepIII : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (p : ℕ)
    (σ : K →+* K), UnrOK K p σ →
    ∀ (G : MvPowerSeries (Fin 2) K) (c c' : K), ‖c‖ ≤ 1 → ‖c'‖ ≤ 1 → DerivIs p G c →
      Integral (Hser p σ G (σ c) (σ c')) → c + σ c' = 0
def SwapRules : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] (p : ℕ) (σ : K →+* K)
    (G : MvPowerSeries (Fin 2) K) (γ γ' : K), 2 ≤ p →
    swap2 (swap2 G) = G ∧ (SuppOK p G → SuppOK p (swap2 G)) ∧ (DivAB G → DivAB (swap2 G)) ∧
    (Integral G → Integral (swap2 G)) ∧ DeS p σ (swap2 G) = swap2 (DeS p σ G) ∧
    Hser p σ (swap2 G) γ' γ = swap2 (Hser p σ G γ γ')
def StepIV : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (p : ℕ)
    (σ : K →+* K), UnrOK K p σ →
    ∀ (G : MvPowerSeries (Fin 2) K) (c : K), DivAB G → σ (σ c) = c →
      Integral (Hser p σ G (σ c) (-c)) → Simeq G (Gser p c (σ c))
def MapSimeq : Prop :=
  ∀ (K0 K ι : Type) [NormedField K0] [CharZero K0] [NormedField K] [CharZero K] (j : K0 →+* K),
    (∀ a, ‖j a‖ = ‖a‖) →
    (∀ f g : MvPowerSeries ι K0, Simeq f g → Simeq (MvPowerSeries.map j f) (MvPowerSeries.map j g)) ∧
    ∀ (p : ℕ) (c c' : K0), MvPowerSeries.map j (Gser p c c') = Gser p (j c) (j c')
end Formalism.InvariantFactorPaths.G7


