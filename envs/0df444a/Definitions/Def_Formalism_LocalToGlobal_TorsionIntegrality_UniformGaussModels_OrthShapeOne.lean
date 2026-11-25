-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_UniformGaussModels_OrthShapeOne
-- name    : Formalism_LocalToGlobal_TorsionIntegrality_UniformGaussModels_OrthShapeOne
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T05:10:40.451441+00:00
-- url     : https://prove2.me/theorems/0c87c0df-b541-43f7-89d0-3b01f40d442b
-- title:
--   Orth Shape One
-- statement:
--   Definitions and structural lemmas for Orth Shape One, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/UniformGaussModels/OrthShapeOne.lean

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_UniformGaussModels_IsHypPair
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_IsotropicVanish
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
namespace Formalism.L2.Th1.Top
open Formalism.L2.Th1.D
open Formalism.DworkPowerSeriesWeights (Integral)
open Formalism.InvariantFactorPaths.G7 (lgF at1 Simeq cob UnrOK IsLawOfLog)
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.G (unitBall)
def PhMap : Prop :=
  ∀ (K K' : Type) [Field K] [Field K'] [CharZero K] [CharZero K'] (φ : K →+* K') (l : ℕ), 2 ≤ l →
    ∀ g2 g3 s2 ε : K,
      PowerSeries.map φ (phFF l g2 g3 s2 ε) = phFF l (φ g2) (φ g3) (φ s2) (φ ε)
def CalcC : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], 5 ≤ l →
  ∀ g2 g3 ε s2 : MaximalUnramifiedExtension l, ‖g2‖ ≤ 1 → ‖g3‖ ≤ 1 → ‖ε‖ = 1 →
    (∀ n, ‖PowerSeries.coeff n (thetaS l g2 g3 ε)‖ ≤ 1) →
  ∀ σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l, UnrOK (MaximalUnramifiedExtension l) l σ →
  ∀ F : MvPowerSeries (Fin 2) (MaximalUnramifiedExtension l), IsLawOfLog l F →
  (∀ α : MaximalUnramifiedExtension l, ‖α‖ = 1 → σ (σ α) = α → NormRel l σ (phFF l g2 g3 s2 ε) α) →
    Formalism.L2.Th1.C.Frame (unitBall ℂ_[l]) (lgF ℂ_[l] l) (expF ℂ_[l] l)
      (PowerSeries.map (MaximalUnramifiedExtension l).subtype (phFF l g2 g3 s2 ε)) ∧
    Formalism.L2.Th1.C.F1 (unitBall ℂ_[l]) (lgF ℂ_[l] l) (expF ℂ_[l] l)
      (PowerSeries.map (MaximalUnramifiedExtension l).subtype (phFF l g2 g3 s2 ε)) ∧
    (∀ α : MaximalUnramifiedExtension l, ‖α‖ ≤ 1 → σ (σ α) = α →
      Formalism.L2.Th1.C.EndInt (unitBall ℂ_[l]) (lgF ℂ_[l] l) (expF ℂ_[l] l) (α : ℂ_[l]) ∧
      Formalism.L2.Th1.C.PhNormAt (unitBall ℂ_[l]) (lgF ℂ_[l] l) (expF ℂ_[l] l)
        (PowerSeries.map (MaximalUnramifiedExtension l).subtype (phFF l g2 g3 s2 ε)) (α : ℂ_[l]) ((σ α : MaximalUnramifiedExtension l) : ℂ_[l]) ∧
      Formalism.L2.Th1.C.AdjAt (unitBall ℂ_[l]) (lgF ℂ_[l] l) (expF ℂ_[l] l)
        (PowerSeries.map (MaximalUnramifiedExtension l).subtype (phFF l g2 g3 s2 ε)) (α : ℂ_[l]) ((σ α : MaximalUnramifiedExtension l) : ℂ_[l])) ∧
    (∀ z : MaximalUnramifiedExtension l, ‖z‖ ≤ 1 → σ z = z → Formalism.L2.Th1.C.IsBinomScalar (unitBall ℂ_[l]) (z : ℂ_[l]))
def OrthShape : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], 5 ≤ l → ∀ (L : PeriodPair) (ι : ℂ ≃+* ℂ_[l]),
  ∀ g2 g3 ε s2 : MaximalUnramifiedExtension l, (g2 : ℂ_[l]) = ι L.g₂ → (g3 : ℂ_[l]) = ι L.g₃ →
    (s2 : ℂ_[l]) = ι (Formalism.L2.Th1.F.s2 L) → ‖g2‖ ≤ 1 → ‖g3‖ ≤ 1 →
    ‖(g2 : ℂ_[l]) ^ 3 - 27 * (g3 : ℂ_[l]) ^ 2‖ = 1 → ‖ε‖ = 1 →
    (∀ n, ‖PowerSeries.coeff n (thetaS l g2 g3 ε)‖ ≤ 1) →
  ∀ σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l, UnrOK (MaximalUnramifiedExtension l) l σ →
  ∀ F : MvPowerSeries (Fin 2) (MaximalUnramifiedExtension l), IsLawOfLog l F →
  (∀ α : MaximalUnramifiedExtension l, ‖α‖ = 1 → σ (σ α) = α → NormRel l σ (phFF l g2 g3 s2 ε) α) →
  ∀ (N0 N1 : ℕ) (ιr : Type) [Fintype ιr] [DecidableEq ιr] (n : Type) [Fintype n]
    (f f' : ιr × Fin N0 × Fin N1 → n → MaximalUnramifiedExtension l), IsHypPair σ f f' →
  ∀ ω₀ : ℂ, ω₀ ∈ L.lattice → ω₀ / 2 ∉ L.lattice →
  ∀ (κ : Type) [Fintype κ] (r : κ → ℂ_[l]) (s : κ → n → ℂ) (N : ℕ), (∀ k, ‖r k‖ ≤ 1) → 0 < N →
    ¬ l ∣ N → (∀ k i, (N : ℂ) * s k i ∈ L.lattice) →
    ∃ U0 Φ : MvPowerSeries (Bool × ιr × Fin N0 × Fin N1) ℂ_[l], Integral U0 ∧
      MvPowerSeries.constantCoeff Φ = 0 ∧
      Simeq Φ (sumE (MvPowerSeries.map (MaximalUnramifiedExtension l).subtype (cob F (phFF l g2 g3 s2 ε)))) ∧
      thetaHyp l L ι (ε : ℂ_[l]) ω₀ f f' r s = Formalism.DworkPowerSeriesWeights.mvExp (-Φ) * U0
def OrthShapeOne : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], 5 ≤ l → ∀ (L : PeriodPair) (ι : ℂ ≃+* ℂ_[l]),
  ∀ g2 g3 ε s2 : MaximalUnramifiedExtension l, (g2 : ℂ_[l]) = ι L.g₂ → (g3 : ℂ_[l]) = ι L.g₃ →
    (s2 : ℂ_[l]) = ι (Formalism.L2.Th1.F.s2 L) → ‖g2‖ ≤ 1 → ‖g3‖ ≤ 1 →
    ‖(g2 : ℂ_[l]) ^ 3 - 27 * (g3 : ℂ_[l]) ^ 2‖ = 1 → ‖ε‖ = 1 →
    (∀ n, ‖PowerSeries.coeff n (thetaS l g2 g3 ε)‖ ≤ 1) →
  ∀ (n : Type) [Fintype n],
  ∀ ω₀ : ℂ, ω₀ ∈ L.lattice → ω₀ / 2 ∉ L.lattice →
  ∀ (κ : Type) [Fintype κ] (r : κ → ℂ_[l]) (s : κ → n → ℂ) (N : ℕ), (∀ k, ‖r k‖ ≤ 1) → 0 < N →
    ¬ l ∣ N → (∀ k i, (N : ℂ) * s k i ∈ L.lattice) →
    ∃ U0 : MvPowerSeries n ℂ_[l], Integral U0 ∧
      thetaOrth l L ι (ε : ℂ_[l]) ω₀ r s =
        Formalism.DworkPowerSeriesWeights.mvExp (-(∑ x : n, at1 x (PowerSeries.map (MaximalUnramifiedExtension l).subtype (phFF l g2 g3 s2 ε)))) * U0
end Formalism.L2.Th1.Top


