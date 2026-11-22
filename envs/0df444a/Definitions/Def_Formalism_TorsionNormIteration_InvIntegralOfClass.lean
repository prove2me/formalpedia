-- Prove2me | Definitions.Def_Formalism_TorsionNormIteration_InvIntegralOfClass
-- name    : Formalism_TorsionNormIteration_InvIntegralOfClass
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:06:47.453082+00:00
-- url     : https://prove2.me/theorems/531c546e-d6dc-4abb-8a84-d504d7e81ce3
-- title:
--   Inv Integral Of Class
-- statement:
--   Definitions and structural lemmas for Inv Integral Of Class, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InvIntegralOfClass.lean

import Definitions.Def_Formalism_FormalGroupLog_Statement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PowerSeries
universe u v
namespace Formalism.LT
open Formalism.G
def DivByMv {K : Type u} [NormedField K] {ι : Type v} (x : K) (F : MvPowerSeries ι K) : Prop :=
  ∀ d : ι →₀ ℕ, ‖MvPowerSeries.coeff d F‖ ≤ ‖x‖
def SolveExists : Prop :=
  ∀ (R : Type u) [CommRing R] (ι : Type v) [Finite ι] (f : PowerSeries R)
    (G : MvPowerSeries ι R),
    constantCoeff f = 0 → coeff 1 f = 1 → MvPowerSeries.constantCoeff G = 0 →
      ∃ h : MvPowerSeries ι R, MvPowerSeries.constantCoeff h = 0 ∧ f.subst h = G
def InvIntegralOfClass : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] (ι : Type v) [Finite ι]
    (C : MvPowerSeries ι K → Prop) (f : PowerSeries K),
    constantCoeff f = 0 → coeff 1 f = 1 →
    (∀ a b, C a → C b → C (a - b)) →
    (∀ P : MvPowerSeries ι K, MvPowerSeries.constantCoeff P = 0 → IntegralMv P →
      C (f.subst P)) →
    (∀ D, C D → ∀ N : ℕ, 1 ≤ N →
      (∀ d : ι →₀ ℕ, d.degree < N → MvPowerSeries.coeff d D = 0) →
      ∀ d : ι →₀ ℕ, d.degree = N → ‖MvPowerSeries.coeff d D‖ ≤ 1) →
    ∀ h : MvPowerSeries ι K, MvPowerSeries.constantCoeff h = 0 → C (f.subst h) → IntegralMv h
def FunEqLowCoeff : Prop :=
  ∀ (K : Type u) [NormedField K] (ι : Type v) (p q : ℕ) (hq : q ≠ 0) (σ : K →+* K), 2 ≤ q →
    ∀ D : MvPowerSeries ι K, IsFunEqTypeMv p q hq σ D → ∀ N : ℕ, 1 ≤ N →
      (∀ d : ι →₀ ℕ, d.degree < N → MvPowerSeries.coeff d D = 0) →
      ∀ d : ι →₀ ℕ, d.degree = N → ‖MvPowerSeries.coeff d D‖ ≤ 1
def IntegralSubst : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] (ι : Type v) (f : PowerSeries K)
    (P : MvPowerSeries ι K),
    IntegralPS f → MvPowerSeries.constantCoeff P = 0 → IntegralMv P → IntegralMv (f.subst P)
def CoeffBound : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CharZero K] (p q : ℕ) (σ : K →+* K),
    FunctionalEquationSetting K p q σ →
    ∀ f : PowerSeries K, constantCoeff f = 0 → IsFunEqType p q σ f →
      ∀ n : ℕ, ∃ k : ℕ, q ^ k ∣ n ∧ ‖coeff n f‖ * ‖(p : K)‖ ^ k ≤ 1
def PowCongr : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] (ι : Type v) (p : ℕ), p.Prime →
    ∀ A B : MvPowerSeries ι K, IntegralMv A → IntegralMv B → ∀ r : ℕ, 1 ≤ r →
      DivByMv ((p : K) ^ r) (A - B) →
      ∀ j m : ℕ, DivByMv ((p : K) ^ (r + j)) (A ^ (p ^ j * m) - B ^ (p ^ j * m))
def FrobCongr : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CharZero K] (p q : ℕ) (hq : q ≠ 0)
    (σ : K →+* K), FunctionalEquationSetting K p q σ →
    ∀ (ι : Type v) (A : MvPowerSeries ι K), IntegralMv A →
      DivByMv (p : K) (A ^ q - MvPowerSeries.expand q hq (MvPowerSeries.map σ A))
end Formalism.LT


