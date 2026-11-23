-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_CubicExponentialFactor
-- name    : Formalism_PeriodIntegrals_CubicExponentialFactor
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:38:03.371083+00:00
-- url     : https://prove2.me/theorems/1e17a119-b2d7-4ccd-b843-cb902e03cdd1
-- title:
--   Cubic Exponential Factor
-- statement:
--   Definitions and structural lemmas for Cubic Exponential Factor, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/CubicExponentialFactor.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Classical
namespace PI.CubicExponentialFactor
def IsIntP {p : ℕ} [Fact p.Prime] (x : ℂ_[p]) : Prop := ‖x‖ ≤ 1
def IntegralMv {σ : Type*} {p : ℕ} [Fact p.Prime] (F : MvPowerSeries σ ℂ_[p]) : Prop :=
  ∀ n, IsIntP (MvPowerSeries.coeff n F)
abbrev Xv {p : ℕ} [Fact p.Prime] {σ : Type*} (i : σ) : MvPowerSeries σ ℂ_[p] := MvPowerSeries.X i
section
variable {p : ℕ} [Fact p.Prime] (l ex : PowerSeries ℂ_[p]) {σ : Type*}
def lg (a : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] := PowerSeries.subst a l
def pt (x : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] := PowerSeries.subst x ex
def add (a b : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] := pt ex (lg l a + lg l b)
def sub (a b : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] := pt ex (lg l a - lg l b)
end
def IsWq {p : ℕ} [Fact p.Prime] (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]) : Prop :=
  let c := algebraMap ℂ_[p] (PowerSeries ℂ_[p])
  let X := (PowerSeries.X : PowerSeries ℂ_[p])
  wq = 1 + c W.a₁ * X * wq + c W.a₂ * X ^ 2 * wq + c W.a₃ * X ^ 3 * wq ^ 2 +
    c W.a₄ * X ^ 4 * wq ^ 2 + c W.a₆ * X ^ 6 * wq ^ 3
def logMv {σ : Type*} {p : ℕ} [Fact p.Prime] (F : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] :=
  fun α => ∑ n ∈ Finset.range ((α.sum fun _ k => k) + 1),
    if n = 0 then 0 else (-1 : ℂ_[p]) ^ (n + 1) * MvPowerSeries.coeff α ((F - 1) ^ n) / (n : ℂ_[p])
def expMv {σ : Type*} {p : ℕ} [Fact p.Prime] (F : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] :=
  fun α => ∑ n ∈ Finset.range ((α.sum fun _ k => k) + 1),
    MvPowerSeries.coeff α (F ^ n) / (n.factorial : ℂ_[p])
def Simeq {σ : Type*} {p : ℕ} [Fact p.Prime] (f g : MvPowerSeries σ ℂ_[p]) : Prop :=
  MvPowerSeries.constantCoeff (f - g) = 0 ∧ IntegralMv (expMv (f - g))
def phAt {p : ℕ} [Fact p.Prime] {σ : Type*} (E : PowerSeries ℂ_[p]) (a : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] :=
  PowerSeries.subst a (-logMv E : PowerSeries ℂ_[p])
def eAt {p : ℕ} [Fact p.Prime] {σ : Type*} (E : PowerSeries ℂ_[p]) (a : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] :=
  PowerSeries.subst a E
def Lemma : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (W : WeierstrassCurve ℂ_[p]) (wq l ex E : PowerSeries ℂ_[p])
    (T : MvPowerSeries (Fin 3) ℂ_[p]),
    IsIntP W.a₁ → IsIntP W.a₂ → IsIntP W.a₃ → IsIntP W.a₄ → IsIntP W.a₆ → IsWq W wq →
    PowerSeries.constantCoeff ex = 0 → PowerSeries.subst ex l = PowerSeries.X →
    PowerSeries.constantCoeff E = 1 →
    T * eAt E (Xv 0 : MvPowerSeries (Fin 3) ℂ_[p]) ^ 3 * eAt E (Xv 1 : MvPowerSeries (Fin 3) ℂ_[p]) ^ 3 *
        eAt E (Xv 2 : MvPowerSeries (Fin 3) ℂ_[p]) ^ 3 =
      eAt wq (Xv 0 : MvPowerSeries (Fin 3) ℂ_[p]) * eAt wq (Xv 1 : MvPowerSeries (Fin 3) ℂ_[p]) *
        eAt wq (Xv 2 : MvPowerSeries (Fin 3) ℂ_[p]) *
        (add l ex (add l ex (Xv 0) (Xv 1)) (Xv 2) * eAt E (add l ex (add l ex (Xv 0) (Xv 1)) (Xv 2))) *
        (sub l ex (Xv 0) (Xv 1) * eAt E (sub l ex (Xv 0) (Xv 1))) *
        (sub l ex (Xv 1) (Xv 2) * eAt E (sub l ex (Xv 1) (Xv 2))) *
        (sub l ex (Xv 2) (Xv 0) * eAt E (sub l ex (Xv 2) (Xv 0))) →
    (∃ n : MvPowerSeries (Fin 3) ℂ_[p], IntegralMv n ∧ MvPowerSeries.constantCoeff n = 1 ∧
      T = add l ex (add l ex (Xv 0) (Xv 1)) (Xv 2) * sub l ex (Xv 0) (Xv 1) * sub l ex (Xv 1) (Xv 2) *
        sub l ex (Xv 2) (Xv 0) * n) →
    Simeq (phAt E (add l ex (add l ex (Xv 0) (Xv 1)) (Xv 2)) + phAt E (sub l ex (Xv 0) (Xv 1)) +
        phAt E (sub l ex (Xv 1) (Xv 2)) + phAt E (sub l ex (Xv 2) (Xv 0)) : MvPowerSeries (Fin 3) ℂ_[p])
      (3 * (phAt E (Xv 0) + phAt E (Xv 1) + phAt E (Xv 2)))
end PI.CubicExponentialFactor


