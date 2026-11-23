-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_FglTriFactor
-- name    : Formalism_PeriodIntegrals_FglTriFactor
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:38:43.86647+00:00
-- url     : https://prove2.me/theorems/d9452a1d-4b18-4032-987c-12b57e15faca
-- title:
--   Fgl Tri Factor
-- statement:
--   Definitions and structural lemmas for Fgl Tri Factor, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/FglTriFactor.lean

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
namespace PI.FglTriFactor
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
def dX {A : Type*} [CommRing A] (f : PowerSeries A) : PowerSeries A :=
  PowerSeries.mk fun n => ((n : A) + 1) * PowerSeries.coeff (n + 1) f
def omegaW {p : ℕ} [Fact p.Prime] (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]) :
    PowerSeries ℂ_[p] :=
  let c := algebraMap ℂ_[p] (PowerSeries ℂ_[p])
  let X := (PowerSeries.X : PowerSeries ℂ_[p])
  (-(2 : PowerSeries ℂ_[p]) * wq - X * dX wq) * (wq * (c W.a₁ * X + c W.a₃ * X ^ 3 * wq - 2))⁻¹
def flog {p : ℕ} [Fact p.Prime] (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]) :
    PowerSeries ℂ_[p] :=
  PowerSeries.mk fun n => if n = 0 then 0 else PowerSeries.coeff (n - 1) (omegaW W wq) / n
def T {p : ℕ} [Fact p.Prime] (wq : PowerSeries ℂ_[p]) : MvPowerSeries (Fin 3) ℂ_[p] :=
  (Xv 0) ^ 3 * PowerSeries.subst (Xv 0 : MvPowerSeries (Fin 3) ℂ_[p]) wq * (Xv 2 - Xv 1) +
    (Xv 1) ^ 3 * PowerSeries.subst (Xv 1 : MvPowerSeries (Fin 3) ℂ_[p]) wq * (Xv 0 - Xv 2) +
    (Xv 2) ^ 3 * PowerSeries.subst (Xv 2 : MvPowerSeries (Fin 3) ℂ_[p]) wq * (Xv 1 - Xv 0)
def Lemma : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (W : WeierstrassCurve ℂ_[p]) (wq ex : PowerSeries ℂ_[p]),
    IsIntP W.a₁ → IsIntP W.a₂ → IsIntP W.a₃ → IsIntP W.a₄ → IsIntP W.a₆ → ‖W.Δ‖ = 1 →
    IsWq W wq → PowerSeries.constantCoeff ex = 0 → PowerSeries.subst ex (flog W wq) = PowerSeries.X →
    IntegralMv (add (flog W wq) ex (Xv 0) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p]) →
    ∃ n : MvPowerSeries (Fin 3) ℂ_[p], IntegralMv n ∧ MvPowerSeries.constantCoeff n = 1 ∧
      T wq = add (flog W wq) ex (add (flog W wq) ex (Xv 0) (Xv 1)) (Xv 2) *
        sub (flog W wq) ex (Xv 0) (Xv 1) * sub (flog W wq) ex (Xv 1) (Xv 2) *
        sub (flog W wq) ex (Xv 2) (Xv 0) * n
end PI.FglTriFactor


