-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_PhNormLimit
-- name    : Formalism_PeriodIntegrals_PhNormLimit
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:31:35.410881+00:00
-- url     : https://prove2.me/theorems/ddbe4920-b4ac-4c2c-afbf-a9ca811c5026
-- title:
--   Ph Norm Limit
-- statement:
--   Definitions and structural lemmas for Ph Norm Limit, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/PhNormLimit.lean

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
namespace PI.PhNormLimit
def IsIntP {p : ℕ} [Fact p.Prime] (x : ℂ_[p]) : Prop := ‖x‖ ≤ 1
def IntegralMv {σ : Type*} {p : ℕ} [Fact p.Prime] (F : MvPowerSeries σ ℂ_[p]) : Prop :=
  ∀ n, IsIntP (MvPowerSeries.coeff n F)
def expMv {σ : Type*} {p : ℕ} [Fact p.Prime] (F : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] :=
  fun α => ∑ n ∈ Finset.range ((α.sum fun _ k => k) + 1),
    MvPowerSeries.coeff α (F ^ n) / (n.factorial : ℂ_[p])
def Simeq {σ : Type*} {p : ℕ} [Fact p.Prime] (f g : MvPowerSeries σ ℂ_[p]) : Prop :=
  MvPowerSeries.constantCoeff (f - g) = 0 ∧ IntegralMv (expMv (f - g))
abbrev Xv {p : ℕ} [Fact p.Prime] {σ : Type*} (i : σ) : MvPowerSeries σ ℂ_[p] := MvPowerSeries.X i
def zc {p : ℕ} [Fact p.Prime] (a : ℤ_[p]) : ℂ_[p] := algebraMap ℚ_[p] ℂ_[p] (a : ℚ_[p])
section Ops
variable {p : ℕ} [Fact p.Prime] {σ : Type*}
def add (l ex : PowerSeries ℂ_[p]) (a b : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] :=
  PowerSeries.subst (PowerSeries.subst a l + PowerSeries.subst b l) ex
def mulBy (l ex : PowerSeries ℂ_[p]) (c : ℂ_[p]) (a : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] :=
  PowerSeries.subst (MvPowerSeries.C c * PowerSeries.subst a l) ex
def phAt (ph : PowerSeries ℂ_[p]) (a : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] :=
  PowerSeries.subst a ph
def be (l ex ph : PowerSeries ℂ_[p]) (a b : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] :=
  phAt ph (add l ex a b) - phAt ph a - phAt ph b
end Ops
def Target : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (l ex ph : PowerSeries ℂ_[p]) (T : Set (ℂ_[p] × ℂ_[p])),
    PowerSeries.constantCoeff ex = 0 → PowerSeries.subst ex l = PowerSeries.X →
    (∀ α ∈ T, IntegralMv (mulBy l ex α.1 (Xv ()) : MvPowerSeries Unit ℂ_[p])) →
    (∀ α ∈ T, Simeq (phAt ph (mulBy l ex α.1 (Xv ())) : MvPowerSeries Unit ℂ_[p])
        (MvPowerSeries.C (α.1 * α.2) * phAt ph (Xv ()))) →
    ∀ α ∈ closure T, Simeq (phAt ph (mulBy l ex α.1 (Xv ())) : MvPowerSeries Unit ℂ_[p])
        (MvPowerSeries.C (α.1 * α.2) * phAt ph (Xv ()))
end PI.PhNormLimit


