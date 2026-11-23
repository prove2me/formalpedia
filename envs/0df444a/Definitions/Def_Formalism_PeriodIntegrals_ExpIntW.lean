-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_ExpIntW
-- name    : Formalism_PeriodIntegrals_ExpIntW
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:22:33.361082+00:00
-- url     : https://prove2.me/theorems/61b48e7e-e97f-4205-804f-3c2241b23ff3
-- title:
--   Exp Int W
-- statement:
--   Definitions and structural lemmas for Exp Int W, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/ExpIntW.lean

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
namespace PI
def IsIntP {p : ℕ} [Fact p.Prime] (x : ℂ_[p]) : Prop := ‖x‖ ≤ 1
def IntegralMv {σ : Type*} {p : ℕ} [Fact p.Prime] (F : MvPowerSeries σ ℂ_[p]) : Prop :=
  ∀ n, IsIntP (MvPowerSeries.coeff n F)
def expMv {σ : Type*} {p : ℕ} [Fact p.Prime] (F : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] :=
  fun α => ∑ n ∈ Finset.range ((α.sum fun _ k => k) + 1),
    MvPowerSeries.coeff α (F ^ n) / (n.factorial : ℂ_[p])
def Wp (p : ℕ) [Fact p.Prime] : Subring ℂ_[p] :=
  (Subring.closure {ζ : ℂ_[p] | ∃ n : ℕ, 0 < n ∧ Nat.Coprime n p ∧ ζ ^ n = 1}).topologicalClosure
def InWf {p : ℕ} [Fact p.Prime] (x : ℂ_[p]) : Prop := ∃ k : ℕ, (p : ℂ_[p]) ^ k * x ∈ Wp p
def IntegralW {σ : Type*} {p : ℕ} [Fact p.Prime] (F : MvPowerSeries σ ℂ_[p]) : Prop :=
  ∀ n, MvPowerSeries.coeff n F ∈ Wp p
def CoefWf {σ : Type*} {p : ℕ} [Fact p.Prime] (F : MvPowerSeries σ ℂ_[p]) : Prop :=
  ∀ n, InWf (MvPowerSeries.coeff n F)
def Simeq {σ : Type*} {p : ℕ} [Fact p.Prime] (f g : MvPowerSeries σ ℂ_[p]) : Prop :=
  MvPowerSeries.constantCoeff (f - g) = 0 ∧ IntegralMv (expMv (f - g))
def SimeqW {σ : Type*} {p : ℕ} [Fact p.Prime] (f g : MvPowerSeries σ ℂ_[p]) : Prop :=
  MvPowerSeries.constantCoeff (f - g) = 0 ∧ IntegralW (expMv (f - g))
def ExpIntW : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (σ : Type) (f : MvPowerSeries σ ℂ_[p]), CoefWf f → Simeq f 0 → SimeqW f 0
end PI
end


