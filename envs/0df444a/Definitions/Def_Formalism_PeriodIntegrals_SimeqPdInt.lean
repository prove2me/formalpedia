-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_SimeqPdInt
-- name    : Formalism_PeriodIntegrals_SimeqPdInt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:31:38.168377+00:00
-- url     : https://prove2.me/theorems/0d22d852-6a10-4df0-bc6d-92ad9b402890
-- title:
--   Simeq Pd Int
-- statement:
--   Definitions and structural lemmas for Simeq Pd Int, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/SimeqPdInt.lean

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
namespace PI.SimeqPdInt
def IsIntP {p : ℕ} [Fact p.Prime] (x : ℂ_[p]) : Prop := ‖x‖ ≤ 1
def IntegralMv {σ : Type*} {p : ℕ} [Fact p.Prime] (F : MvPowerSeries σ ℂ_[p]) : Prop :=
  ∀ n, IsIntP (MvPowerSeries.coeff n F)
def expMv {σ : Type*} {p : ℕ} [Fact p.Prime] (F : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] :=
  fun α => ∑ n ∈ Finset.range ((α.sum fun _ k => k) + 1),
    MvPowerSeries.coeff α (F ^ n) / (n.factorial : ℂ_[p])
def Simeq {σ : Type*} {p : ℕ} [Fact p.Prime] (f g : MvPowerSeries σ ℂ_[p]) : Prop :=
  MvPowerSeries.constantCoeff (f - g) = 0 ∧ IntegralMv (expMv (f - g))
def pd {σ : Type*} [DecidableEq σ] {A : Type*} [CommRing A] (k : σ) (F : MvPowerSeries σ A) :
    MvPowerSeries σ A :=
  fun n => ((n k : A) + 1) * MvPowerSeries.coeff (n + Finsupp.single k 1) F
def Target : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (σ : Type) [DecidableEq σ] (f : MvPowerSeries σ ℂ_[p]), Simeq f 0 →
    ∀ k : σ, IntegralMv (pd k f)
end PI.SimeqPdInt


