-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_PhEven
-- name    : Formalism_PeriodIntegrals_PhEven
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:25:05.029077+00:00
-- url     : https://prove2.me/theorems/f2f31371-5d8a-48ff-a36c-452e33787568
-- title:
--   Ph Even
-- statement:
--   Definitions and structural lemmas for Ph Even, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/PhEven.lean

import Definitions.Def_Formalism_PeriodIntegrals_AddIntG
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.PhEven
open PI.AddIntG
def logMv {σ : Type*} {p : ℕ} [Fact p.Prime] (F : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] :=
  fun α => ∑ n ∈ Finset.range ((α.sum fun _ k => k) + 1),
    if n = 0 then 0 else (-1 : ℂ_[p]) ^ (n + 1) * MvPowerSeries.coeff α ((F - 1) ^ n) / (n : ℂ_[p])
def ePhi {p : ℕ} [Fact p.Prime] (l s : PowerSeries ℂ_[p]) (ep : ℂ_[p]) : PowerSeries ℂ_[p] :=
  PowerSeries.mk fun n => ep⁻¹ * PowerSeries.coeff (n + 1)
    (PowerSeries.subst (algebraMap ℂ_[p] (PowerSeries ℂ_[p]) ep * l) s)
def ph {p : ℕ} [Fact p.Prime] (l s : PowerSeries ℂ_[p]) (ep : ℂ_[p]) : PowerSeries ℂ_[p] := -logMv (ePhi l s ep)
def OddDeriv : Prop :=
  ∀ G : ℂ → ℂ, (∀ z, G (-z) = -G z) → ∀ n, Even n → iteratedDeriv n G 0 = 0
def WqEven : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]),
    W.a₁ = 0 → W.a₃ = 0 → IsWq W wq → ∀ n, Odd n → PowerSeries.coeff n wq = 0
def LogOdd : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]),
    W.a₁ = 0 → W.a₃ = 0 → IsWq W wq → ∀ n, Even n → PowerSeries.coeff n (flog W wq) = 0
def ExOdd : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (l ex : PowerSeries K),
    (∀ n, Even n → PowerSeries.coeff n l = 0) → PowerSeries.coeff 1 l = 1 →
    PowerSeries.constantCoeff ex = 0 → PowerSeries.subst ex l = PowerSeries.X →
    ∀ n, Even n → PowerSeries.coeff n ex = 0
def Target : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (W : WeierstrassCurve ℂ_[p]) (wq ex s : PowerSeries ℂ_[p]) (ep : ℂ_[p]),
    W.a₁ = 0 → W.a₃ = 0 → IsWq W wq →
    PowerSeries.constantCoeff ex = 0 → PowerSeries.subst ex (flog W wq) = PowerSeries.X →
    (∀ n, Even n → PowerSeries.coeff n s = 0) →
    (PowerSeries.subst (MvPowerSeries.C (-1) * PowerSeries.subst (Xv ()) (flog W wq)) ex : MvPowerSeries Unit ℂ_[p]) = -Xv () ∧
    (PowerSeries.subst (-Xv ()) (ph (flog W wq) s ep) : MvPowerSeries Unit ℂ_[p]) =
      PowerSeries.subst (Xv ()) (ph (flog W wq) s ep)
end PI.PhEven
end


