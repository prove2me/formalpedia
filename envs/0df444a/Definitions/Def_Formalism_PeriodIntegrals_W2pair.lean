-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_W2pair
-- name    : Formalism_PeriodIntegrals_W2pair
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:25:22.704629+00:00
-- url     : https://prove2.me/theorems/04ff3d5a-29ae-4c82-a82b-db0f3d92b36a
-- title:
--   W2pair
-- statement:
--   Definitions and structural lemmas for W2pair, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/W2pair.lean

import Definitions.Def_Formalism_PeriodIntegrals_ExpIntW
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
namespace PI
def WfEndDefs.W2pair (p : ℕ) [Fact p.Prime] : Set (ℂ_[p] × ℂ_[p]) :=
  closure (Subring.closure {x : ℂ_[p] × ℂ_[p] | ∃ ζ : ℂ_[p], ζ ^ (p ^ 2 - 1) = 1 ∧ x = (ζ, ζ ^ p)} :
    Set (ℂ_[p] × ℂ_[p]))
def mulBy {p : ℕ} [Fact p.Prime] {σ : Type*} (l ex : PowerSeries ℂ_[p]) (c : ℂ_[p]) (a : MvPowerSeries σ ℂ_[p]) :
    MvPowerSeries σ ℂ_[p] :=
  PowerSeries.subst (MvPowerSeries.C c * PowerSeries.subst a l) ex
def PairW : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], ∀ α ∈ WfEndDefs.W2pair p, α.1 ∈ Wp p
def WfEnd : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (W : WeierstrassCurve ℂ_[p]) (wq ex : PowerSeries ℂ_[p]),
    W.a₁ ∈ Wp p → W.a₂ ∈ Wp p → W.a₃ ∈ Wp p → W.a₄ ∈ Wp p → W.a₆ ∈ Wp p → AddIntG.IsWq W wq →
    PowerSeries.constantCoeff ex = 0 → PowerSeries.subst ex (AddIntG.flog W wq) = PowerSeries.X →
    ∀ c : ℂ_[p], InWf c →
      IntegralMv (mulBy (AddIntG.flog W wq) ex c (MvPowerSeries.X ()) : MvPowerSeries Unit ℂ_[p]) →
      IntegralW (mulBy (AddIntG.flog W wq) ex c (MvPowerSeries.X ()) : MvPowerSeries Unit ℂ_[p])
end PI
end


