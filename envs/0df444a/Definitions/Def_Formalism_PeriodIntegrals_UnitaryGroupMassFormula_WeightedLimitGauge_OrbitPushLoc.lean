-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_OrbitPushLoc
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_OrbitPushLoc
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T08:39:00.972127+00:00
-- url     : https://prove2.me/theorems/784070bc-752d-51a2-a800-fc0bdbb01ca8
-- title:
--   Orbit Push Loc
-- statement:
--   Definitions and structural lemmas for Orbit Push Loc, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeightedLimitGauge/OrbitPushLoc.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RhsWLim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_VolumeLieE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_ChartJac
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_OrbitPushCut
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Matrix
open scoped ENNReal
namespace PI.RhsWLim.W
open PI.RhsWLim
def psiE (k r : ℕ) (T' : ℝ) (q : TrE k) : (Fin k → ℂ) × ℂ :=
  opCo k r (NormedSpace.exp (opGen k r q) *ᵥ opBase k r T')
def kapT (k : ℕ) (v : (Fin k → ℂ) × ℂ) : TrE k :=
  (WithLp.equiv 2 (Option (Fin k × Bool) → ℝ)).symm (fun o => match o with
    | none => Complex.arg v.2
    | some (a, b) => if b then (v.1 a).im else (v.1 a).re)
def phiT (k r : ℕ) (T' : ℝ) (q : TrE k) : TrE k := kapT k (psiE k r T' q)
def HypChart : Prop :=
  ∀ (k r : ℕ) (T' : ℝ), 1 ≤ k → 0 < T' → ∃ ε > 0, ∀ ρ : ℝ, 0 < ρ → ρ < ε →
    hypM k T' (opE k r T' ρ) = (1 / 2) * volume (phiT k r T' '' Metric.ball 0 ρ)
def PhiDiff : Prop :=
  ∀ (k r : ℕ) (T' : ℝ), 1 ≤ k → 0 < T' →
    ContDiffAt ℝ 1 (phiT k r T') 0 ∧ (fderiv ℝ (phiT k r T') 0).det = (T' / 2) ^ k
end PI.RhsWLim.W


