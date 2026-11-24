-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_CurveCocycleIntegralAllResidues
-- name    : Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_CurveCocycleIntegralAllResidues
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-24T21:39:05.042475+00:00
-- url     : https://prove2.me/theorems/52ac569f-b5a0-4e94-9e52-de9aa5f61a4f
-- title:
--   Curve Cocycle Integral All Residues
-- statement:
--   Definitions and structural lemmas for Curve Cocycle Integral All Residues, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/CurveCocycleIntegralAllResidues.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementW
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LawDifferenceThree
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.L2.Th1.B
open Formalism.DworkPowerSeriesWeights (Integral)
open Formalism.InvariantFactorPaths.G7 (Simeq at1 cob d1 swap2 DivAB)
open Formalism.L2.Th1.A (fgl iSer logSer wpReg g₂ g₃ IntModel)
def CurveFrobStick : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (W : WeierstrassCurve K) (s2 : K),
    (at1 0 (sgW W s2) * at1 1 (sgW W s2) * at1 2 (sgW W s2)) ^ 3 * det3 (wpReg W) =
      -2 * (MvPowerSeries.X 0 * MvPowerSeries.X 1 * MvPowerSeries.X 2) ^ 3 *
        (evalSumThree (sgW W s2) * evalDiffThree 0 1 (sgW W s2) * evalDiffThree 0 2 (sgW W s2) * evalDiffThree 1 2 (sgW W s2))
def CurveParThree : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (W : WeierstrassCurve K) (s2 : K),
    IntModel W → Simeq (par3 (fgl W) (iSer W) (phW W s2)) 0
def CurveCocycleIntegralAllResidues : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (W : WeierstrassCurve K) (s2 : K),
    IntModel W →
    DivAB (beW W s2) ∧ swap2 (beW W s2) = beW W s2 ∧
      Simeq (d1 (fgl W) (beW W s2)) 0 ∧ Simeq (d1 (fgl W) (swap2 (beW W s2))) 0 ∧
      ∀ n : ℕ, 3 ≤ n → ‖PowerSeries.constantCoeff ((Dinv (logSer W))^[n] (phW W s2))‖ ≤ 1
end Formalism.L2.Th1.B


