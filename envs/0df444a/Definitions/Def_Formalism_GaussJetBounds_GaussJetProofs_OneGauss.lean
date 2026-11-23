-- Prove2me | Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_OneGauss
-- name    : Formalism_GaussJetBounds_GaussJetProofs_OneGauss
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T06:41:12.727824+00:00
-- url     : https://prove2.me/theorems/505e6730-2500-4951-b016-68669f4dd7b7
-- title:
--   One Gauss
-- statement:
--   Definitions and structural lemmas for One Gauss, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/OneGauss.lean

import Definitions.Def_Formalism_GaussJetBounds_StatementU
import Definitions.Def_Formalism_GaussJetBounds_OneLetterRadius
import Definitions.Def_Formalism_GaussJetBounds_MonoShapeTop
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_GField
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_Transfer
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_FJEval
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_Labels
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ThmAOp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace Formalism.DworkPowerSeriesWeights
open Formalism.IncomingBounds
namespace OneGauss
def expo {K : Type} [Field K] {τ ι : Type} [Fintype τ] (v : τ → MvPowerSeries ι K) (sgn ep : K)
    (be : MvPowerSeries (ZMod 2) K) : MvPowerSeries ι K :=
  (sgn / 2) • ∑ x : τ, MvPowerSeries.subst
    (fun s : ZMod 2 => (if s = 0 then (1 : K) else ep) • v x) be
section Expo
variable {K : Type} [Field K] {τ ι : Type} [Fintype τ]
end Expo
section Theta
variable {K : Type} [NormedField K] [CharZero K] {N0 N1 : ℕ}
end Theta
def frA {K : Type} [Field K] {N0 N1 : ℕ} (Y : Fin N0 × Fin N0 → K) :
    Fin N0 × Fin N1 → Fin N0 × Fin N1 → K :=
  fun y z => if y.2 = z.2 then Y (y.1, z.1) else 0
end OneGauss
end Formalism.DworkPowerSeriesWeights


