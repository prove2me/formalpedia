-- Prove2me | Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_JetsCube
-- name    : Formalism_EllipticTorsion_EllipticTorsionProofs_JetsCube
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:58:46.581821+00:00
-- url     : https://prove2.me/theorems/29150f8e-a71d-4f87-8e48-487cdfbac1ad
-- title:
--   Jets Cube
-- statement:
--   Definitions and structural lemmas for Jets Cube, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/JetsCube.lean

import Mathlib
import Definitions.Def_Formalism_EllipticTorsion_JetsCube
import Definitions.Def_Formalism_FormalGroupLog_LogDeterminesLaw
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
universe u
noncomputable section
namespace Formalism.ELL.FormalGroupCubeJets
open MvPowerSeries Formalism.G Formalism.G.LogCR Formalism.G.LogP
variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CharZero K]
variable (F : FormalGroup (unitBall K))
def Dj (j : Fin 3) (g : MvPowerSeries (Fin 3) K) : MvPowerSeries (Fin 3) K :=
  (omegaF F).subst (MvPowerSeries.X j : MvPowerSeries (Fin 3) K) * MvPowerSeries.pderiv K j g
end Formalism.ELL.FormalGroupCubeJets
namespace Formalism.ELL
end Formalism.ELL


