-- Prove2me | Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_JetsTwo
-- name    : Formalism_EllipticTorsion_EllipticTorsionProofs_JetsTwo
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:58:54.384319+00:00
-- url     : https://prove2.me/theorems/e6649e3f-722a-4c21-88ce-5ac83b5dc1e1
-- title:
--   Jets Two
-- statement:
--   Definitions and structural lemmas for Jets Two, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/JetsTwo.lean

import Definitions.Def_Formalism_EllipticTorsion_JetsCube
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ConstantCoeffSubstOfZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
noncomputable section
namespace Formalism.ELL.FormalGroupQuadraticJets
open Formalism.G.LogCR
variable {K : Type*} [CommRing K]
def ccd (i : Fin 2) (H : MvPowerSeries (Fin 2) K) : K :=
  MvPowerSeries.constantCoeff (MvPowerSeries.pderiv K i H)
def Q (H : MvPowerSeries (Fin 2) K) : K :=
  MvPowerSeries.constantCoeff (MvPowerSeries.pderiv K 1 (MvPowerSeries.pderiv K 0 H))
end Formalism.ELL.FormalGroupQuadraticJets
namespace Formalism.ELL.FormalGroupQuadraticJets
open Formalism.G.LogCR
variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CharZero K]
end Formalism.ELL.FormalGroupQuadraticJets
namespace Formalism.ELL
open Formalism.G Formalism.ELL.FormalGroupQuadraticJets Formalism.G.LogCR
end Formalism.ELL


