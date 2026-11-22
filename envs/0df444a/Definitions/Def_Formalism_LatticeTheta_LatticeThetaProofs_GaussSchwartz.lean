-- Prove2me | Definitions.Def_Formalism_LatticeTheta_LatticeThetaProofs_GaussSchwartz
-- name    : Formalism_LatticeTheta_LatticeThetaProofs_GaussSchwartz
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T16:50:38.343494+00:00
-- url     : https://prove2.me/theorems/ef0fd96f-843b-4de5-b76a-fa32b52cc9aa
-- title:
--   Gauss Schwartz
-- statement:
--   Definitions and structural lemmas for Gauss Schwartz, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LatticeTheta/LatticeThetaProofs/GaussSchwartz.lean

import Definitions.Def_Formalism_LatticeTheta_LatticeSummableDecay
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Asymptotics Complex
open scoped FourierTransform RealInnerProductSpace SchwartzMap
noncomputable section
namespace Formalism.H
variable (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
end Formalism.H


