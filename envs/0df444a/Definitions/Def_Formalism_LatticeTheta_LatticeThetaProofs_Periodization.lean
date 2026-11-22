-- Prove2me | Definitions.Def_Formalism_LatticeTheta_LatticeThetaProofs_Periodization
-- name    : Formalism_LatticeTheta_LatticeThetaProofs_Periodization
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T16:50:43.935296+00:00
-- url     : https://prove2.me/theorems/2ebb077b-0ec6-4bdf-a46e-8d34db851efb
-- title:
--   Periodization
-- statement:
--   Definitions and structural lemmas for Periodization, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LatticeTheta/LatticeThetaProofs/Periodization.lean

import Definitions.Def_Formalism_LatticeTheta_LatticeSummableDecay
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Asymptotics Complex Metric
open scoped RealInnerProductSpace
noncomputable section
namespace Formalism.H
namespace PoissonPeriodization
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
end PoissonPeriodization
end Formalism.H


