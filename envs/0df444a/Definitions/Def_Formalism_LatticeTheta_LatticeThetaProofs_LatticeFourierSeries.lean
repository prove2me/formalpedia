-- Prove2me | Definitions.Def_Formalism_LatticeTheta_LatticeThetaProofs_LatticeFourierSeries
-- name    : Formalism_LatticeTheta_LatticeThetaProofs_LatticeFourierSeries
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T17:09:06.165325+00:00
-- url     : https://prove2.me/theorems/0125dc5e-e671-4048-bb25-a39b847e236a
-- title:
--   Lattice Fourier Series
-- statement:
--   Definitions and structural lemmas for Lattice Fourier Series, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LatticeTheta/LatticeThetaProofs/LatticeFourierSeries.lean

import Definitions.Def_Formalism_LatticeTheta_LatticeThetaProofs_TorusProjIsOpenQuotientMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set Complex
open scoped RealInnerProductSpace
noncomputable section
namespace Formalism.H
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
end Formalism.H


