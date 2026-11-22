-- Prove2me | Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_TendstoTsumDivPow
-- name    : Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_TendstoTsumDivPow
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:22:34.438734+00:00
-- url     : https://prove2.me/theorems/d4ae1e17-d777-4875-a2af-314bbe17a120
-- title:
--   Tendsto Tsum Div Pow
-- statement:
--   Definitions and structural lemmas for Tendsto Tsum Div Pow, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/TendstoTsumDivPow.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module MeasureTheory Filter Topology Bornology Pointwise ZLattice
noncomputable section
namespace Formalism.HermitianLattices.Ext.L3.LatSum
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
variable (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
variable {ι : Type*} [Fintype ι]
end Formalism.HermitianLattices.Ext.L3.LatSum


