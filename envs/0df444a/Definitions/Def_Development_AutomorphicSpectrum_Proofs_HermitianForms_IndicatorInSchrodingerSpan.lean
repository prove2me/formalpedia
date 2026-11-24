-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_HermitianForms_IndicatorInSchrodingerSpan
-- name    : Development_AutomorphicSpectrum_Proofs_HermitianForms_IndicatorInSchrodingerSpan
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:04:00.194152+00:00
-- url     : https://prove2.me/theorems/955e0ace-376e-458e-a4b7-cb2798e8e90d
-- title:
--   Indicator In Schrodinger Span
-- statement:
--   Definitions and structural lemmas for Indicator In Schrodinger Span, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/HermitianForms/IndicatorInSchrodingerSpan.lean

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_SWXSDefs
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsSelfDualOfDualSubgroups
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory HeckeCharacterZeroLocus.SiegelWeilU Filter Topology
namespace GlobalTheory.CompanionTheory.SDPadic
variable {V : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [MeasurableSpace V] [BorelSpace V] [T2Space V] [LocallyCompactSpace V] [SecondCountableTopology V]
end GlobalTheory.CompanionTheory.SDPadic


