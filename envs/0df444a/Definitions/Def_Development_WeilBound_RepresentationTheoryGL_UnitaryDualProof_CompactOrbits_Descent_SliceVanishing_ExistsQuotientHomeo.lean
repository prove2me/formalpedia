-- Prove2me | Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_CompactOrbits_Descent_SliceVanishing_ExistsQuotientHomeo
-- name    : Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_CompactOrbits_Descent_SliceVanishing_ExistsQuotientHomeo
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T21:52:04.046297+00:00
-- url     : https://prove2.me/theorems/0a64621b-7dcf-4686-84e3-e5383e8e7edd
-- title:
--   Exists Quotient Homeo
-- statement:
--   Definitions and structural lemmas for Exists Quotient Homeo, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/UnitaryDualProof/CompactOrbits/Descent/SliceVanishing/ExistsQuotientHomeo.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PositivityTheory.RgUd.T.Desc.SLF
open MulAction
variable {G T : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SigmaCompactSpace G]
  [TopologicalSpace T] [T2Space T] [BaireSpace T] [MulAction G T] [ContinuousSMul G T] [IsPretransitive G T]
end PositivityTheory.RgUd.T.Desc.SLF


