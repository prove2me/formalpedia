-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ExistsSmoothExt
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_ExistsSmoothExt
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-24T14:09:47.897128+00:00
-- url     : https://prove2.me/theorems/7ee04d01-b730-4f65-88e6-4733dd85191d
-- title:
--   Exists Smooth Ext
-- statement:
--   Definitions and structural lemmas for Exists Smooth Ext, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ExistsSmoothExt.lean

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Mathlib.Geometry.Manifold.PartitionOfUnity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Set Filter Topology
open scoped Manifold ContDiff
noncomputable section
namespace Formalism.FourierDecayAlt.P.SmoothExtensionClosedSet
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt
end Formalism.FourierDecayAlt.P.SmoothExtensionClosedSet


