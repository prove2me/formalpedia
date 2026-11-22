-- Prove2me | Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsIsomFix
-- name    : Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsIsomFix
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:22:22.703096+00:00
-- url     : https://prove2.me/theorems/c7cab33a-bd16-43fe-8efa-2eb74af27e2a
-- title:
--   Exists Isom Fix
-- statement:
--   Definitions and structural lemmas for Exists Isom Fix, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsIsomFix.lean

import Definitions.Def_Formalism_HermitianLattices_StatementLat
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.HermitianLattices.Ext.L3.WA
variable {K V : Type*} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
def quasiRefl (h : V →ₗ⋆[K] V →ₗ[K] K) (u : V) (a : K) : V →ₗ[K] V :=
  LinearMap.id - a • (h u).smulRight u
end Formalism.HermitianLattices.Ext.L3.WA


