-- Prove2me | Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsOrthTransfer
-- name    : Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsOrthTransfer
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:38:59.483513+00:00
-- url     : https://prove2.me/theorems/e41018c0-0d87-4a93-a9a2-6c97382e355f
-- title:
--   Exists Orth Transfer
-- statement:
--   Definitions and structural lemmas for Exists Orth Transfer, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsOrthTransfer.lean

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsIsomScale
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.HermitianLattices.Ext.L3.U0
open WA Module
variable {K V : Type*} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
variable {S : Subring K} {π : K} {h : V →ₗ⋆[K] V →ₗ[K] K}
end Formalism.HermitianLattices.Ext.L3.U0


