-- Prove2me | Definitions.Def_Formalism_CoboundaryTransfers_GammaStableTransfers_DiffOneSmulOfTower
-- name    : Formalism_CoboundaryTransfers_GammaStableTransfers_DiffOneSmulOfTower
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:25:21.08372+00:00
-- url     : https://prove2.me/theorems/c51f8353-063d-47ea-96e3-0942d81a317b
-- title:
--   Diff One Smul Of Tower
-- statement:
--   Definitions and structural lemmas for Diff One Smul Of Tower, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CoboundaryTransfers/GammaStableTransfers/DiffOneSmulOfTower.lean

import Definitions.Def_Formalism_CoboundaryTransfers_StatementAPI
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.CoboundaryTransfers
section DiagramChase₂
variable {O A : Type} [CommRing O] [CommRing A] [Algebra O A] {B : Base O A} {M : ℕ}
  {D : Type} [AddCommGroup D] [Module A D] [Module O D] [IsScalarTower O A D]
  {D' : Type} [AddCommGroup D'] [Module A D'] [Module O D'] [IsScalarTower O A D']
end DiagramChase₂
end Formalism.CoboundaryTransfers


