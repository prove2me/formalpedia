-- Prove2me | Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_CrystallineStableLifts_WachCol
-- name    : Formalism_WeaklyAdmissibleFiltrations_CrystallineStableLifts_WachCol
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:24:46.989798+00:00
-- url     : https://prove2.me/theorems/c76963d9-97f0-459a-85e9-d32e2147f9ea
-- title:
--   Wach Col
-- statement:
--   Definitions and structural lemmas for Wach Col, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/WeaklyAdmissibleFiltrations/CrystallineStableLifts/WachCol.lean

import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_CocyclesFunctorial
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.WeaklyAdmissibleFiltrations
open Module
section Abstract
variable {O X H : Type} [CommRing O] [AddCommGroup X] [Module O X] [AddCommGroup H] [Module O H]
end Abstract
section WachSide
open Formalism.CoboundaryTransfers
variable {O A : Type} [CommRing O] [CommRing A] [Algebra O A] {Bw : Base O A} {M : ℕ}
  {D D' : Type} [AddCommGroup D] [Module A D] [Module O D] [IsScalarTower O A D]
  [AddCommGroup D'] [Module A D'] [Module O D'] [IsScalarTower O A D']
end WachSide
end Formalism.WeaklyAdmissibleFiltrations


