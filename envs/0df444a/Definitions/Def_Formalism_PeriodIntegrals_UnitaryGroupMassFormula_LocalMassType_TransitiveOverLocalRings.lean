-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalMassType_TransitiveOverLocalRings
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalMassType_TransitiveOverLocalRings
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:12:10.013794+00:00
-- url     : https://prove2.me/theorems/047b32e7-2b65-47ac-9baf-d084b2e31d38
-- title:
--   Transitive Over Local Rings
-- statement:
--   Definitions and structural lemmas for Transitive Over Local Rings, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalMassType/TransitiveOverLocalRings.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalMassType_WCoreDef
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.LocMassTypW.WCoreP
open Matrix Module
def k1 {R : Type*} [CommRing R] {n m : ℕ} (A B0 B : Matrix (Fin n) (Fin m) R)
    (L0 M : Matrix (Fin m) (Fin n) R) : Matrix (Fin n) (Fin n) R :=
  A * L0 + Mᵀ * B0ᵀ - Mᵀ * Bᵀ * A * L0
end PI.LocMassTypW.WCoreP
namespace PI.LocMassTypW
open Matrix WCoreP
end PI.LocMassTypW


