-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensFFS
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensFFS
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:11:02.802817+00:00
-- url     : https://prove2.me/theorems/cd238b20-1e14-4be1-9687-34c817815657
-- title:
--   Loc Dens FFS
-- statement:
--   Definitions and structural lemmas for Loc Dens FFS, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/LocDensFFS.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensFF
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.VolStabW
namespace FiniteFieldSplitting
open Matrix
variable {k : Type} [Field k] [Finite k]
def cols {M a : ℕ} (P : Matrix (Fin M) (Fin a) k) : Fin a → Fin M → k := fun j i ↦ P i j
end FiniteFieldSplitting
namespace FiniteFieldSplitting
open Matrix
variable {k : Type} [Field k] [Finite k] {M a : ℕ}
abbrev swapR (k : Type) [Field k] : k × k →+* k × k := (RingEquiv.prodComm (R := k) (S := k)).toRingHom
def U1 (X : Fin a → Fin M → k × k) : Matrix (Fin a) (Fin M) k := fun r i ↦ (X r i).1
def V1 (X : Fin a → Fin M → k × k) : Matrix (Fin a) (Fin M) k := fun r i ↦ (X r i).2
end FiniteFieldSplitting
end PI.VolStabW


