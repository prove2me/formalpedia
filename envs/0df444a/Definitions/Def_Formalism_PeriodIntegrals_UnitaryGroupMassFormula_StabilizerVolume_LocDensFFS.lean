-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerVolume_LocDensFFS
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerVolume_LocDensFFS
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:05:26.009832+00:00
-- url     : https://prove2.me/theorems/08b69da4-fbb8-4343-a659-ff360c78d26d
-- title:
--   Loc Dens FFS
-- statement:
--   Definitions and structural lemmas for Loc Dens FFS, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerVolume/LocDensFFS.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerVolume_LocDensFF
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.VolStabS
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
end PI.VolStabS


