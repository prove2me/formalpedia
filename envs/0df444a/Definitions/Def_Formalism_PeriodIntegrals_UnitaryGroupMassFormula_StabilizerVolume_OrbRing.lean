-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerVolume_OrbRing
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerVolume_OrbRing
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:03:32.984804+00:00
-- url     : https://prove2.me/theorems/599557f0-d403-46a7-8842-5c8c772a6da8
-- title:
--   Orb Ring
-- statement:
--   Definitions and structural lemmas for Orb Ring, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerVolume/OrbRing.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnitaryOrbits_HformEntry
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.VolStabS.OrbR
open Matrix Formalism.UG PIW.AdelicOrbitU
variable {S : Type} [CommRing S] (s : S →+* S) {n : ℕ} (J : Matrix (Fin n) (Fin n) S)
def r1 (c : S) (u v : Fin n → S) : Matrix (Fin n) (Fin n) S :=
  1 - c • vecMulVec v (vecMul (fun i => s (u i)) J)
def tM {m : ℕ} (X : Fin m → Fin n → S) : Matrix (Fin n) (Fin m) S := Matrix.of fun r i => X i r
end PI.VolStabS.OrbR


