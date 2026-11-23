-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsIntegralIdempotentLiftNewton
-- name    : Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsIntegralIdempotentLiftNewton
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T21:31:42.706373+00:00
-- url     : https://prove2.me/theorems/2a4977a2-1f20-44fe-9873-69276e64b361
-- title:
--   Exists Integral Idempotent Lift Newton
-- statement:
--   Definitions and structural lemmas for Exists Integral Idempotent Lift Newton, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsIntegralIdempotentLiftNewton.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CommOfBezout
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitDiscAlg
namespace GlobalTheory.IdemLift
open Filter Topology
variable {E : Type} [NontriviallyNormedField E] [IsUltrametricDist E] {n : ℕ}
noncomputable def step (y : Matrix (Fin n) (Fin n) E) : Matrix (Fin n) (Fin n) E :=
  y * y + y * y + y * y - (y * y * y + y * y * y)
noncomputable def seq (x : Matrix (Fin n) (Fin n) E) : ℕ → Matrix (Fin n) (Fin n) E
  | 0 => x
  | k + 1 => step (seq x k)
end GlobalTheory.IdemLift


