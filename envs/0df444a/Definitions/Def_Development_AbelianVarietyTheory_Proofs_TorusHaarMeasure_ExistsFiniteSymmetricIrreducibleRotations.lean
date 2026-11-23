-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsFiniteSymmetricIrreducibleRotations
-- name    : Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsFiniteSymmetricIrreducibleRotations
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:27:11.297824+00:00
-- url     : https://prove2.me/theorems/1c3dd506-2c84-4188-8519-19b1bd94ea81
-- title:
--   Exists Finite Symmetric Irreducible Rotations
-- statement:
--   Definitions and structural lemmas for Exists Finite Symmetric Irreducible Rotations, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/ExistsFiniteSymmetricIrreducibleRotations.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology Matrix
open scoped ComplexOrder ENNReal Pointwise
namespace GlobalTheory
namespace HypRot
variable {r : ℕ}
noncomputable def offN (j k : Fin r) (u : ℂ) : Matrix (Fin r) (Fin r) ℂ :=
  Matrix.single j k u + Matrix.single k j (star u)
noncomputable def projP (j k : Fin r) : Matrix (Fin r) (Fin r) ℂ :=
  Matrix.single j j 1 + Matrix.single k k 1
noncomputable def rot (j k : Fin r) (u : ℂ) : Matrix (Fin r) (Fin r) ℂ :=
  1 + (1 / 4 : ℂ) • projP j k + (3 / 4 : ℂ) • offN j k u
end HypRot
end GlobalTheory


