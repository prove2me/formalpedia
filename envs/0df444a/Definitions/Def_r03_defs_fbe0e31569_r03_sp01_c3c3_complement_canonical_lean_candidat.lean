-- Prove2me | Definitions.Def_r03_defs_fbe0e31569_r03_sp01_c3c3_complement_canonical_lean_candidat
-- name    : r03_defs_fbe0e31569_r03_sp01_c3c3_complement_canonical_lean_candidat
-- status  : Definition
-- author  : @hao jia
-- created : 2026-09-17T09:54:07.386065+00:00
-- url     : https://prove2.me/theorems/c094fe26-afdb-4fd5-bc59-438169d07153
-- title:
--   R03 candidate definition: r03 defs fbe0e31569 r03 sp01 c3c3 complement canonical lean candidat
-- statement:
--   This is a source-faithful definition module supporting a conditional formalization of the cubic P3-partition problem. It contains data structures and predicates used by separately published theorem candidates; it does not assert that the open root problem is solved.
-- source:
--   VibeMathing candidate definition artifact: Definitions/Def_r03_defs_fbe0e31569_r03_sp01_c3c3_complement_canonical_lean_candidat.lean; candidate-only formalization for ProblemContract problem:opg-46613-p3-partition.

import Definitions.Def_cubic_p3_partition_models

/-!
Candidate-only canonical-interface C3 disjoint union C3 branch for SP01.

The declaration uses the project's imported `CubicP3Partition.P3Factor`.
The two-part complement condition is supplied explicitly; the cubic-to-
complement classification is not claimed here.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

namespace CubicP3Partition

abbrev SP01C3V := Fin 6

def sp01TriTo : Fin 6 → Fin 6 := ![0, 3, 1, 4, 2, 5]
def sp01TriInv : Fin 6 → Fin 6 := ![0, 2, 4, 1, 3, 5]

def sp01TriEquiv : Fin 6 ≃ Fin 6 where
  toFun := sp01TriTo
  invFun := sp01TriInv
  left_inv := by decide
  right_inv := by decide

/-- The two complement triangles have no complement edge between them. -/
def SP01ComplementHasTwoParts (G : SimpleGraph SP01C3V)
    (parts : Fin 6 ≃ SP01C3V) : Prop :=
  ∀ u v, u.val / 3 ≠ v.val / 3 → ¬ Gᶜ.Adj (parts u) (parts v)

def sp01C3C3Place (parts : Fin 6 ≃ SP01C3V) :
    (Fin 2 × Fin 3) ≃ SP01C3V :=
  finProdFinEquiv.trans (sp01TriEquiv.trans parts)

end CubicP3Partition


