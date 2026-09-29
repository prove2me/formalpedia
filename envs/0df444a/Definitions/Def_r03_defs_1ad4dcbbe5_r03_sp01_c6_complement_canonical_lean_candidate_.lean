-- Prove2me | Definitions.Def_r03_defs_1ad4dcbbe5_r03_sp01_c6_complement_canonical_lean_candidate_
-- name    : r03_defs_1ad4dcbbe5_r03_sp01_c6_complement_canonical_lean_candidate_
-- status  : Definition
-- author  : @hao jia
-- created : 2026-09-17T09:53:09.068727+00:00
-- url     : https://prove2.me/theorems/164623c6-6abe-41cd-a17f-abbf91bd49ac
-- title:
--   R03 candidate definition: r03 defs 1ad4dcbbe5 r03 sp01 c6 complement canonical lean candidate
-- statement:
--   This is a source-faithful definition module supporting a conditional formalization of the cubic P3-partition problem. It contains data structures and predicates used by separately published theorem candidates; it does not assert that the open root problem is solved.
-- source:
--   VibeMathing candidate definition artifact: Definitions/Def_r03_defs_1ad4dcbbe5_r03_sp01_c6_complement_canonical_lean_candidate_.lean; candidate-only formalization for ProblemContract problem:opg-46613-p3-partition.

import Definitions.Def_cubic_p3_partition_models

/-!
Candidate-only canonical-interface C6 branch for SP01.

Unlike the local branch file, this declaration uses the project's imported
`CubicP3Partition.P3Factor` structure.  The complement classification is still
an explicit hypothesis, so this is not a root theorem.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

namespace CubicP3Partition

abbrev SP01V := Fin 6

def sp01Next6 (i : Fin 6) : Fin 6 :=
  if h : i.val = 5 then 0 else ⟨i.val + 1, by omega⟩

def sp01AltTo : Fin 6 → Fin 6 := ![0, 2, 4, 1, 3, 5]
def sp01AltInv : Fin 6 → Fin 6 := ![0, 3, 1, 4, 2, 5]

def sp01AltEquiv : Fin 6 ≃ Fin 6 where
  toFun := sp01AltTo
  invFun := sp01AltInv
  left_inv := by decide
  right_inv := by decide

def SP01ComplementIsC6 (G : SimpleGraph SP01V)
    (order : Fin 6 ≃ SP01V) : Prop :=
  ∀ i j, (Gᶜ).Adj (order i) (order j) ↔
    (j = sp01Next6 i ∨ i = sp01Next6 j)

def sp01C6Place (order : Fin 6 ≃ SP01V) :
    (Fin 2 × Fin 3) ≃ SP01V :=
  finProdFinEquiv.trans (sp01AltEquiv.trans order)

end CubicP3Partition


