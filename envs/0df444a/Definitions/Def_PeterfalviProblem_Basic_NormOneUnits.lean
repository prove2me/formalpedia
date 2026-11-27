-- Prove2me | Definitions.Def_PeterfalviProblem_Basic_NormOneUnits
-- name    : PeterfalviProblem_Basic_NormOneUnits
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-27T04:58:43.972372+00:00
-- url     : https://prove2.me/theorems/2f459812-30ad-4a98-8313-1b6e0a2eadd3
-- title:
--   Norm One Units
-- statement:
--   Definitions and structural lemmas for Norm One Units, from Yawara Ishida (yawara/peterfalvi-problem; see pinned Apache-2.0 LICENSE and source headers)'s pinned Resolution of Péterfalvi problem for p = 3 and SL(2, 2^q) witness for p = 2 development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/yawara/peterfalvi-problem/blob/698b7ae0af649f7fad48c482aa8ff0d2d14336bb/PeterfalviProblem/Basic/NormOneUnits.lean

import Mathlib.Algebra.Ring.GeomSum
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.Finite.Trace
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Definitions.Def_PeterfalviProblem_Algebra_PaleySet
import Definitions.Def_PeterfalviProblem_Statement
set_option autoImplicit false
namespace PeterfalviProblem
variable (p q : ℕ)
noncomputable def normN [Fact p.Prime] (x : GaloisField p q) : GaloisField p q :=
  ∏ i ∈ Finset.range q, x ^ (p ^ i)
variable {p q}
end PeterfalviProblem


