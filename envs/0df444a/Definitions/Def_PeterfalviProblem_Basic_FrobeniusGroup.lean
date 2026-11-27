-- Prove2me | Definitions.Def_PeterfalviProblem_Basic_FrobeniusGroup
-- name    : PeterfalviProblem_Basic_FrobeniusGroup
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-27T05:02:16.402088+00:00
-- url     : https://prove2.me/theorems/0ae9a4df-769f-491e-985e-bdd3f0714427
-- title:
--   Frobenius Group
-- statement:
--   Definitions and structural lemmas for Frobenius Group, from Yawara Ishida (yawara/peterfalvi-problem; see pinned Apache-2.0 LICENSE and source headers)'s pinned Resolution of Péterfalvi problem for p = 3 and SL(2, 2^q) witness for p = 2 development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/yawara/peterfalvi-problem/blob/698b7ae0af649f7fad48c482aa8ff0d2d14336bb/PeterfalviProblem/Basic/FrobeniusGroup.lean

import Definitions.Def_PeterfalviProblem_Basic_NormOneUnits
set_option autoImplicit false
namespace PeterfalviProblem
variable (p q : ℕ) [Fact p.Prime]
noncomputable def normOneFrobeniusKernel : Subgroup (normOneFrobeniusGroup p q) :=
  (SemidirectProduct.inl : additiveFieldGroup p q →* normOneFrobeniusGroup p q).range
noncomputable def primeLineGenerator : normOneFrobeniusGroup p q :=
  SemidirectProduct.inl (Multiplicative.ofAdd (1 : GaloisField p q))
end PeterfalviProblem


