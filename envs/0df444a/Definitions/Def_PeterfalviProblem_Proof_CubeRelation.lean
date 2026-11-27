-- Prove2me | Definitions.Def_PeterfalviProblem_Proof_CubeRelation
-- name    : PeterfalviProblem_Proof_CubeRelation
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-27T05:10:21.143794+00:00
-- url     : https://prove2.me/theorems/8c97015e-f917-43b7-b2fa-3638c5748f0a
-- title:
--   Cube Relation
-- statement:
--   Definitions and structural lemmas for Cube Relation, from Yawara Ishida (yawara/peterfalvi-problem; see pinned Apache-2.0 LICENSE and source headers)'s pinned Resolution of Péterfalvi problem for p = 3 and SL(2, 2^q) witness for p = 2 development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/yawara/peterfalvi-problem/blob/698b7ae0af649f7fad48c482aa8ff0d2d14336bb/PeterfalviProblem/Proof/CubeRelation.lean

import Definitions.Def_PeterfalviProblem_Basic_Witness
import Definitions.Def_PeterfalviProblem_Proof_GroupIdentities
set_option autoImplicit false
namespace PeterfalviProblem
variable {p q : ℕ} [Fact p.Prime] {G : Type*} [Group G]
noncomputable def conjGen (data : Witness p q G) : G := MulAut.conj data.y data.s
noncomputable def fieldHom (data : Witness p q G) :
    Multiplicative (GaloisField p q) →* G :=
  data.sigma.comp SemidirectProduct.inl
end PeterfalviProblem


