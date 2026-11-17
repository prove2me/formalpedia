-- Prove2me | Definitions.Def_NondetConn_Supplement_isDeterministic
-- name    : NondetConn_Supplement_isDeterministic
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T04:06:08.703039+00:00
-- url     : https://prove2.me/theorems/9decf834-fbe2-4864-a0d9-60e7f798948d
-- title:
--   Deterministic protocols inside the randomized tree model
-- statement:
--   A protocol is **deterministic** when its public coin is a point mass and every local message and output kernel is also a point mass.
--
--   This identifies ordinary deterministic interactive protocols inside the shared randomized communication-tree representation used by the supplement.
-- source:
--   Zhang, Settling Nondeterministic Communication Complexity of Graph Connectivity, arXiv:2610.32346 (held version, sha256 1d4f00d1…4e7ac), Theorem B.1, p.45 (PDF p.47)

import Definitions.Def_CommThresholdPR_StrongConverse_Protocols

set_option autoImplicit false

namespace NondetConn.Supplement

open CommThresholdPR.StrongConverse

/-- A protocol has one fixed public coin and every local message/output kernel is a point
mass. This identifies the deterministic protocols inside the general randomized tree model. -/
def isDeterministic {X Y A B : Type} (P : Protocol X Y A B) : Prop :=
  ∃ ω, P.publicLaw = PMF.pure ω ∧
    let rec deterministicTree : BinaryTree X Y A B → Prop
      | .leaf outA outB =>
          (∀ x, ∃ a, outA x = PMF.pure a) ∧ (∀ y, ∃ b, outB y = PMF.pure b)
      | .alice bit zero one =>
          (∀ x, ∃ b, bit x = PMF.pure b) ∧ deterministicTree zero ∧ deterministicTree one
      | .bob bit zero one =>
          (∀ y, ∃ b, bit y = PMF.pure b) ∧ deterministicTree zero ∧ deterministicTree one
    deterministicTree (P.tree ω)

end NondetConn.Supplement


