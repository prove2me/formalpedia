-- Prove2me | Definitions.Def_MazurCampaign_group_constraints
-- name    : MazurCampaign_group_constraints
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-06T07:00:08.363096+00:00
-- url     : https://prove2.me/theorems/dee74227-ec98-4286-9de2-ef9300faf834
-- title:
--   Forbidden subgroup interfaces for Mazur classification
-- statement:
--   For additive abelian groups A and G, ForbidsEmbedding(A,G) asserts that no injective additive homomorphism A → G exists. AvoidsMazurForbiddenSubgroups(G) collects the seven exclusions: (Z/2Z)^3; (Z/3Z)^2; (Z/4Z)^2; (Z/5Z)^2; (Z/7Z)^2; Z/2Z × Z/10Z; and Z/2Z × Z/12Z. This definition supplies hypotheses, and does not assert that any elliptic-curve group satisfies them. Its named downstream consumer is MazurCampaign.finite_group_classification, the checked finite-abelian step connecting point-order and subgroup obstructions to the full fifteen-group classification.
-- source:
--   https://github.com/vilin97/MazurTheorem/blob/54d43d8dda8a6fcf069cc02a815f850d762c5c0c/MazurTorsion/GroupTheory/ForbiddenEmbeddings.lean#L25 ; https://github.com/vilin97/MazurTheorem/blob/54d43d8dda8a6fcf069cc02a815f850d762c5c0c/MazurTorsion/GroupTheory/FiniteClassification.lean#L35

/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin

Adapted from MazurTorsion/GroupTheory/FiniteClassification.lean and
MazurTorsion/GroupTheory/ForbiddenEmbeddings.lean in vilin97/MazurTheorem.
-/
import Definitions.Def_MazurCampaign_target_objects

namespace MazurTorsion

/-- No injective additive homomorphism exists from A to G. -/
def ForbidsEmbedding (A G : Type*) [AddCommGroup A] [AddCommGroup G] : Prop :=
  ∀ f : A →+ G, ¬ Function.Injective f

/-- The seven subgroup exclusions needed by the finite-abelian classification. -/
structure AvoidsMazurForbiddenSubgroups (G : Type*) [AddCommGroup G] : Prop where
  c2Cube : ForbidsEmbedding (ZMod 2 × ZMod 2 × ZMod 2) G
  c3Square : ForbidsEmbedding (ZMod 3 × ZMod 3) G
  c4Square : ForbidsEmbedding (ZMod 4 × ZMod 4) G
  c5Square : ForbidsEmbedding (ZMod 5 × ZMod 5) G
  c7Square : ForbidsEmbedding (ZMod 7 × ZMod 7) G
  c2c10 : ForbidsEmbedding (ZMod 2 × ZMod 10) G
  c2c12 : ForbidsEmbedding (ZMod 2 × ZMod 12) G

end MazurTorsion


