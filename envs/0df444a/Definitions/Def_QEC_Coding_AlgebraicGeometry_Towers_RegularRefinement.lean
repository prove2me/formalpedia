-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_RegularRefinement
-- name    : QEC_Coding_AlgebraicGeometry_Towers_RegularRefinement
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T19:10:46.015437+00:00
-- url     : https://prove2.me/theorems/37057cd5-b24a-4837-957c-9c396113ea9e
-- title:
--   Regular Refinement
-- statement:
--   Definitions and structural lemmas for Regular Refinement, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/RegularRefinement.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_TraceRefinement
set_option autoImplicit false
open IntermediateField
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
variable {F E : Type*} [_root_.Field F] [_root_.Field E] [Algebra F E]
  [Algebra F256 E] (Q : GlobalPlace F256 E)
def RegularQuadraticEdge (K L : IntermediateField F E) : Prop :=
  ∃ y : E, y ∈ Q.valuationRing ∧ y ^ 2 + y ∈ K ∧ L = K ⊔ F⟮y⟯
abbrev RegularRefinement (K L : IntermediateField F E) : Prop :=
  Relation.ReflTransGen (RegularQuadraticEdge Q) K L
section ChangeBase
variable {B : Type*} [_root_.Field B] [Algebra F B] [Algebra B E]
  [IsScalarTower F B E]
end ChangeBase
end
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth


