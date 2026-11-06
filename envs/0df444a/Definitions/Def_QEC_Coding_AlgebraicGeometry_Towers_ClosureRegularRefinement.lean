-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_ClosureRegularRefinement
-- name    : QEC_Coding_AlgebraicGeometry_Towers_ClosureRegularRefinement
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T20:43:38.330659+00:00
-- url     : https://prove2.me/theorems/c88b0d6c-cb5c-4c89-bda0-4911a37b7466
-- title:
--   Closure Regular Refinement
-- statement:
--   Definitions and structural lemmas for Closure Regular Refinement, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/ClosureRegularRefinement.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_RegularSourceRefinement
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_ClosureConjugateChains
set_option autoImplicit false
open IntermediateField
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
attribute [local instance 2500] Algebra.toSMul Algebra.toModule
attribute [local instance] sourceConstantBaseTower
end
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth


