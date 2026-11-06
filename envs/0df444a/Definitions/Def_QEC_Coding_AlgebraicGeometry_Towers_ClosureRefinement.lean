-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_ClosureRefinement
-- name    : QEC_Coding_AlgebraicGeometry_Towers_ClosureRefinement
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T20:43:33.151988+00:00
-- url     : https://prove2.me/theorems/98804578-3bb6-4d69-b937-65107dfd8370
-- title:
--   Closure Refinement
-- statement:
--   Definitions and structural lemmas for Closure Refinement, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/ClosureRefinement.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_ClosureConjugateChains
set_option autoImplicit false
open IntermediateField
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
attribute [local instance 2500] Algebra.toSMul Algebra.toModule
attribute [local instance] sourceConstantBaseTower
scoped instance sourceClosurePlace_finite_residue (m : ℕ)
    (Q : GlobalPlace F256 (SourceGaloisClosureField m)) : Finite Q.residueField := by
  letI : Algebra (Polynomial F256) (SourceGaloisClosureField m) :=
    ((algebraMap (RatFunc F256) (SourceGaloisClosureField m)).comp
      (algebraMap (Polynomial F256) (RatFunc F256))).toAlgebra
  letI : IsScalarTower (Polynomial F256) (RatFunc F256) (SourceGaloisClosureField m) :=
    IsScalarTower.of_algebraMap_eq' rfl
  exact GlobalPlace.finite_residueField Q
end
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth


