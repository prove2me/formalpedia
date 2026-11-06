-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_ClosureGenus
-- name    : QEC_Coding_AlgebraicGeometry_Towers_ClosureGenus
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T05:32:24.652184+00:00
-- url     : https://prove2.me/theorems/db8dd879-ba41-40e6-a013-abf587aa0d22
-- title:
--   Closure Genus
-- statement:
--   Definitions and structural lemmas for Closure Genus, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/ClosureGenus.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_ClosureCanonicalDifferential
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_ClosureFullConstants
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_Theorem
set_option autoImplicit false
namespace QEC.Coding.AlgebraicGeometry
namespace F256GarciaStichtenoth
noncomputable section
attribute [local instance 2500] Algebra.toSMul Algebra.toModule
def sourceClosureGenus (m : ℕ) : ℕ :=
  GlobalPlace.functionFieldGenus F256 (SourceGaloisClosureField m)
end
end F256GarciaStichtenoth
end QEC.Coding.AlgebraicGeometry


