-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_ClosureConjugateChains
-- name    : QEC_Coding_AlgebraicGeometry_Towers_ClosureConjugateChains
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T20:41:50.161426+00:00
-- url     : https://prove2.me/theorems/cf07589e-d7a3-48f5-9b87-8f23951177b9
-- title:
--   Closure Conjugate Chains
-- statement:
--   Definitions and structural lemmas for Closure Conjugate Chains, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/ClosureConjugateChains.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_EmbeddedWSeed
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisWNormal
set_option autoImplicit false
open IntermediateField
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
attribute [local instance 2500] Algebra.toSMul Algebra.toModule
local instance sourceConstantBaseTower (m : ℕ) :
    IsScalarTower F256 GaloisBaseField (SourceField m) := IsScalarTower.of_algebraMap_eq' (by
  apply RingHom.ext
  intro c
  change algebraMap F256 (SourceField m) c =
    algebraMap (RatFunc F256) (SourceField m) (algebraMap F256 (RatFunc F256) c)
  exact IsScalarTower.algebraMap_apply F256 (RatFunc F256) (SourceField m) c)
local instance wConstantBaseTower :
    IsScalarTower F256 GaloisBaseField SourceGaloisWField := IsScalarTower.of_algebraMap_eq' rfl
abbrev sourceClosureWBase (m : ℕ) : IntermediateField F256 (SourceGaloisClosureField m) :=
  (SourceGaloisWClosureField m).restrictScalars F256
scoped instance sourceClosureWBase_finite (m : ℕ) :
    FiniteDimensional (sourceClosureWBase m) (SourceGaloisClosureField m) :=
  inferInstanceAs (FiniteDimensional (SourceGaloisWClosureField m) (SourceGaloisClosureField m))
scoped instance sourceClosureWBase_separable (m : ℕ) :
    Algebra.IsSeparable (sourceClosureWBase m) (SourceGaloisClosureField m) :=
  inferInstanceAs (Algebra.IsSeparable (SourceGaloisWClosureField m) (SourceGaloisClosureField m))
end
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth


