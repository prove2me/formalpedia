-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_WBaseDifferentialOrder
-- name    : QEC_Coding_AlgebraicGeometry_Towers_WBaseDifferentialOrder
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T20:49:40.122607+00:00
-- url     : https://prove2.me/theorems/9e8860b5-3cf5-4946-add0-dbbb7c3b0c76
-- title:
--   WBase Differential Order
-- statement:
--   Definitions and structural lemmas for WBase Differential Order, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/WBaseDifferentialOrder.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_ClosureDifferentialOrder
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_RationalDifferentialTransport
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisWClosurePlaces
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_PlaceNormalizedExtension_trans

set_option autoImplicit false
open IntermediateField QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
attribute [local instance 5000] Algebra.toSMul Algebra.toModule
attribute [local instance] wConstantBaseTower
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000
local instance wBaseField (m : ℕ) : _root_.Field (sourceClosureWBase m) :=
  (sourceClosureWBase m).toField
local instance wBaseOriginalBaseAlgebra (m : ℕ) :
    Algebra GaloisBaseField (sourceClosureWBase m) := sourceGaloisWClosureFieldAlgebra m
local instance wBaseOriginalRationalAlgebra (m : ℕ) :
    Algebra (RatFunc F256) (sourceClosureWBase m) := sourceClosureWBase_zAlgebra m
local instance wBaseOriginalConstantAlgebra (m : ℕ) :
    Algebra F256 (sourceClosureWBase m) := (sourceClosureWBase m).algebra'
local instance wBaseCharacteristic (m : ℕ) : CharP (sourceClosureWBase m) 2 := by
  letI : CharP F256 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) F256).injective 2
  exact charP_of_injective_algebraMap (algebraMap F256 (sourceClosureWBase m)).injective 2
local instance wBaseConstantTower (m : ℕ) :
    IsScalarTower F256 GaloisBaseField (sourceClosureWBase m) :=
  @IsScalarTower.of_algebraMap_eq' F256 GaloisBaseField (sourceClosureWBase m)
    _ _ _ _ (sourceGaloisWClosureFieldAlgebra m) (sourceClosureWBase m).algebra' (by
      apply RingHom.ext
      intro c
      apply Subtype.ext
      exact IsScalarTower.algebraMap_apply F256 GaloisBaseField (SourceGaloisClosureField m) c)
def sourceClosureWBase_wEquiv (m : ℕ) : RatFunc F256 ≃ₐ[F256] sourceClosureWBase m :=
  sourceGaloisWFieldEquivRatFunc.trans
    ((sourceGaloisWFieldEquivClosureField m).restrictScalars F256)
end
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth


