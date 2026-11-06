-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Differents_PlaceLocalization
-- name    : QEC_Coding_AlgebraicGeometry_Differents_PlaceLocalization
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T14:14:49.410649+00:00
-- url     : https://prove2.me/theorems/9c5138b0-cdf4-43e2-a710-a70fbfdb6be0
-- title:
--   Place Localization
-- statement:
--   Definitions and structural lemmas for Place Localization, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differents/PlaceLocalization.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differents_LocalizedPrime
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_DifferentialLocal
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_HeightOneOrderTransport
set_option autoImplicit false
namespace QEC.Coding.AlgebraicGeometry
noncomputable section
def valuationSubringRingEquivOfEq
    {K : Type*} [_root_.Field K]
    (S T : ValuationSubring K) (h : S = T) : S ≃+* T where
  toFun x := ⟨x, by rw [← h]; exact x.property⟩
  invFun x := ⟨x, by rw [h]; exact x.property⟩
  left_inv x := Subtype.ext rfl
  right_inv x := Subtype.ext rfl
  map_mul' _ _ := Subtype.ext rfl
  map_add' _ _ := Subtype.ext rfl
@[reducible] noncomputable def transportedSubringAlgebra
    (B K : Type*) [CommRing B] [_root_.Field K]
    (S T : ValuationSubring K) [Algebra B S]
    (h : S = T) : Algebra B T :=
  (((valuationSubringRingEquivOfEq S T h).toRingHom).comp
    (algebraMap B S)).toAlgebra
end
end QEC.Coding.AlgebraicGeometry


