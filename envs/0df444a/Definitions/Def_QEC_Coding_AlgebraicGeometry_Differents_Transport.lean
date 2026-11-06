-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Differents_Transport
-- name    : QEC_Coding_AlgebraicGeometry_Differents_Transport
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T14:14:39.232476+00:00
-- url     : https://prove2.me/theorems/1afe44f0-d16c-4168-a515-f577bd0a591c
-- title:
--   Transport
-- statement:
--   Definitions and structural lemmas for Transport, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differents/Transport.lean

import Mathlib.RingTheory.DedekindDomain.Different
set_option autoImplicit false
namespace QEC.Coding.AlgebraicGeometry
noncomputable section
attribute [local instance] FractionRing.liftAlgebra
noncomputable def fractionRingAlgEquivOfAlgEquiv
    (A B C : Type*) [CommRing A] [CommRing B] [CommRing C]
    [IsDomain A] [IsDomain B] [IsDomain C]
    [Algebra A B] [Algebra A C]
    [Module.IsTorsionFree A B] [Module.IsTorsionFree A C]
    (sigma : B ≃ₐ[A] C) :
    FractionRing B ≃ₐ[FractionRing A] FractionRing C :=
  IsFractionRing.fieldEquivOfAlgEquiv
    (FractionRing A) (FractionRing B) (FractionRing C) sigma
def idealMapRingEquiv
    (B C : Type*) [CommSemiring B] [CommSemiring C]
    (sigma : B ≃+* C) : Ideal B ≃+* Ideal C where
  toFun I := Ideal.map sigma I
  invFun I := Ideal.map sigma.symm I
  map_add' I J := (Ideal.mapHom sigma).map_add I J
  map_mul' I J := Ideal.map_mul sigma I J
  left_inv I := by
    calc
      Ideal.map sigma.symm (Ideal.map sigma I) =
          Ideal.map (sigma.symm.toRingHom.comp sigma.toRingHom) I :=
        I.map_map sigma.toRingHom sigma.symm.toRingHom
      _ = I := by
        rw [sigma.symm_toRingHom_comp_toRingHom, Ideal.map_id]
  right_inv I := by
    calc
      Ideal.map sigma (Ideal.map sigma.symm I) =
          Ideal.map (sigma.toRingHom.comp sigma.symm.toRingHom) I :=
        I.map_map sigma.symm.toRingHom sigma.toRingHom
      _ = I := by
        rw [sigma.toRingHom_comp_symm_toRingHom, Ideal.map_id]
end
end QEC.Coding.AlgebraicGeometry


