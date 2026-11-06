-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_GaloisBase
-- name    : QEC_Coding_AlgebraicGeometry_Towers_GaloisBase
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T18:53:45.274421+00:00
-- url     : https://prove2.me/theorems/6faa4e87-33b0-4753-b88b-9173c85ec923
-- title:
--   Galois Base
-- statement:
--   Definitions and structural lemmas for Galois Base, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/GaloisBase.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_BasePlaces
import Mathlib.Data.Fintype.EquivFin
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_f256ArtinSchreier_ker_card
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_rationalAdicPolynomialToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalAdicResidueEquiv_mk
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalPlaceEquiv_apply_none
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalPlaceEquiv_apply_some
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_order
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackage_valuation
import Theorems.Thm_QEC_Coding_f256_card
attribute [local simp] QEC.Coding.AlgebraicGeometry.Divisor.degree_zero
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_constantsToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_rationalAdicPolynomialToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalAdicResidueEquiv_mk
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalPlaceEquiv_apply_none
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalPlaceEquiv_apply_some
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_order
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_valuation
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackage_valuation


set_option autoImplicit false
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
noncomputable def galoisBaseW : RatFunc F256 :=
  RatFunc.X ^ 16 + RatFunc.X
noncomputable def galoisBaseZ : RatFunc F256 :=
  galoisBaseW ^ 15
noncomputable def galoisBaseWValue (a : F256) : F256 :=
  f256ArtinSchreier a
theorem galoisBaseWValue_eq (a : F256) :
    galoisBaseWValue a = a ^ 16 + a := by
  exact f256ArtinSchreier_apply a
noncomputable def galoisBaseZValue (a : F256) : F256 :=
  galoisBaseWValue a ^ 15
abbrev GaloisBaseSplitPoint : Type :=
  {a : F256 // galoisBaseWValue a ≠ 0}
noncomputable def galoisBaseWZeroEquivKernel :
    {a : F256 // galoisBaseWValue a = 0} ≃
      LinearMap.ker f256ArtinSchreier where
  toFun a := ⟨a, a.property⟩
  invFun a := ⟨a, a.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
theorem galoisBaseSplitPoint_card :
    Fintype.card GaloisBaseSplitPoint = 240 := by
  calc
    Fintype.card GaloisBaseSplitPoint =
        Fintype.card F256 -
          Fintype.card {a : F256 // galoisBaseWValue a = 0} :=
      Fintype.card_subtype_compl
        (fun a : F256 => galoisBaseWValue a = 0)
    _ = 256 - 16 := by
      rw [f256_card,
        Fintype.card_congr galoisBaseWZeroEquivKernel,
        f256ArtinSchreier_ker_card]
    _ = 240 := by norm_num
noncomputable def galoisBaseSplitPointEquiv :
    Fin 240 ≃ GaloisBaseSplitPoint :=
  Fintype.equivOfCardEq (by
    simpa only [Fintype.card_fin] using galoisBaseSplitPoint_card.symm)
noncomputable def galoisBaseSplitPointUnit
    (a : GaloisBaseSplitPoint) : F256ˣ :=
  Units.mk0 a (by
    intro ha
    apply a.property
    simp [galoisBaseWValue_eq, ha])
noncomputable def galoisBaseSplitRationalPlace
    (a : GaloisBaseSplitPoint) : RationalPlace F256 (RatFunc F256) :=
  baseRationalPlace (galoisBaseSplitPointUnit a)
end
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth


