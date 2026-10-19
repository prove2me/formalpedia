-- Prove2me | Definitions.Def_MIPRE_Background_LIDT_Bridge_Field
-- name    : MIPRE_Background_LIDT_Bridge_Field
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-16T23:13:59.133523+00:00
-- url     : https://prove2.me/theorems/a86d9f52-db14-4d83-a2bd-1769a67caa31
-- title:
--   Definitions of Field: Bridge, part 1: parameters and the field coding The MIPStarRE development works with a coded field `Fq params := Fin…
-- statement:
--   The definitions of the module `MIPRE.Background.LIDT.Bridge.Field` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Bridge, part 1: parameters and the field coding. The MIPStarRE development works with a coded field `Fq params := Fin params.q` together with a `FieldModel params.q` instance carrying an actual field `K` and an equivalence `K ≃ Fin q`; all arithmetic is transported through the coding (`encodeScalar`, `decodeScalar`, `addCoord`, ...). This file instantiates that setup for our finite field `F`: the parameters `lidtParams F m d` (with `q = Fintype.card F`) and the field model with `K := F`, and it records how the coding interacts with points, lines and the arithmetic of `F`.
--
--   **Definitions** (8): `MIPRE.LIDT.Bridge.dec` (Decode a coded scalar into `F`.); `MIPRE.LIDT.Bridge.decP` (Decode a coded point.); `MIPRE.LIDT.Bridge.enc` (Encode a scalar of `F` into the coded field of the parameters.); `MIPRE.LIDT.Bridge.encP` (Encode a point of `F^m`.); `MIPRE.LIDT.Bridge.fieldModel` (The field model with carrier `F` itself, coded by an arbitrary enumeration.); `MIPRE.LIDT.Bridge.lidtParams` (The MIPStarRE parameters of the `(m, q, d)` test, `q = |F|`.); `MIPRE.LIDT.Bridge.pointEquiv` (The coding of points, as an equivalence.); `MIPRE.LIDT.Bridge.scalarEquiv` (The coding of scalars, as an equivalence.).
--
--   **Embedded lemmas** (15): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `decP_addPoint`, `decP_encP`, `decP_smulPoint`, `decP_zeroPoint`, `dec_addCoord`, `dec_enc`, `dec_mulCoord`, `dec_zeroCoord`, `decodePoint_eq`, `encP_decP`, ….
--
--   **Formalization Note** The bundle is the module `MIPRE.Background.LIDT.Bridge.Field` (`MIPRE/Background/LIDT/Bridge/Field.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 6 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/LIDT/Bridge/Field.lean

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/Bridge/Field.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Finsupp
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finite.Defs
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finsupp.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.FunLike.Basic
import Mathlib.Data.FunLike.Equiv
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.List.Nodup
import Mathlib.Data.Multiset.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Data.SetLike.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Logic.Basic
import Mathlib.Logic.Equiv.Defs
import Mathlib.Logic.Nonempty
import Mathlib.Order.Basic
import Mathlib.Order.Defs.PartialOrder
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic
import Mathlib.Tactic.DeriveFintype
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Background_LIDT_Game
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_ParametersBase
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_DiagonalLine

/-!
# Bridge, part 1: parameters and the field coding

The MIPStarRE development works with a coded field `Fq params := Fin params.q` together
with a `FieldModel params.q` instance carrying an actual field `K` and an equivalence
`K ≃ Fin q`; all arithmetic is transported through the coding (`encodeScalar`,
`decodeScalar`, `addCoord`, ...). This file instantiates that setup for our finite field
`F`: the parameters `lidtParams F m d` (with `q = Fintype.card F`) and the field model
with `K := F`, and it records how the coding interacts with points, lines and the
arithmetic of `F`.
-/

open MIPStarRE.LDT

noncomputable section

namespace MIPRE.LIDT.Bridge

variable (F : Type*) [Field F] [Fintype F] [DecidableEq F] (m d : ℕ) [NeZero m]

/-- The MIPStarRE parameters of the `(m, q, d)` test, `q = |F|`. -/
abbrev lidtParams : Parameters where
  m := m
  q := Fintype.card F
  d := d
  hm := NeZero.pos m
  hq := Fintype.card_pos
  hqPrimePower := by
    obtain ⟨p, _, n, hp, hcard⟩ := FiniteField.card' (K := F)
    exact ⟨p, n, hp, n.pos, hcard⟩

/-- The field model with carrier `F` itself, coded by an arbitrary enumeration. -/
instance fieldModel : FieldModel (Fintype.card F) where
  K := F
  instField := inferInstance
  instFintype := inferInstance
  instDecidableEq := inferInstance
  equiv := Fintype.equivFin F

variable {F m d}

/-! ## Coding of scalars and points -/

/-- Encode a scalar of `F` into the coded field of the parameters. -/
abbrev enc (x : F) : Fq (lidtParams F m d) := encodeScalar (params := lidtParams F m d) x

/-- Decode a coded scalar into `F`. -/
abbrev dec (x : Fq (lidtParams F m d)) : F := decodeScalar (params := lidtParams F m d) x

/-- Encode a point of `F^m`. -/
abbrev encP (u : Point F m) : MIPStarRE.LDT.Point (lidtParams F m d) := fun i => enc (u i)

/-- Decode a coded point. -/
abbrev decP (u : MIPStarRE.LDT.Point (lidtParams F m d)) : Point F m := fun i => dec (u i)

@[simp] theorem dec_enc (x : F) : dec (enc (m := m) (d := d) x) = x :=
  decode_encodeScalar (params := lidtParams F m d) x

@[simp] theorem enc_dec (x : Fq (lidtParams F m d)) : enc (dec x) = x :=
  encode_decodeScalar (params := lidtParams F m d) x

@[simp] theorem decP_encP (u : Point F m) : decP (encP (d := d) u) = u := by
  funext i; simp

@[simp] theorem encP_decP (u : MIPStarRE.LDT.Point (lidtParams F m d)) : encP (decP u) = u := by
  funext i; simp

/-- The coding of points, as an equivalence. -/
def pointEquiv : Point F m ≃ MIPStarRE.LDT.Point (lidtParams F m d) where
  toFun := encP
  invFun := decP
  left_inv := decP_encP
  right_inv := encP_decP

@[simp] theorem pointEquiv_apply (u : Point F m) : pointEquiv (d := d) u = encP u := rfl
@[simp] theorem pointEquiv_symm_apply (u : MIPStarRE.LDT.Point (lidtParams F m d)) :
    (pointEquiv (F := F) (m := m) (d := d)).symm u = decP u := rfl

/-- The coding of scalars, as an equivalence. -/
def scalarEquiv : F ≃ Fq (lidtParams F m d) where
  toFun := enc
  invFun := dec
  left_inv := dec_enc
  right_inv := enc_dec

@[simp] theorem scalarEquiv_apply (x : F) : scalarEquiv (m := m) (d := d) x = enc x := rfl
@[simp] theorem scalarEquiv_symm_apply (x : Fq (lidtParams F m d)) :
    (scalarEquiv (F := F) (m := m) (d := d)).symm x = dec x := rfl

@[simp] theorem decodePoint_eq (u : MIPStarRE.LDT.Point (lidtParams F m d)) :
    decodePoint (params := lidtParams F m d) u = decP u := rfl

/-! ## Arithmetic through the coding -/

@[simp] theorem dec_zeroCoord : dec (zeroCoord (params := lidtParams F m d)) = (0 : F) := by
  simp [zeroCoord]

@[simp] theorem dec_addCoord (x y : Fq (lidtParams F m d)) :
    dec (addCoord x y) = dec x + dec y := by
  simp [addCoord]

@[simp] theorem dec_mulCoord (x y : Fq (lidtParams F m d)) :
    dec (mulCoord x y) = dec x * dec y := by
  simp [mulCoord]

@[simp] theorem decP_addPoint (u v : MIPStarRE.LDT.Point (lidtParams F m d)) :
    decP (addPoint u v) = decP u + decP v := by
  funext i
  show dec (addCoord (u i) (v i)) = dec (u i) + dec (v i)
  exact dec_addCoord _ _

@[simp] theorem decP_smulPoint (t : Fq (lidtParams F m d))
    (u : MIPStarRE.LDT.Point (lidtParams F m d)) :
    decP (smulPoint t u) = dec t • decP u := by
  funext i
  show dec (mulCoord t (u i)) = dec t * dec (u i)
  exact dec_mulCoord _ _

@[simp] theorem decP_zeroPoint : decP (zeroPoint (params := lidtParams F m d)) = (0 : Point F m) := by
  funext i
  show dec zeroCoord = 0
  exact dec_zeroCoord

end MIPRE.LIDT.Bridge

end


