-- Prove2me | Definitions.Def_MIPRE_Background_LIDT_Bridge_Polynomial
-- name    : MIPRE_Background_LIDT_Bridge_Polynomial
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T00:57:18.242877+00:00
-- url     : https://prove2.me/theorems/84df6cd1-c452-47ba-9d01-fbf77c0cb039
-- title:
--   Definitions of Polynomial: Bridge, part 2: polynomial answer alphabets Our answer alphabets are coefficient vectors (`LinePoly F n := Fin (n+1) →…
-- statement:
--   The definitions of the module `MIPRE.Background.LIDT.Bridge.Polynomial` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Bridge, part 2: polynomial answer alphabets. Our answer alphabets are coefficient vectors (`LinePoly F n := Fin (n+1) → F`) and coefficient tables (`LowIndDegPoly := (Fin m → Fin (d+1)) → F`); the MIPStarRE development uses subtypes of Mathlib's `Polynomial` and `MvPolynomial` with degree bounds (`AxisLinePolynomial`, `DiagonalLinePolynomial`, `MIPStarRE.LDT.Polynomial`). This file provides the equivalences between the two, and shows that evaluation is compatible with them through the field coding.
--
--   **Definitions** (6): `MIPRE.LIDT.Bridge.axisEquiv` (Axis-line answers: coefficient vectors of length `d + 1` versus polynomials of degree at most `d`.); `MIPRE.LIDT.Bridge.diagEquiv` (Diagonal-line answers: coefficient vectors of length `m·d + 1` versus polynomials of degree at most `m·d`.); `MIPRE.LIDT.Bridge.expo` (The exponent vector of a monomial index.); `MIPRE.LIDT.Bridge.lowIndDegEquiv` (Global answers: coefficient tables versus polynomials of individual degree at most `d`.); `MIPRE.LIDT.Bridge.ofCoeffs` (The univariate polynomial with the given coefficients.); `MIPRE.LIDT.Bridge.toMv` (The multivariate polynomial with the given coefficient table.).
--
--   **Embedded lemmas** (13): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `axisEquiv_poly`, `coeff_ofCoeffs`, `coeff_toMv`, `coeff_toMv_of_not_le`, `degreeOf_toMv_le`, `diagEquiv_poly`, `expo_apply`, `expo_injective`, `lowIndDegEquiv_poly`, `natDegree_ofCoeffs_le`, ….
--
--   **Formalization Note** The bundle is the module `MIPRE.Background.LIDT.Bridge.Polynomial` (`MIPRE/Background/LIDT/Bridge/Polynomial.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 9 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/LIDT/Bridge/Polynomial.lean

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/Bridge/Polynomial.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.Algebra.Hom
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Finsupp
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.Algebra.MonoidAlgebra.Module
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.Polynomial
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.GroupWithZero.Canonical
import Mathlib.Algebra.Order.IsBotOne
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.Order.SuccPred
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finite.Defs
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finsupp.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.FunLike.Basic
import Mathlib.Data.FunLike.Equiv
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.List.Nodup
import Mathlib.Data.Multiset.Count
import Mathlib.Data.Multiset.Defs
import Mathlib.Data.Multiset.MapFold
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Nat.SuccPred
import Mathlib.Data.Real.Basic
import Mathlib.Data.SetLike.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Logic.Basic
import Mathlib.Logic.Equiv.Defs
import Mathlib.Logic.Nonempty
import Mathlib.Logic.Nontrivial.Defs
import Mathlib.Logic.Unique
import Mathlib.Order.Basic
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Lattice
import Mathlib.Order.Lattice.Nat
import Mathlib.Order.Nat
import Mathlib.Order.RelClasses
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic
import Mathlib.Tactic.DeriveFintype
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Background_LIDT_Game
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_ParametersBase
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
import Definitions.Def_MIPRE_Background_LIDT_Bridge_Field
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_LinePolynomials
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_LowDegreePolynomial

/-!
# Bridge, part 2: polynomial answer alphabets

Our answer alphabets are coefficient vectors (`LinePoly F n := Fin (n+1) → F`) and
coefficient tables (`LowIndDegPoly := (Fin m → Fin (d+1)) → F`); the MIPStarRE
development uses subtypes of Mathlib's `Polynomial` and `MvPolynomial` with degree
bounds (`AxisLinePolynomial`, `DiagonalLinePolynomial`, `MIPStarRE.LDT.Polynomial`).
This file provides the equivalences between the two, and shows that evaluation is
compatible with them through the field coding.
-/

open MIPStarRE.LDT (encodeScalar decodeScalar evalLinePolynomialModel evalPolynomialModel)

noncomputable section

namespace MIPRE.LIDT.Bridge

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m d : ℕ} [NeZero m]

/-! ## Univariate polynomials from coefficient vectors -/

/-- The univariate polynomial with the given coefficients. -/
def ofCoeffs {n : ℕ} (c : LinePoly F n) : _root_.Polynomial F :=
  ∑ i, _root_.Polynomial.C (c i) * _root_.Polynomial.X ^ (i : ℕ)

omit [Fintype F] [DecidableEq F] in
theorem natDegree_ofCoeffs_le {n : ℕ} (c : LinePoly F n) : (ofCoeffs c).natDegree ≤ n :=
  _root_.Polynomial.natDegree_sum_le_of_forall_le _ _ fun i _ =>
    (_root_.Polynomial.natDegree_C_mul_X_pow_le _ _).trans (Nat.lt_succ_iff.mp i.isLt)

omit [Fintype F] [DecidableEq F] in
theorem coeff_ofCoeffs {n : ℕ} (c : LinePoly F n) (i : Fin (n + 1)) :
    (ofCoeffs c).coeff i = c i := by
  simp [ofCoeffs, _root_.Polynomial.finsetSum_coeff, Fin.val_inj]

omit [Fintype F] [DecidableEq F] in
theorem ofCoeffs_coeff {n : ℕ} (p : _root_.Polynomial F) (hp : p.natDegree ≤ n) :
    ofCoeffs (fun i : Fin (n + 1) => p.coeff i) = p := by
  ext k
  by_cases hk : k ≤ n
  · exact coeff_ofCoeffs (fun i : Fin (n + 1) => p.coeff i) ⟨k, Nat.lt_succ_of_le hk⟩
  · push Not at hk
    rw [_root_.Polynomial.coeff_eq_zero_of_natDegree_lt
        (lt_of_le_of_lt (natDegree_ofCoeffs_le _) hk),
      _root_.Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hp hk)]

/-- Axis-line answers: coefficient vectors of length `d + 1` versus polynomials of degree
at most `d`. -/
def axisEquiv : LinePoly F d ≃ MIPStarRE.LDT.AxisLinePolynomial (lidtParams F m d) where
  toFun c := ⟨ofCoeffs c, natDegree_ofCoeffs_le c⟩
  invFun f := fun i => f.poly.coeff i
  left_inv c := funext fun i => coeff_ofCoeffs c i
  right_inv f := MIPStarRE.LDT.AxisLinePolynomial.ext (ofCoeffs_coeff f.poly f.degreeBounded)

/-- Diagonal-line answers: coefficient vectors of length `m·d + 1` versus polynomials of
degree at most `m·d`. -/
def diagEquiv : LinePoly F (m * d) ≃ MIPStarRE.LDT.DiagonalLinePolynomial (lidtParams F m d) where
  toFun c := ⟨ofCoeffs c, natDegree_ofCoeffs_le c⟩
  invFun f := fun i => f.poly.coeff i
  left_inv c := funext fun i => coeff_ofCoeffs c i
  right_inv f := MIPStarRE.LDT.DiagonalLinePolynomial.ext (ofCoeffs_coeff f.poly f.degreeBounded)

@[simp] theorem axisEquiv_poly (c : LinePoly F d) :
    (axisEquiv (m := m) c).poly = ofCoeffs c := rfl

@[simp] theorem diagEquiv_poly (c : LinePoly F (m * d)) :
    (diagEquiv (d := d) c).poly = ofCoeffs c := rfl

/-! ## Multivariate polynomials from coefficient tables -/

/-- The exponent vector of a monomial index. -/
def expo (e : Fin m → Fin (d + 1)) : Fin m →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun i => (e i : ℕ)

omit [NeZero m] in
@[simp] theorem expo_apply (e : Fin m → Fin (d + 1)) (i : Fin m) : expo e i = e i := by
  simp [expo]

omit [NeZero m] in
theorem expo_injective : Function.Injective (expo (m := m) (d := d)) := by
  intro e e' h
  funext i
  simpa [Fin.val_inj] using congrArg (fun s : Fin m →₀ ℕ => s i) h

/-- The multivariate polynomial with the given coefficient table. -/
def toMv (c : LowIndDegPoly (F := F) (m := m) (d := d)) : MvPolynomial (Fin m) F :=
  ∑ e, MvPolynomial.monomial (expo e) (c e)

omit [Fintype F] [DecidableEq F] [NeZero m] in
theorem coeff_toMv (c : LowIndDegPoly (F := F) (m := m) (d := d)) (e : Fin m → Fin (d + 1)) :
    (toMv c).coeff (expo e) = c e := by
  simp [toMv, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial, expo_injective.eq_iff]

omit [Fintype F] [DecidableEq F] [NeZero m] in
theorem coeff_toMv_of_not_le (c : LowIndDegPoly (F := F) (m := m) (d := d)) (s : Fin m →₀ ℕ)
    (hs : ¬ ∀ i, s i ≤ d) : (toMv c).coeff s = 0 := by
  simp only [toMv, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
  refine Finset.sum_eq_zero fun e _ => ?_
  rw [if_neg]
  intro h
  apply hs
  intro i
  rw [← h, expo_apply]
  exact Nat.lt_succ_iff.mp (e i).isLt

omit [Fintype F] [DecidableEq F] [NeZero m] in
theorem degreeOf_toMv_le (c : LowIndDegPoly (F := F) (m := m) (d := d)) (i : Fin m) :
    (toMv c).degreeOf i ≤ d := by
  rw [MvPolynomial.degreeOf_le_iff]
  intro s hs
  by_contra h
  exact MvPolynomial.mem_support_iff.mp hs
    (coeff_toMv_of_not_le c s fun h' => h (h' i))

omit [Fintype F] [DecidableEq F] [NeZero m] in
/-- A polynomial of bounded individual degree is determined by its coefficient table. -/
theorem toMv_coeff (p : MvPolynomial (Fin m) F) (hp : ∀ i, p.degreeOf i ≤ d) :
    toMv (fun e : Fin m → Fin (d + 1) => p.coeff (expo e)) = p := by
  refine MvPolynomial.ext _ _ fun s => ?_
  by_cases hs : ∀ i, s i ≤ d
  · have : s = expo fun i => (⟨s i, Nat.lt_succ_of_le (hs i)⟩ : Fin (d + 1)) := by
      ext i; simp
    rw [this, coeff_toMv]
  · rw [coeff_toMv_of_not_le _ s hs]
    by_contra h
    push Not at hs
    obtain ⟨i, hi⟩ := hs
    have := MvPolynomial.degreeOf_le_iff.mp (hp i) s
      (MvPolynomial.mem_support_iff.mpr (Ne.symm h))
    omega

/-- Extensionality for MIPStarRE's global polynomial answers. -/
theorem polynomial_ext {g g' : MIPStarRE.LDT.Polynomial (lidtParams F m d)} (h : g.poly = g'.poly) :
    g = g' := by
  cases g; cases g'; cases h; rfl

/-- Global answers: coefficient tables versus polynomials of individual degree at most
`d`. -/
def lowIndDegEquiv :
    LowIndDegPoly (F := F) (m := m) (d := d) ≃ MIPStarRE.LDT.Polynomial (lidtParams F m d) where
  toFun c := ⟨toMv c, degreeOf_toMv_le c⟩
  invFun g := fun e => g.poly.coeff (expo e)
  left_inv c := funext fun e => coeff_toMv c e
  right_inv g := polynomial_ext (toMv_coeff g.poly g.lowIndividualDegree)

@[simp] theorem lowIndDegEquiv_poly (c : LowIndDegPoly (F := F) (m := m) (d := d)) :
    (lowIndDegEquiv c).poly = toMv c := rfl

end MIPRE.LIDT.Bridge

end


