-- Prove2me | Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_Arithmetic
-- name    : QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_Arithmetic
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T10:37:18.599298+00:00
-- url     : https://prove2.me/theorems/89561755-6441-4c2f-9a74-52896eff20e5
-- title:
--   Arithmetic
-- statement:
--   Definitions and structural lemmas for Arithmetic, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/Arithmetic.lean

import Mathlib.FieldTheory.Finite.Extension
import Mathlib.FieldTheory.Finite.Trace
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.RingTheory.LaurentSeries
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.PolynomialAlgebra
set_option autoImplicit false
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups RatFunc
structure BasePrime where
  q : Nat
  prime : q.Prime
  five_le : 5 <= q
instance (P : BasePrime) : Fact P.q.Prime := ⟨P.prime⟩
inductive Rank where
  | three
  | four
  deriving DecidableEq
instance : Fintype Rank where
  elems := {.three, .four}
  complete := by intro rank; cases rank <;> simp
namespace Rank
def matrixRank : Rank -> Nat
  | three => 3
  | four => 4
def complexDimension (r : Rank) : Nat := r.matrixRank - 1
@[simp] theorem matrixRank_three : matrixRank three = 3 := rfl
@[simp] theorem matrixRank_four : matrixRank four = 4 := rfl
@[simp] theorem complexDimension_three : complexDimension three = 2 := rfl
@[simp] theorem complexDimension_four : complexDimension four = 3 := rfl
def residueExponent (r : Rank) (level : Nat) : Nat :=
  r.matrixRank * (3 + level)
end Rank
abbrev BaseField (P : BasePrime) := ZMod P.q
noncomputable abbrev ConstantExtension (P : BasePrime) (r : Rank) :=
  GaloisField P.q r.matrixRank
abbrev FunctionField (P : BasePrime) := RatFunc (BaseField P)
abbrev BuildingLocalField (P : BasePrime) := LaurentSeries (BaseField P)
abbrev BuildingIntegerRing (P : BasePrime) := PowerSeries (BaseField P)
abbrev PolynomialRing (P : BasePrime) := Polynomial (BaseField P)
abbrev IntegralArithmeticRing (P : BasePrime) :=
  Localization.Away (1 + Polynomial.X : PolynomialRing P)
abbrev ArithmeticRing (P : BasePrime) :=
  Localization.Away
    (Polynomial.X * (1 + Polynomial.X) : PolynomialRing P)
noncomputable abbrev yAdicPlace (P : BasePrime) :=
  RatFunc.polynomialValuationX (BaseField P)
noncomputable def functionFieldToBuildingLocalField (P : BasePrime) :
    RingHom (FunctionField P) (BuildingLocalField P) :=
  algebraMap (FunctionField P) (BuildingLocalField P)
noncomputable abbrev ResidueField (P : BasePrime) (r : Rank) (level : Nat) :=
  GaloisField P.q (r.residueExponent level)
noncomputable instance (P : BasePrime) (r : Rank) :
    Fintype (ConstantExtension P r) :=
  Fintype.ofFinite _
noncomputable instance (P : BasePrime) (r : Rank) (level : Nat) :
    Fintype (ResidueField P r level) :=
  Fintype.ofFinite _
noncomputable def constantBasis (P : BasePrime) (r : Rank) :
    Module.Basis (Fin r.matrixRank) (BaseField P) (ConstantExtension P r) :=
  Module.finBasisOfFinrankEq (BaseField P) (ConstantExtension P r)
    (GaloisField.finrank P.q (by cases r <;> simp [Rank.matrixRank]))
noncomputable def constantFrobenius (P : BasePrime) (r : Rank) :
    AlgEquiv (BaseField P) (ConstantExtension P r) (ConstantExtension P r) :=
  FiniteField.frobeniusAlgEquivOfAlgebraic
    (BaseField P) (ConstantExtension P r)
noncomputable def beta (P : BasePrime) (r : Rank) : ConstantExtension P r :=
  1
noncomputable def betaLinearPolynomial (P : BasePrime) (r : Rank) :
    Polynomial (ConstantExtension P r) :=
  1 + Polynomial.C (beta P r) * Polynomial.X
noncomputable def sourceOnePlusY (P : BasePrime) (r : Rank) :
    Polynomial (BaseField P) :=
  (1 + Polynomial.X) ^ r.matrixRank
noncomputable def sourceYPolynomial (P : BasePrime) (r : Rank) :
    Polynomial (BaseField P) :=
  sourceOnePlusY P r - 1
noncomputable def constantRegularMatrix (P : BasePrime) (r : Rank) :
    AlgHom (BaseField P) (ConstantExtension P r)
      (Matrix (Fin r.matrixRank) (Fin r.matrixRank) (BaseField P)) :=
  Algebra.leftMulMatrix (constantBasis P r)
noncomputable def frobeniusGL (P : BasePrime) (r : Rank) :
    Matrix.GeneralLinearGroup (Fin r.matrixRank) (BaseField P) :=
  (Matrix.GeneralLinearGroup.toLin' (constantBasis P r)).symm
    (LinearMap.GeneralLinearGroup.ofLinearEquiv
      (constantFrobenius P r).toLinearEquiv)
abbrev PGL (P : BasePrime) (r : Rank) (level : Nat) :=
  Matrix.ProjGenLinGroup (Fin r.matrixRank) (ResidueField P r level)
noncomputable def specialToProjective (P : BasePrime) (r : Rank) (level : Nat) :
    MonoidHom
      (Matrix.SpecialLinearGroup (Fin r.matrixRank) (ResidueField P r level))
      (PGL P r level) :=
  Matrix.ProjGenLinGroup.mk.comp Matrix.SpecialLinearGroup.toGL
noncomputable def PSL (P : BasePrime) (r : Rank) (level : Nat) :
    Subgroup (PGL P r level) :=
  (specialToProjective P r level).range
end QEC.Coding.HighDimensionalExpander.CartwrightSteger


