-- Prove2me | Definitions.Def_MIPRE_Background_QLD_CLBinary
-- name    : MIPRE_Background_QLD_CLBinary
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T01:03:22.756632+00:00
-- url     : https://prove2.me/theorems/006c9cd8-750d-4381-b4c0-45dbd11a6172
-- title:
--   Definitions of CLBinary: Binary coordinates for the concrete Pauli CL family A supplied basis of the actual finite field converts the twenty-six…
-- statement:
--   The definitions of the module `MIPRE.Background.QLD.CLBinary` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Binary coordinates for the concrete Pauli CL family. A supplied basis of the actual finite field converts the twenty-six concrete presentations into three-level binary presentations on `(3m+3)t` numbered coordinates. The theorems identify both the exact question map and the existing Pauli game's joint question law. No executable or uniform runtime claim is part of this coordinate conversion.
--
--   **Definitions** (8): `MIPRE.QLD.PauliCL.binaryCoordEquiv` (Each field coordinate is followed by its `t` bits in basis order.); `MIPRE.QLD.PauliCL.binaryPresentation`; `MIPRE.QLD.PauliCL.binaryQuestion` (Decode the binary content of a question of the given type.); `MIPRE.QLD.PauliCL.binarySampleEquiv`; `MIPRE.QLD.PauliCL.binaryVectorEquiv`; `MIPRE.QLD.PauliCL.coordNumbering` (Field coordinates in the fixed order: `uX`, `uZ`, seed, direction, `rX`, `rZ`.); `_private.MIPRE.Background.QLD.CLBinary.0.MIPRE.QLD.PauliCL.basisIndex`; `_private.MIPRE.Background.QLD.CLBinary.0.MIPRE.QLD.PauliCL.unitIndex`.
--
--   **Embedded lemmas** (6): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `coordNumbering_direction`, `coordNumbering_point_X`, `coordNumbering_point_Z`, `coordNumbering_scalar_X`, `coordNumbering_scalar_Z`, `coordNumbering_seed`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Background.QLD.CLBinary` (`MIPRE/Background/QLD/CLBinary.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 31 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/QLD/CLBinary.lean; blueprint lem:intro-executable-lines

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/QLD/CLBinary.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.Star.Module
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Sum
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Pi
import Mathlib.Order.Fin.Basic
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.Module
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Background_LIDT_Game
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Canonical
import Definitions.Def_MIPRE_Background_LIDT_CLGame
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_CL_Closure_B
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_GameTransport
import Definitions.Def_MIPRE_Foundations_POVMValue
import Definitions.Def_MIPRE_Foundations_PVM
import Definitions.Def_MIPRE_Foundations_PVM_B
import Definitions.Def_MIPRE_Foundations_LowDegree_SchwartzZippel
import Definitions.Def_MIPRE_Foundations_LowDegree_Anticomm
import Definitions.Def_MIPRE_Foundations_GameAdapt
import Definitions.Def_MIPRE_Foundations_RegisterReindex
import Definitions.Def_MIPRE_Foundations_RegisterReindex_B
import Definitions.Def_MIPRE_Foundations_SampledGame
import Definitions.Def_MIPRE_Foundations_CL_Downsize
import Definitions.Def_MIPRE_LCS_Basic
import Definitions.Def_MIPRE_LCS_Common
import Definitions.Def_MIPRE_LCS_Measurement
import Definitions.Def_MIPRE_LCS_Observable
import Definitions.Def_MIPRE_LCS_Strategy_ObservableToProjector
import Definitions.Def_MIPRE_LCS_NonlocalGame
import Definitions.Def_MIPRE_LCS_Pauli
import Definitions.Def_MIPRE_LCS_MagicSquare_Strategy
import Definitions.Def_MIPRE_LCS_MagicSquare_Game
import Definitions.Def_MIPRE_Background_QLD_Game
import Definitions.Def_MIPRE_Background_QLD_CLPresentation
import Theorems.Thm_MIPRE_CL_CLFun_eval_reindex

/-! # Binary coordinates for the concrete Pauli CL family

A supplied basis of the actual finite field converts the twenty-six concrete
presentations into three-level binary presentations on `(3m+3)t` numbered
coordinates. The theorems identify both the exact question map and the
existing Pauli game's joint question law. No executable or uniform runtime
claim is part of this coordinate conversion.
-/

noncomputable section
namespace MIPRE.QLD.PauliCL
open Finset Classical
set_option linter.unusedSectionVars false

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Algebra (ZMod 2) F] {m t : ℕ} [NeZero m]

def basisIndex : Bas ≃ Fin 2 where
  toFun | .X => 0 | .Z => 1
  invFun i := if i = 0 then .X else .Z
  left_inv W := by cases W <;> rfl
  right_inv i := by fin_cases i <;> rfl

def unitIndex : Unit ≃ Fin 1 where
  toFun _ := 0
  invFun _ := ()
  left_inv u := by cases u; rfl
  right_inv i := by fin_cases i; rfl

/-- Field coordinates in the fixed order: `uX`, `uZ`, seed, direction,
`rX`, `rZ`. The numbering contains no arbitrary finite-type enumeration. -/
def coordNumbering (m : ℕ) : Coord m ≃ Fin (3 * m + 3) :=
  let points : Bas × Fin m ≃ Fin (2 * m) :=
    (Equiv.prodCongr basisIndex (Equiv.refl _)).trans finProdFinEquiv
  let tail : Unit ⊕ (Fin m ⊕ Bas) ≃ Fin (1 + (m + 2)) :=
    (Equiv.sumCongr unitIndex
      ((Equiv.sumCongr (Equiv.refl _) basisIndex).trans finSumFinEquiv)).trans finSumFinEquiv
  ((coordEquiv m).trans ((Equiv.sumCongr points tail).trans finSumFinEquiv)).trans
    (finCongr (by omega))

@[simp] theorem coordNumbering_point_X (m : ℕ) (i : Fin m) :
    (coordNumbering m (.point .X i)).val = i.val := by
  simp [coordNumbering, coordEquiv, basisIndex, finProdFinEquiv, finSumFinEquiv]

@[simp] theorem coordNumbering_point_Z (m : ℕ) (i : Fin m) :
    (coordNumbering m (.point .Z i)).val = m + i.val := by
  simp [coordNumbering, coordEquiv, basisIndex, finProdFinEquiv, finSumFinEquiv]
  omega

@[simp] theorem coordNumbering_seed (m : ℕ) :
    (coordNumbering m .seed).val = 2 * m := by
  simp [coordNumbering, coordEquiv, unitIndex, finSumFinEquiv]

@[simp] theorem coordNumbering_direction (m : ℕ) (i : Fin m) :
    (coordNumbering m (.direction i)).val = 2 * m + 1 + i.val := by
  simp [coordNumbering, coordEquiv, finSumFinEquiv]
  omega

@[simp] theorem coordNumbering_scalar_X (m : ℕ) :
    (coordNumbering m (.scalar .X)).val = 3 * m + 1 := by
  simp [coordNumbering, coordEquiv, basisIndex, finSumFinEquiv]
  omega

@[simp] theorem coordNumbering_scalar_Z (m : ℕ) :
    (coordNumbering m (.scalar .Z)).val = 3 * m + 2 := by
  simp [coordNumbering, coordEquiv, basisIndex, finSumFinEquiv]
  omega

/-- Each field coordinate is followed by its `t` bits in basis order. -/
def binaryCoordEquiv (m t : ℕ) : Coord m × Fin t ≃ Fin ((3 * m + 3) * t) :=
  (Equiv.prodCongr (coordNumbering m) (Equiv.refl _)).trans finProdFinEquiv

def binaryVectorEquiv (b : Module.Basis (Fin t) (ZMod 2) F) :
    (Coord m → F) ≃ₗ[ZMod 2] (Fin ((3 * m + 3) * t) → ZMod 2) :=
  (CL.downsizeEquiv b).trans (CL.reindexEquiv (binaryCoordEquiv m t))

def binaryPresentation (hm : m ∣ Fintype.card F)
    (b : Module.Basis (Fin t) (ZMod 2) F) (T : Ty) :
    CL.CLFun (ZMod 2) (Fin ((3 * m + 3) * t)) 3 :=
  ((presentation hm T).downsize b).reindex (binaryCoordEquiv m t)

/-- Decode the binary content of a question of the given type. -/
def binaryQuestion (b : Module.Basis (Fin t) (ZMod 2) F) (T : Ty)
    (x : Fin ((3 * m + 3) * t) → ZMod 2) : Question F m :=
  questionOfVector T ((binaryVectorEquiv b).symm x)

def binarySampleEquiv (b : Module.Basis (Fin t) (ZMod 2) F) :
    Sample F m ≃ (TyEdge × (Fin ((3 * m + 3) * t) → ZMod 2)) :=
  Equiv.prodCongr (Equiv.refl _) (contentEquiv.trans (binaryVectorEquiv b).toEquiv)

end MIPRE.QLD.PauliCL
end


