-- Prove2me | Definitions.Def_APSPSource_ThreeSumApsp_Spec_Sec2_Theorem5_Alphabets
-- name    : APSPSource_ThreeSumApsp_Spec_Sec2_Theorem5_Alphabets
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-06T08:09:28.625958+00:00
-- url     : https://prove2.me/theorems/b538488d-4600-4cdc-8b11-e540a087e1a4
-- title:
--   Numeric alphabets and coefficient tables for the algebraic encoding
-- statement:
--   The algebraic symbols are assigned fixed digit encodings. With zero-based indices, the left and right variables use base seven:
--
--   $$x_i\mapsto i,\quad p_{ij}\mapsto3+2i+j,\qquad y_j\mapsto j,\quad q_{ij}\mapsto3+2i+j.$$
--
--   Output variables and terms use base ten, and inner index pairs use base four:
--
--   $$z_{ij},P_{ij}\mapsto3i+j,\qquad z_0,P_0\mapsto9,\qquad(i,j)\mapsto2i+j.$$
--
--   The bundle gives each inverse map and the associated finite equivalence. It then encodes left and right strings in base seven, output strings and leaves in base ten, outer index strings in base three, and inner index-pair strings in base four. Decoding reconstructs a length-specified term string; a separate total digit-to-term function returns $P_0$ for natural inputs at least ten.
--
--   Two explicit $10\times7$ integer tables store the left and right coefficient families in digit order, together with row-major flattened versions. These definitions connect symbolic algebraic objects to the numeric indices and tables used in programs. Correctness lemmas for the concrete coefficient tables are separate from the definitions.
--
--   References:
--
--   1. [Source formalization, lines 40–113](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Spec/Sec2/Theorem5/Alphabets.lean#L40-L113).
--   2. [Source formalization, lines 125–130](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Spec/Sec2/Theorem5/Alphabets.lean#L125-L130).
--   3. [Source formalization, lines 146–162](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Spec/Sec2/Theorem5/Alphabets.lean#L146-L162).
--   4. [Source formalization, lines 167–168](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Spec/Sec2/Theorem5/Alphabets.lean#L167-L168).
--   5. [Source formalization, lines 245–263](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Spec/Sec2/Theorem5/Alphabets.lean#L245-L263).
-- source:
--   https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Spec/Sec2/Theorem5/Alphabets.lean#L40-L113; https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Spec/Sec2/Theorem5/Alphabets.lean#L125-L130; https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Spec/Sec2/Theorem5/Alphabets.lean#L146-L162; https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Spec/Sec2/Theorem5/Alphabets.lean#L167-L168; https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Spec/Sec2/Theorem5/Alphabets.lean#L245-L263

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Definitions.Def_APSPSource_PaperStatements
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Digits
import Definitions.Def_TrulySubcubicAPSP_SourceSpecification
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.GetD
import Mathlib.Data.List.OfFn
import Mathlib.Data.Nat.Count
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Logic.Equiv.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Probability.Independence.Basic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option relaxedAutoImplicit false


/-!
# The alphabets of Schönhage's identity as digits

Section 2.2 names seven left variables, seven right variables, ten output variables and
ten terms; Section 2.3.1 indexes arrays by strings over these alphabets.  Here every
letter gets a digit, so that a string becomes a number (`codeStr`).

* The left variables `x₁ x₂ x₃ p₁₁ p₁₂ p₂₁ p₂₂` are the digits `0, …, 6`; likewise the right
  variables.
* The output variables `z₁₁ z₁₂ … z₃₃ z₀` are the digits `0, …, 9`, and the terms `P₁₁ … P₃₃ P₀`
  likewise, so that `z_ij` and `P_ij` have the same digit `3(i-1) + (j-1)`, and `z₀` and `P₀` have
  the digit 9.
* Left and right strings are numbers in base 7 (`codeL`, `codeR`), output strings, vertices and
  leaves in base 10 (`codeO`, `codeT`), strings of indices of outer variables in base 3
  (`codeOuter`) and of inner variables in base 4 (`codeInner`), always with level 1 most
  significant.
* Which output variables are inner, and which term contributes to which output variable (Section
  2.2), is read off the digits (`outVar_isInner_iff`, `contributes_iff`).
* The coefficients of the linear forms `φ_λ` and `ψ_λ` (Section 2.2) are written out as the rows of
  two 10 × 7 tables, `phiTable` and `psiTable`, which the programs store row after row
  (`phiFlat_spec`, `psiFlat_spec`).
-/

@[expose] public section

namespace ThreeSumApsp.Spec

/-! ## Digits -/

/-- The digit of a left variable. -/
def leftIdx : LeftVar → Fin 7
  | .x i => ⟨i, by omega⟩
  | .p i j => ⟨3 + 2 * i + j, by omega⟩

/-- The left variable with a given digit. -/
def leftOfIdx (k : Fin 7) : LeftVar :=
  if h : (k : ℕ) < 3 then .x ⟨k, h⟩
  else .p ⟨((k : ℕ) - 3) / 2, by omega⟩ ⟨((k : ℕ) - 3) % 2, by omega⟩

/-- The digit of a right variable. -/
def rightIdx : RightVar → Fin 7
  | .y j => ⟨j, by omega⟩
  | .q i j => ⟨3 + 2 * i + j, by omega⟩

/-- The right variable with a given digit. -/
def rightOfIdx (k : Fin 7) : RightVar :=
  if h : (k : ℕ) < 3 then .y ⟨k, h⟩
  else .q ⟨((k : ℕ) - 3) / 2, by omega⟩ ⟨((k : ℕ) - 3) % 2, by omega⟩

/-- The digit of an output variable. -/
def outIdx : OutVar → Fin 10
  | .z i j => ⟨3 * i + j, by omega⟩
  | .z0 => 9

/-- The output variable with a given digit. -/
def outOfIdx (k : Fin 10) : OutVar :=
  if h : (k : ℕ) < 9 then .z ⟨(k : ℕ) / 3, by omega⟩ ⟨(k : ℕ) % 3, by omega⟩ else .z0

/-- The digit of a term. -/
def termIdx : Term → Fin 10
  | .P i j => ⟨3 * i + j, by omega⟩
  | .P0 => 9

/-- The term with a given digit. -/
def termOfIdx (k : Fin 10) : Term :=
  if h : (k : ℕ) < 9 then .P ⟨(k : ℕ) / 3, by omega⟩ ⟨(k : ℕ) % 3, by omega⟩ else .P0

/-- The digit of an index pair `(i, j)` of an inner variable. -/
def pairIdx (p : Fin 2 × Fin 2) : Fin 4 := ⟨2 * p.1 + p.2, by omega⟩

/-- The index pair with a given digit. -/
def pairOfIdx (k : Fin 4) : Fin 2 × Fin 2 := (⟨(k : ℕ) / 2, by omega⟩, ⟨(k : ℕ) % 2, by omega⟩)

/-- The left variables and their digits. -/
def leftEquiv : LeftVar ≃ Fin 7 where
  toFun := leftIdx
  invFun := leftOfIdx
  left_inv := by decide
  right_inv := by decide

/-- The right variables and their digits. -/
def rightEquiv : RightVar ≃ Fin 7 where
  toFun := rightIdx
  invFun := rightOfIdx
  left_inv := by decide
  right_inv := by decide

/-- The output variables and their digits. -/
def outEquiv : OutVar ≃ Fin 10 where
  toFun := outIdx
  invFun := outOfIdx
  left_inv := by decide
  right_inv := by decide

/-- The terms and their digits. -/
def termEquiv : Term ≃ Fin 10 where
  toFun := termIdx
  invFun := termOfIdx
  left_inv := by decide
  right_inv := by decide

/-- The term with the digit `t`, for a natural number `t` below 10 (and `P₀` from 10 on). -/
def termOfNat (t : ℕ) : Term := if h : t < 10 then termEquiv.symm ⟨t, h⟩ else .P0











/-- The index pairs and their digits. -/
def pairEquiv : Fin 2 × Fin 2 ≃ Fin 4 where
  toFun := pairIdx
  invFun := pairOfIdx
  left_inv := by decide
  right_inv := by decide

/-! Applying one of the five bijections gives the digit. -/











/-! ## Codes of strings -/

/-- The code of a left string, in base 7. -/
def codeL {n : ℕ} (u : LeftStr n) : ℕ := codeStr leftEquiv u

/-- The code of a right string, in base 7. -/
def codeR {n : ℕ} (v : RightStr n) : ℕ := codeStr rightEquiv v

/-- The code of an output string, in base 10. -/
def codeO {n : ℕ} (w : OutStr n) : ℕ := codeStr outEquiv w

/-- The code of a vertex or a leaf, in base 10. -/
def codeT {n : ℕ} (τ : Vertex n) : ℕ := codeStr termEquiv τ

/-- The code of a string of indices of outer variables, in base 3. -/
def codeOuter {n : ℕ} (r : Fin n → Fin 3) : ℕ := codeStr (Equiv.refl (Fin 3)) r

/-- The code of a string of index pairs of inner variables, in base 4. -/
def codeInner {n : ℕ} (π : Fin n → Fin 2 × Fin 2) : ℕ := codeStr pairEquiv π




/-- The vertex or leaf with a given code. -/
def decodeT (n c : ℕ) : Vertex n := decodeStr termEquiv n c

/-! ### Codes of output strings and of vertices

The general facts about `codeStr`, under names of their own for the two codes that occur most. -/




































/-! ## The structure of the identity, in digits -/

































/-! ## The coefficients of the linear forms, as tables -/

/-- The coefficients of the forms `φ_λ`: row `λ`, column `s`, both by digits. -/
def phiTable : List (List ℤ) :=
  [[1, 0, 0, 1, 0, 0, 0], [1, 0, 0, 0, 1, 0, 0], [1, 0, 0, 0, 0, 0, 0],
   [0, 1, 0, 0, 0, 1, 0], [0, 1, 0, 0, 0, 0, 1], [0, 1, 0, 0, 0, 0, 0],
   [0, 0, 1, -1, 0, -1, 0], [0, 0, 1, 0, -1, 0, -1], [0, 0, 1, 0, 0, 0, 0],
   [-1, -1, -1, 0, 0, 0, 0]]

/-- The coefficients of the forms `ψ_λ`: row `λ`, column `t`, both by digits. -/
def psiTable : List (List ℤ) :=
  [[1, 0, 0, 1, 0, 0, 0], [0, 1, 0, 0, 1, 0, 0], [0, 0, 1, -1, -1, 0, 0],
   [1, 0, 0, 0, 0, 1, 0], [0, 1, 0, 0, 0, 0, 1], [0, 0, 1, 0, 0, -1, -1],
   [1, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0],
   [1, 1, 1, 0, 0, 0, 0]]

/-- The table of the coefficients `φ_λ(s)`, row after row, as a program stores it. -/
def phiFlat : List ℤ := phiTable.flatten

/-- The table of the coefficients `ψ_λ(t)`, row after row, as a program stores it. -/
def psiFlat : List ℤ := psiTable.flatten



















end ThreeSumApsp.Spec


