-- Prove2me | Definitions.Def_APSPSource_ThreeSumApsp_Sec2_Lemma6
-- name    : APSPSource_ThreeSumApsp_Sec2_Lemma6
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-06T07:47:19.60731+00:00
-- url     : https://prove2.me/theorems/7db63b6b-6a11-4140-8439-b69af4dfe331
-- title:
--   Finite index equivalences for algebraic variables and terms
-- statement:
--   The left alphabet consists of three symbols $x_i$ and four symbols $p_{ij}$; the right alphabet similarly consists of three $y_j$ and four $q_{ij}$. The bundle supplies the explicit equivalences
--
--   $$\{x_i,p_{ij}}\simeq\{0,1,2\}\sqcup\bigl(\{0,1\}\times\{0,1\}\bigr),$$
--   $$\{y_j,q_{ij}\}\simeq\{0,1,2\}\sqcup\bigl(\{0,1\}\times\{0,1\}\bigr).$$
--
--   Each outer variable maps to its index in the first summand; each inner variable maps to its pair of indices in the second. The ten terms are indexed by an optional pair:
--
--   $$\{P_{ij}:0\le i,j<3\}\cup\{P_0\}\simeq\operatorname{Option}(\{0,1,2\}^2),$$
--
--   with $P_{ij}$ mapped to the pair $(i,j)$ and the distinguished term $P_0$ mapped to the absent value. The definitions include their inverse laws by inspection of constructors.
--
--   These interfaces supply finite indices for the variable and term alphabets used in the encoding recursions.
--
--   References:
--
--   1. [Source formalization, lines 60–91](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Sec2/Lemma6.lean#L60-L91).
-- source:
--   https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Sec2/Lemma6.lean#L60-L91

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Definitions.Def_APSPSource_PaperStatements
import Definitions.Def_TrulySubcubicAPSP_SourceSpecification
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Probability.Independence.Basic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option relaxedAutoImplicit false


/-!
# Lemma 6: Schönhage's identity

Sections 2.1 and 2.2. After Strassen's identity (equation (1)), which the paper
recalls, this file treats Schönhage's. It has ten terms `λ`, each the product of a linear form `φ_λ`
in the seven left variables, a linear form `ψ_λ` in the seven right variables and a linear form
`χ_λ` in the ten output variables. Lemma 6 says that `∑_λ φ_λ ψ_λ χ_λ = G + E`, an identity of
polynomials in the 24 variables: `G` holds the outer product and the inner product that are wanted,
and `E` is an error.

* A linear form is the vector of its coefficients. `formL`, `formR` and `formO` turn it into a
  polynomial, and they are linear (`formL_eq_linearCombination` and its two companions).
* The proof of `lemma_6` is the paper's. The coefficient of `z_ij` comes only from the term `P_ij`.
  In the coefficient of `z₀` the products `x_i y_j` cancel, the cross terms vanish because the
  columns of `p̂` and the rows of `q̂` sum to zero (`pHat_column_sum`, `qHat_row_sum`), and what
  remains is the inner product (`sum_pHat_mul_qHat`).
* Second observation after the lemma: every term contributes to `z₀`, and only `P_ij` contributes to
  `z_ij` (`Term.contributes_z0`, `Term.contributes_z_iff`).

The later files on Section 2 use the second observation and the coefficients of the forms; none of
their proofs uses `lemma_6`.
-/

@[expose] public section

open Finset

namespace ThreeSumApsp















/-! ### The alphabets -/

/-- The left variables, listed: `x i` is `.inl i`, and `p i j` is `.inr (i, j)`. -/
def LeftVar.equiv : LeftVar ≃ Fin 3 ⊕ Fin 2 × Fin 2 where
  toFun
    | .x i => .inl i
    | .p i j => .inr (i, j)
  invFun
    | .inl i => .x i
    | .inr (i, j) => .p i j
  left_inv s := by cases s <;> rfl
  right_inv s := by rcases s with _ | ⟨_, _⟩ <;> rfl

/-- The right variables, listed: `y j` is `.inl j`, and `q i j` is `.inr (i, j)`. -/
def RightVar.equiv : RightVar ≃ Fin 3 ⊕ Fin 2 × Fin 2 where
  toFun
    | .y j => .inl j
    | .q i j => .inr (i, j)
  invFun
    | .inl j => .y j
    | .inr (i, j) => .q i j
  left_inv t := by cases t <;> rfl
  right_inv t := by rcases t with _ | ⟨_, _⟩ <;> rfl

/-- The terms, listed: `P i j` is `some (i, j)`, and `P0` is `none`. -/
def Term.equiv : Term ≃ Option (Fin 3 × Fin 3) where
  toFun
    | .P i j => some (i, j)
    | .P0 => none
  invFun
    | some (i, j) => .P i j
    | none => .P0
  left_inv t := by cases t <;> rfl
  right_inv t := by rcases t with _ | ⟨_, _⟩ <;> rfl



















/-! ### Linear forms as polynomials -/























































/-! ### Lemma 6 -/



































/-! ### Which terms contribute to which output variables -/




































end ThreeSumApsp


