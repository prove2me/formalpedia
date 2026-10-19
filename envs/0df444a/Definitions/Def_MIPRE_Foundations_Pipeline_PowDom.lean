-- Prove2me | Definitions.Def_MIPRE_Foundations_Pipeline_PowDom
-- name    : MIPRE_Foundations_Pipeline_PowDom
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-16T23:11:14.313453+00:00
-- url     : https://prove2.me/theorems/5665dba5-1a6f-49b4-8078-65836e59f4e9
-- title:
--   Definitions of PowDom: Domination by a power of a monomial The time bounds of the answer-reduced verifier (`thm:answer-reduction`) have the…
-- statement:
--   The definitions of the module `MIPRE.Foundations.Pipeline.PowDom` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Domination by a power of a monomial. The time bounds of the answer-reduced verifier (`thm:answer-reduction`) have the shape `(c (W + 1)^m X^e)^{K + 1}`: `W` a number dominating the parameters at index `n`, `X = |d| + 1` the size of the input and `K = μ` the input sampler's degree. It is the shape of the contract's `outBound bound λ μ σ n = P(L + σ)^{μ + 1}` at degree `d (μ + 1)`: one call to a sampler of coefficient `B ≤ W` and degree `K` on a query of size below `c (W + 1)^m X^e` costs `B (c (W + 1)^m X^e)^K`, which is of this shape (`ofCall`), and so is any fixed polynomial of such a cost…
--
--   **Definitions** (1): `MIPRE.Pipeline.PDom` (`v ≤ (c (W + 1)^m X^e)^{K + 1}`.).
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.Pipeline.PowDom` (`MIPRE/Foundations/Pipeline/PowDom.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 5 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Pipeline/PowDom.lean; blueprint lem:ar-construction

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Pipeline/PowDom.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Tactic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Growth
import Definitions.Def_MIPRE_Foundations_Repeat_Dom

/-!
# Domination by a power of a monomial

The time bounds of the answer-reduced verifier (`thm:answer-reduction`) have the shape
`(c (W + 1)^m X^e)^{K + 1}`: `W` a number dominating the parameters at index `n`, `X = |d| + 1`
the size of the input and `K = μ` the input sampler's degree. It is the shape of the contract's
`outBound bound λ μ σ n = P(L + σ)^{μ + 1}` at degree `d (μ + 1)`: one call to a sampler of
coefficient `B ≤ W` and degree `K` on a query of size below `c (W + 1)^m X^e` costs
`B (c (W + 1)^m X^e)^K`, which is of this shape (`ofCall`), and so is any fixed polynomial of
such a cost (`poly`). `MIPRE.Repeat.Dom` is the unpowered shape `c (W + 1)^m X^{e (K + 1)}`,
which suffices when the coefficient of the simulated program does not depend on `K`; here the
powered coefficient carries the constants that a query larger than the input by a constant
factor raises to the power `K`, and the index-independent `K + 1 ≤ 2^{K + 1}` (`ofLeK`).

`PDom W X K c m e v` says `v` is below `(c (W + 1)^m X^e)^{K + 1}`; the combinators assemble the
constants, and `le_final` reads off the coefficient `(c (W + 1)^m)^{K + 1}` and degree
`e (K + 1)`.
-/

namespace MIPRE.Pipeline

open Cost

/-- `v ≤ (c (W + 1)^m X^e)^{K + 1}`. -/
def PDom (W X K c m e v : ℕ) : Prop := v ≤ (c * (W + 1) ^ m * X ^ e) ^ (K + 1)

namespace PDom

variable {W X K : ℕ}

end PDom

end MIPRE.Pipeline


