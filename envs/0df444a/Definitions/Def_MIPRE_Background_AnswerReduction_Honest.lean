-- Prove2me | Definitions.Def_MIPRE_Background_AnswerReduction_Honest
-- name    : MIPRE_Background_AnswerReduction_Honest
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T00:58:03.385459+00:00
-- url     : https://prove2.me/theorems/fdd07017-9843-41e7-b21f-8dc82c416083
-- title:
--   Definitions of Honest: Honest answers of the answer-reduced verifier Piece AR-4 of `planning/answer-reduction.md`, the combinatorial half: the…
-- statement:
--   The definitions of the module `MIPRE.Background.AnswerReduction.Honest` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Honest answers of the answer-reduced verifier. Piece AR-4 of `planning/answer-reduction.md`, the combinatorial half: the decision predicate `accepts` of `fig:decider-pcp` accepts the honest answers of two players who answer from polynomial data that is consistent in the ways the five steps check. A player's data (`HPolys`) is five `m`-variate polynomials `g₁ … g₅`, one for each of the first five copies of the low-degree test, and `m' + 6` `m'`-variate polynomials `c`, the codewords of the sixth copy. Its honest answer to a question of type `(i, τ)` (`honestAns`) is the honest answer…
--
--   **Definitions** (6): `MIPRE.AnswerReduction.Consistent` (**The consistency of two players' data** that the five steps read: equal roles have equal data, and an isolated player `v`'s `g_v` is an…); `MIPRE.AnswerReduction.HPolys` (**A player's polynomial data**: the answer polynomials of the first five copies, and the codewords of the sixth.); `MIPRE.AnswerReduction.HPolys.LowDeg` (Every polynomial has individual degree at most `d = 7`.); `MIPRE.AnswerReduction.HPolys.Oracle` (An oracle's data: the sixth copy's first five codewords are the `gⱼ` read on their blocks, and every point's evaluations pass the check…); `MIPRE.AnswerReduction.HPolys.idx6` (The index `j ≤ 5` of a first-five copy among the sixth copy's codewords.); `MIPRE.AnswerReduction.honestAns` (**The honest answer** of a player with data `H` to the question of PCP type `t` read off `y`.).
--
--   **Formalization Note** The bundle is the module `MIPRE.Background.AnswerReduction.Honest` (`MIPRE/Background/AnswerReduction/Honest.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 31 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/AnswerReduction/Honest.lean; blueprint lem:ar-completeness

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/AnswerReduction/Honest.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Pi
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Background_LIDT_Game
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Canonical
import Definitions.Def_MIPRE_Background_LIDT_CLGame
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Background_LIDT_Presentation
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_SAT_Circuit
import Definitions.Def_MIPRE_Foundations_SAT_Cnf
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_CL_Closure
import Definitions.Def_MIPRE_Foundations_CL_Closure_B
import Definitions.Def_MIPRE_Foundations_CL_Sampler
import Definitions.Def_MIPRE_Foundations_Verifier
import Definitions.Def_MIPRE_Foundations_SAT_Succinct
import Definitions.Def_MIPRE_Foundations_SAT_Decoupled
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Fold
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_SAT_Pcp
import Definitions.Def_MIPRE_Background_AnswerReduction_PcpPresentation
import Definitions.Def_MIPRE_Foundations_OracularGame
import Definitions.Def_MIPRE_Background_AnswerReduction_Predicate
import Definitions.Def_MIPRE_Foundations_LowDegree_LineRestrict
import Definitions.Def_MIPRE_Background_LIDT_CLHonest

/-!
# Honest answers of the answer-reduced verifier

Piece AR-4 of `planning/answer-reduction.md`, the combinatorial half: the decision predicate
`accepts` of `fig:decider-pcp` accepts the honest answers of two players who answer from
polynomial data that is consistent in the ways the five steps check.

A player's data (`HPolys`) is five `m`-variate polynomials `g₁ … g₅`, one for each of the first
five copies of the low-degree test, and `m' + 6` `m'`-variate polynomials `c`, the codewords of the
sixth copy. Its honest answer to a question of type `(i, τ)` (`honestAns`) is the honest answer
(`LIDT.CL.honest`) of `gᵢ`, or of `c` for the sixth copy, to the seeded question the type's
presentation computes. In the paper (`ld_compiler.tex`, the completeness part of `thm:ar`):

* an oracle's data is the PCP proof of its pair of answers: `g₁, g₂` the low-degree encodings of
  the two answers, `g₃ … g₅` the proof's other answer polynomials, and `c` the five `gᵢ` read on
  their blocks of `F^{m'}` followed by the constraint polynomials (`HPolys.Oracle`);
* an isolated player's data has for `g_v` the low-degree encoding of its own answer, `v` its
  role's index, and anything of low degree elsewhere (zero, in AR-4's instance).

`accepts_honest` is the statement: for two questions read off one PCP vector, players whose data
is of individual degree at most `d = 7` (`HPolys.LowDeg`), equal for equal roles, with the oracle's
`g_v` the isolated player `v`'s, and with an oracle's data passing its PCP check at every point,
are accepted.
-/

noncomputable section

namespace MIPRE.AnswerReduction

open Finset MIPRE.LIDT MIPRE.LIDT.CL SAT Pcp

variable {P : PcpParams} {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **A player's polynomial data**: the answer polynomials of the first five copies, and the
codewords of the sixth. -/
structure HPolys (P : PcpParams) (F : Type*) [Field F] where
  /-- The polynomials of copies `1`–`5`. -/
  g : Fin 5 → MvPolynomial (Fin P.m) F
  /-- The `m' + 6` codewords of copy `6`. -/
  c : Fin (P.m' + 6) → MvPolynomial (Fin P.m') F

namespace HPolys

/-- Every polynomial has individual degree at most `d = 7`. -/
def LowDeg (H : HPolys P F) : Prop :=
  (∀ j i, (H.g j).degreeOf i ≤ dPcp) ∧ ∀ j i, (H.c j).degreeOf i ≤ dPcp

/-- The index `j ≤ 5` of a first-five copy among the sixth copy's codewords. -/
def idx6 (j : Fin 5) : Fin (P.m' + 6) := ⟨j, by have := j.isLt; omega⟩

/-- An oracle's data: the sixth copy's first five codewords are the `gⱼ` read on their blocks,
and every point's evaluations pass the check `chk`. -/
def Oracle (H : HPolys P F) (chk : (Fin P.m' → F) → (Fin (P.m' + 6) → F) → Bool) : Prop :=
  (∀ (j : Fin 5) (z : Fin P.m' → F),
      MvPolynomial.eval z (H.c (idx6 j)) = MvPolynomial.eval (P.block j z) (H.g j)) ∧
    ∀ z, chk z (fun j => MvPolynomial.eval z (H.c j)) = true

end HPolys

variable [NeZero P.m] {hm : P.m ∣ Fintype.card F} {hm' : P.m' ∣ Fintype.card F}
  (S : Sel F P.m hm) (S' : Sel F P.m' hm')

/-- **The honest answer** of a player with data `H` to the question of PCP type `t` read off `y`. -/
def honestAns (H : HPolys P F) (t : PcpTy) (y : Coord P → F) : Ans P F :=
  if h : (t.1 : ℕ) < 5 then
    .inl (LIDT.CL.honest hm (d := dPcp) (fun _ => H.g ⟨t.1, h⟩) (q1 S ⟨t.1, h⟩ t.2 y))
  else .inr (LIDT.CL.honest hm' (d := dPcp) H.c (q6 S' t.2 y))

/-! ## The questions of one PCP vector -/

/-! ## Reading the honest answers -/

/-! ## The five steps -/

variable {X : Type*} (check : X → (Fin P.m' → F) → (Fin (P.m' + 6) → F) → Bool)

/-- **The consistency of two players' data** that the five steps read: equal roles have equal
data, and an isolated player `v`'s `g_v` is an oracle's. -/
structure Consistent (rp rq : Role) (Hp Hq : HPolys P F) : Prop where
  same : rp = rq → Hp = Hq
  orc : ∀ v, rp = .oracle → roleIdx rq = some v → Hq.g v = Hp.g v

end MIPRE.AnswerReduction

end


