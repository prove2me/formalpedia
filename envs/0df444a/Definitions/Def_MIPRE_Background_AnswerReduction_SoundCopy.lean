-- Prove2me | Definitions.Def_MIPRE_Background_AnswerReduction_SoundCopy
-- name    : MIPRE_Background_AnswerReduction_SoundCopy
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T00:59:32.067993+00:00
-- url     : https://prove2.me/theorems/da7d66c2-6c2a-4cd5-9bfe-dd646523d88c
-- title:
--   Definitions of SoundCopy: Soundness of answer reduction: the low-degree test inside the predicate Piece AR-5b of `planning/answer-reduction.md`…
-- statement:
--   The definitions of the module `MIPRE.Background.AnswerReduction.SoundCopy` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Soundness of answer reduction: the low-degree test inside the predicate. Piece AR-5b of `planning/answer-reduction.md` (`claim:ar-3`, `claim:ar-4`): on the nine type pairs of one copy of the low-degree test, at a role pair where the answer-reduced predicate runs that copy's test, acceptance of the predicate implies acceptance of the seeded CL test on the questions the copy's presentation computes (`cl_accepts_of_accepts`, `cl_accepts_of_accepts6`). The copies tested are copy `v` for the isolated player `v` (step 3), copies `3`, `4`, `5` and the sixth for two oracles (step 4); an oracle's…
--
--   **Definitions** (1): `MIPRE.AnswerReduction.LDStep` (The role pairs and copies at which the predicate runs a copy's low-degree test: copy `v` for the isolated player `v`, copies `3`, `4`, `5`…).
--
--   **Formalization Note** The bundle is the module `MIPRE.Background.AnswerReduction.SoundCopy` (`MIPRE/Background/AnswerReduction/SoundCopy.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 33 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/AnswerReduction/SoundCopy.lean

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/AnswerReduction/SoundCopy.lean (definition bundle: declarations the uploaded statements rest on);
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
import Definitions.Def_MIPRE_Background_AnswerReduction_Honest
import Definitions.Def_MIPRE_Background_LIDT_PresentationEmbed

/-!
# Soundness of answer reduction: the low-degree test inside the predicate

Piece AR-5b of `planning/answer-reduction.md` (`claim:ar-3`, `claim:ar-4`): on the nine type
pairs of one copy of the low-degree test, at a role pair where the answer-reduced predicate runs
that copy's test, acceptance of the predicate implies acceptance of the seeded CL test on the
questions the copy's presentation computes (`cl_accepts_of_accepts`, `cl_accepts_of_accepts6`).
The copies tested are copy `v` for the isolated player `v` (step 3), copies `3`, `4`, `5` and the
sixth for two oracles (step 4); an oracle's copies `1` and `2` are tested only through the
isolated players.

The CL test's equality subtest on equal types is the predicate's step 1, its format check is the
preamble, and its point-against-line subtests are steps 3 and 4, in either order of the players
(`CL.accepts_comm`).
-/

noncomputable section

namespace MIPRE.LIDT.CL

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m d ldc : ℕ} [NeZero m]
  (hm : m ∣ Fintype.card F)

end MIPRE.LIDT.CL

namespace MIPRE.AnswerReduction

open Finset MIPRE.LIDT MIPRE.LIDT.CL SAT Pcp

variable {P : PcpParams} {F : Type*} [Field F] [Fintype F] [DecidableEq F] [NeZero P.m]
  {hm : P.m ∣ Fintype.card F} {hm' : P.m' ∣ Fintype.card F} (S : Sel F P.m hm)
  (S' : Sel F P.m' hm') {X : Type*} (check : X → (Fin P.m' → F) → (Fin (P.m' + 6) → F) → Bool)

/-- The role pairs and copies at which the predicate runs a copy's low-degree test: copy `v` for
the isolated player `v`, copies `3`, `4`, `5` for two oracles. -/
def LDStep (r : Role) (i : Fin 5) : Prop := roleIdx r = some i ∨ (r = .oracle ∧ 2 ≤ (i : ℕ))

end MIPRE.AnswerReduction

end


