-- Prove2me | Definitions.Def_MIPRE_Background_LIDT_PresentationEmbed
-- name    : MIPRE_Background_LIDT_PresentationEmbed
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T00:57:21.975228+00:00
-- url     : https://prove2.me/theorems/4953da0b-afc8-44d6-8244-b06be02af92c
-- title:
--   Definitions of PresentationEmbed: The presentation's output is a function of its question Piece AR-5b of `planning/answer-reduction.md` needs the…
-- statement:
--   The definitions of the module `MIPRE.Background.LIDT.PresentationEmbed` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The presentation's output is a function of its question. Piece AR-5b of `planning/answer-reduction.md` needs the converse of `Regs.questionOf_eval`: the vector a type's presentation outputs is supported on the copy's own registers, and is a fixed function (`Regs.embedQ`) of the seeded question it computes (`Regs.pres_eval`). So a strategy that answers a question vector of the answer-reduced verifier answers, through `embedQ`, the seeded low-degree test's question, and the two games' questions correspond one to one.
--
--   **Definitions** (4): `MIPRE.LIDT.CL.Question.ty` (The type of a question.); `MIPRE.LIDT.CL.Regs.embedQ` (**The vector a question is presented as**: the point written in the point register, the seed decoded by the permutation in the seed…); `MIPRE.LIDT.CL.Sample.equiv` (A sample is its two types, point, seed and direction.); `MIPRE.LIDT.CL.Sample.retype` (A sample with its two types replaced.).
--
--   **Embedded lemmas** (2): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `question_retype`, `question_ty`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Background.LIDT.PresentationEmbed` (`MIPRE/Background/LIDT/PresentationEmbed.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 11 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/LIDT/PresentationEmbed.lean

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/PresentationEmbed.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Pi
import Mathlib.Tactic.DeriveFintype
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Background_LIDT_Game
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Canonical
import Definitions.Def_MIPRE_Background_LIDT_CLGame
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Background_LIDT_Presentation
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_LowDegree_LineRestrict
import Definitions.Def_MIPRE_Background_LIDT_CLHonest

/-!
# The presentation's output is a function of its question

Piece AR-5b of `planning/answer-reduction.md` needs the converse of `Regs.questionOf_eval`: the
vector a type's presentation outputs is supported on the copy's own registers, and is a fixed
function (`Regs.embedQ`) of the seeded question it computes (`Regs.pres_eval`). So a strategy
that answers a question vector of the answer-reduced verifier answers, through `embedQ`, the
seeded low-degree test's question, and the two games' questions correspond one to one.
-/

noncomputable section

namespace MIPRE.LIDT.CL

/-- The type of a question. -/
def Question.ty {F : Type*} {n : ℕ} : Question F n → Ty
  | .point _ => .point
  | .aline _ _ => .aline
  | .dline _ _ _ => .dline

@[simp] theorem Sample.question_ty {F : Type*} [Field F] [Fintype F] [DecidableEq F] {n : ℕ}
    [NeZero n] (hn : n ∣ Fintype.card F) (sm : Sample F n) (t : Ty) :
    (sm.question hn t).ty = t := by
  cases t <;> rfl

namespace Regs

open Finset MIPRE.CL

variable {ι : Type*} [DecidableEq ι] [Fintype ι] {n : ℕ} (R : Regs ι n)
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [NeZero n] {hn : n ∣ Fintype.card F}
  (S : Sel F n hn)

/-- **The vector a question is presented as**: the point written in the point register, the
seed decoded by the permutation in the seed register, the direction in the direction register. -/
def embedQ : Question F n → (ι → F)
  | .point u => R.putPt u
  | .aline u₀ s => Pi.single R.coord (S.π.symm s) + R.putPt u₀
  | .dline u₀ s v => Pi.single R.coord (S.π.symm s) + R.putDir v + R.putPt u₀

end Regs

/-! ## Two types on one sample -/

/-- A sample with its two types replaced. -/
def Sample.retype {F : Type*} {n : ℕ} (sm : Sample F n) (a b : Ty) : Sample F n :=
  ⟨a, b, sm.u, sm.s, sm.v⟩

/-- A question depends on the sample's point, seed and direction, not on its types. -/
@[simp] theorem Sample.question_retype {F : Type*} [Field F] [Fintype F] [DecidableEq F] {n : ℕ}
    [NeZero n] (hn : n ∣ Fintype.card F) (sm : Sample F n) (a b t : Ty) :
    (sm.retype a b).question hn t = sm.question hn t := by
  cases t <;> rfl

/-- A sample is its two types, point, seed and direction. -/
def Sample.equiv (F : Type*) (n : ℕ) : Sample F n ≃ Ty × Ty × Point F n × F × Point F n where
  toFun sm := (sm.tyA, sm.tyB, sm.u, sm.s, sm.v)
  invFun p := ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

namespace Regs

variable {ι : Type*} [DecidableEq ι] [Fintype ι] {n : ℕ} (R : Regs ι n)
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [NeZero n] {hn : n ∣ Fintype.card F}
  (S : Sel F n hn)

end MIPRE.LIDT.CL.Regs

end


