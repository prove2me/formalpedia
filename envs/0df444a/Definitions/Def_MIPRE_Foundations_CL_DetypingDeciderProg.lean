-- Prove2me | Definitions.Def_MIPRE_Foundations_CL_DetypingDeciderProg
-- name    : MIPRE_Foundations_CL_DetypingDeciderProg
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T02:26:08.422906+00:00
-- url     : https://prove2.me/theorems/b9e1e330-21b0-4b96-85df-59248310e633
-- title:
--   Definitions of DetypingDeciderProg: Executable detyping of the decision predicate The compiler first queries the supplied typed sampler for its dimension,…
-- statement:
--   The definitions of the module `MIPRE.Foundations.CL.DetypingDeciderProg` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Executable detyping of the decision predicate. The compiler first queries the supplied typed sampler for its dimension, then runs the supplied cutoff routine, and finally applies the graph router. Both the original answers and the original index are retained. The cutoff routine is an actual program: its bounds need not be polynomial in the binary index.
--
--   **Definitions** (12): `MIPRE.CL.Detyping.CutoffProgram` (An executable pair of answer bounds.); `MIPRE.CL.Detyping.DeciderProgram.cutoffRoute`; `MIPRE.CL.Detyping.DeciderProgram.cutoffStage`; `MIPRE.CL.Detyping.DeciderProgram.decider` (A genuine ambient decider, built from executable source programs.); `MIPRE.CL.Detyping.DeciderProgram.decisionStage`; `MIPRE.CL.Detyping.DeciderProgram.dimensionRoute`; `MIPRE.CL.Detyping.DeciderProgram.dimensionStage`; `MIPRE.CL.Detyping.DeciderProgram.pairPost`; `MIPRE.CL.Detyping.DeciderProgram.prog`; `MIPRE.CL.Detyping.TypedDecider` (A typed decider uses the source's seven-field input convention.); `MIPRE.CL.Detyping.TypedDecider.Accepts`; `MIPRE.CL.Detyping.TypedDecider.Total`.
--
--   **Embedded lemmas** (4): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `cutoffStage_closed`, `decisionStage_closed`, `dimensionStage_closed`, `prog_closed`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.CL.DetypingDeciderProg` (`MIPRE/Foundations/CL/DetypingDeciderProg.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 44 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/CL/DetypingDeciderProg.lean; blueprint def:typed-normal-interface, lem:detype-executable-decider

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/CL/DetypingDeciderProg.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Finset.Image
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Basic
import Mathlib.Data.List.OfFn
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Pi
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_SAT_Circuit
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_CL_Closure
import Definitions.Def_MIPRE_Foundations_CL_Closure_B
import Definitions.Def_MIPRE_Foundations_CL_Sampler
import Definitions.Def_MIPRE_Foundations_Verifier
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Fold
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
import Definitions.Def_MIPRE_Foundations_GameTransport
import Definitions.Def_MIPRE_Foundations_GameAdapt
import Definitions.Def_MIPRE_Foundations_CL_Embedding
import Definitions.Def_MIPRE_Foundations_CL_Graph
import Definitions.Def_MIPRE_Foundations_CL_Detyping
import Definitions.Def_MIPRE_Foundations_CL_DetypingLaw
import Definitions.Def_MIPRE_Foundations_SampledGame
import Definitions.Def_MIPRE_Foundations_CL_DetypingGame
import Definitions.Def_MIPRE_Foundations_CL_TypedSampler
import Definitions.Def_MIPRE_Foundations_Cost_Binary
import Definitions.Def_MIPRE_Foundations_SAT_Formula
import Definitions.Def_MIPRE_Foundations_SAT_FmlLib
import Definitions.Def_MIPRE_Foundations_SAT_Flatten
import Definitions.Def_MIPRE_Foundations_Cost_Reader
import Definitions.Def_MIPRE_Foundations_SAT_FmlProg
import Definitions.Def_MIPRE_Foundations_SAT_ArrayProg
import Definitions.Def_MIPRE_Foundations_Cost_BinaryArithmetic
import Definitions.Def_MIPRE_Foundations_Cost_BinaryCompare
import Definitions.Def_MIPRE_Foundations_Cost_TreeBits
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgFinite
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgParse
import Definitions.Def_MIPRE_Foundations_CL_DetypingQueries
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgBits
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgCall
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgRoute
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgQueries
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgSampler
import Definitions.Def_MIPRE_Foundations_CL_DetypingDeciderRoute
import Theorems.Thm_MIPRE_Cost_Prog_routeOneCall_closed

/-! # Executable detyping of the decision predicate

The compiler first queries the supplied typed sampler for its dimension, then
runs the supplied cutoff routine, and finally applies the graph router. Both
the original answers and the original index are retained. The cutoff routine
is an actual program: its bounds need not be polynomial in the binary index.
-/

noncomputable section

namespace MIPRE.CL.Detyping

set_option linter.unusedSectionVars false

open Cost Cost.PolyTimeFun Program

/-- A typed decider uses the source's seven-field input convention. -/
structure TypedDecider (T : Type*) [SizedEncoding T] where
  prog : Prog
  closed : prog.WellScoped 1

namespace TypedDecider

def Accepts {T : Type*} [SizedEncoding T] (D : TypedDecider T)
    (n : ℕ) (u : T) (x : BitStr) (v : T) (y a b : BitStr) : Prop :=
  ∃ time, D.prog.Runs (encode (n, u, x, v, y, a, b)) (encode true) time

def Total {T : Type*} [SizedEncoding T] (D : TypedDecider T) : Prop :=
  ∀ (n : ℕ) (d : Data), Halts D.prog (.cons (encode n) d)

end TypedDecider

/-- An executable pair of answer bounds. The inner bound is the source typed
game's cutoff for its entire answer; the outer bound applies even on nonedge views. -/
structure CutoffProgram where
  inner : ℕ → ℕ
  outer : ℕ → ℕ
  prog : Prog
  closed : prog.WellScoped 1
  runs : ∀ n, ∃ time, prog.Runs (encode n) (encode (inner n, outer n)) time

namespace DeciderProgram

variable {T : Type*} [Fintype T] [DecidableEq T] [SizedEncoding T]
variable {ℓ : ℕ} (E : T → T → Prop) [DecidableRel E]
variable (S : TypedSampler ℓ T) (D : TypedDecider T) (C : CutoffProgram)

def pairPost : PolyTimeFun (Data × Data) Data := treePair

def dimensionRoute : PolyTimeFun Data (Bool × Data) :=
  (const true).pair (ap₂ treePair
    (ap₂ treePair (encoded.comp (readNat.comp treeHead)) (const Data.nil)) (PolyTimeFun.id Data))

def cutoffRoute : PolyTimeFun Data (Bool × Data) :=
  (const true).pair (ap₂ treePair
    (encoded.comp (readNat.comp (treeHead.comp treeHead))) (PolyTimeFun.id Data))

def dimensionStage : Prog := Prog.routeOneCall dimensionRoute S.prog pairPost
def cutoffStage : Prog := Prog.routeOneCall cutoffRoute C.prog pairPost
def decisionStage : Prog := Prog.routeOneCall (route E) D.prog post

theorem dimensionStage_closed : (dimensionStage S).WellScoped 1 :=
  Prog.routeOneCall_closed _ S.closed _
theorem cutoffStage_closed : (cutoffStage C).WellScoped 1 :=
  Prog.routeOneCall_closed _ C.closed _
theorem decisionStage_closed : (decisionStage E D).WellScoped 1 :=
  Prog.routeOneCall_closed _ D.closed _

def prog : Prog := .let_ (dimensionStage S) (.let_ (cutoffStage C) (decisionStage E D))

theorem prog_closed : (prog E S D C).WellScoped 1 :=
  ⟨dimensionStage_closed S, (cutoffStage_closed C).mono (by omega) _,
    (decisionStage_closed E D).mono (by omega) _⟩

/-- A genuine ambient decider, built from executable source programs. -/
def decider : MIPRE.Decider where
  prog := prog E S D C
  closed := prog_closed E S D C

end DeciderProgram
end MIPRE.CL.Detyping


