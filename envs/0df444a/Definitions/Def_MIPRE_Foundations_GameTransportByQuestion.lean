-- Prove2me | Definitions.Def_MIPRE_Foundations_GameTransportByQuestion
-- name    : MIPRE_Foundations_GameTransportByQuestion
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T00:55:33.37801+00:00
-- url     : https://prove2.me/theorems/44fad5c3-95cc-4cb8-a0b5-fff5ecc3c626
-- title:
--   Definitions of GameTransportByQuestion: Merging strategy answers separately at each question Deterministic answer decoding can depend on the question
-- statement:
--   The definitions of the module `MIPRE.Foundations.GameTransportByQuestion` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Merging strategy answers separately at each question. Deterministic answer decoding can depend on the question. Merging the fibers of these maps preserves projectivity, register dimensions and the shared state. Acceptance implication gives monotonicity of the resulting value.
--
--   **Definitions** (4): `MIPRE.ProjectiveMeasurement.mergeByQuestion` (Merge each question's effects along its own answer map.); `MIPRE.TensorProductStrategy.MergeByQuestionPAEq` (Exact equality of an Alice effect under a same-alphabet answer merge.); `MIPRE.TensorProductStrategy.MergeByQuestionPBEq` (Exact equality of a Bob effect under a same-alphabet answer merge.); `MIPRE.TensorProductStrategy.mergeAnswersByQuestion` (Decode answers by a question-dependent function, preserving registers and state.).
--
--   **Embedded lemmas** (2): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `mergeByQuestion_M`, `copy_d`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.GameTransportByQuestion` (`MIPRE/Foundations/GameTransportByQuestion.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 5 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/GameTransportByQuestion.lean

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/GameTransportByQuestion.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.ENat.Lattice
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Foundations_Closeness
import Definitions.Def_MIPRE_Foundations_PerfectStrategy
import Definitions.Def_MIPRE_Foundations_GameTransport

/-! # Merging strategy answers separately at each question

Deterministic answer decoding can depend on the question. Merging the fibers
of these maps preserves projectivity, register dimensions and the shared
state. Acceptance implication gives monotonicity of the resulting value.
-/

noncomputable section
namespace MIPRE
open Matrix Kronecker Finset Classical

namespace ProjectiveMeasurement
variable {X A A' H : Type*} [Fintype A] [Fintype A'] [DecidableEq A]
  [Fintype H] [DecidableEq H]

/-- Merge each question's effects along its own answer map. -/
def mergeByQuestion (P : ProjectiveMeasurement X A' (Matrix H H ℂ)) (r : X → A' → A) :
    ProjectiveMeasurement X A (Matrix H H ℂ) where
  M x a := (P.merge (r x)).M x a
  selfAdjoint x a := (P.merge (r x)).selfAdjoint x a
  projective x a := (P.merge (r x)).projective x a
  normalized x := (P.merge (r x)).normalized x

/-- A merged effect is the sum over the decoding fiber at that question. -/
@[simp] theorem mergeByQuestion_M
    (P : ProjectiveMeasurement X A' (Matrix H H ℂ)) (r : X → A' → A) (x : X) (a : A) :
    (P.mergeByQuestion r).M x a = ∑ a' ∈ univ.filter (fun a' => r x a' = a), P.M x a' := rfl

end ProjectiveMeasurement

namespace TensorProductStrategy
variable {X Y A B A' B' : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
  [Fintype A'] [Fintype B'] [DecidableEq A] [DecidableEq B]

/-- Decode answers by a question-dependent function, preserving registers and state. -/
def mergeAnswersByQuestion {G' : Game X Y A' B'} (S' : TensorProductStrategy G')
    (G : Game X Y A B) (rA : X → A' → A) (rB : Y → B' → B) : TensorProductStrategy G :=
  ⟨S'.dA, S'.dB, S'.ψ, S'.ψ_unit, S'.PA.mergeByQuestion rA, S'.PB.mergeByQuestion rB⟩

/-- Exact equality of an Alice effect under a same-alphabet answer merge. -/
def MergeByQuestionPAEq {G' : Game X Y A B} (S' : TensorProductStrategy G')
    (G : Game X Y A B) (rA : X → A → A) (rB : Y → B → B) (x : X) (a : A) : Prop :=
  (S'.mergeAnswersByQuestion G rA rB).PA.M x a = S'.PA.M x a

/-- Exact equality of a Bob effect under a same-alphabet answer merge. -/
def MergeByQuestionPBEq {G' : Game X Y A B} (S' : TensorProductStrategy G')
    (G : Game X Y A B) (rA : X → A → A) (rB : Y → B → B) (y : Y) (b : B) : Prop :=
  (S'.mergeAnswersByQuestion G rA rB).PB.M y b = S'.PB.M y b

end TensorProductStrategy

namespace SyncStrategy
variable {X A : Type*} [Fintype X] [Fintype A] [DecidableEq A]
  {G : SynchronousGame X A}

/-- Copying a synchronous strategy keeps its dimension. -/
@[simp] theorem copy_d (S : SyncStrategy G) (G' : SynchronousGame X A) :
    (S.copy G').d = S.d := rfl
end SyncStrategy
end MIPRE


