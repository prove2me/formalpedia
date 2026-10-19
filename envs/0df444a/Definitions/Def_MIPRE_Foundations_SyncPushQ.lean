-- Prove2me | Definitions.Def_MIPRE_Foundations_SyncPushQ
-- name    : MIPRE_Foundations_SyncPushQ
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T00:56:27.696984+00:00
-- url     : https://prove2.me/theorems/43880e2b-ba08-4c66-8a24-eac9f23ea820
-- title:
--   Definitions of SyncPushQ: Playing a synchronous strategy through a reading of the questions The honest strategy of a compiled game often measures…
-- statement:
--   The definitions of the module `MIPRE.Foundations.SyncPushQ` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Playing a synchronous strategy through a reading of the questions. The honest strategy of a compiled game often measures an old strategy at a question computed from the new one, and post-processes the outcome with a map that may depend on the new question. For answer reduction (AR-4 of `planning/answer-reduction.md`) the old game is the oracularized one: each player measures at the oracularized question its seed's oracle half determines, and answers the low-degree encoding of the outcome that its PCP question asks for. `SyncStrategy.pushQ` is that strategy: at a new question `x'`, the…
--
--   **Definitions** (2): `MIPRE.SyncStrategy.pushQ` (**The strategy read through `g` and `f`**, on another synchronous game.); `MIPRE.SyncStrategy.pushQMeas` (The measurement played at `x'`: the old measurement at `g x'`, its outcomes pushed forward along `f x'`.).
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.SyncPushQ` (`MIPRE/Foundations/SyncPushQ.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 5 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/SyncPushQ.lean; blueprint lem:ar-completeness

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/SyncPushQ.lean (definition bundle: declarations the uploaded statements rest on);
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

/-!
# Playing a synchronous strategy through a reading of the questions

The honest strategy of a compiled game often measures an old strategy at a question computed from
the new one, and post-processes the outcome with a map that may depend on the new question. For
answer reduction (AR-4 of `planning/answer-reduction.md`) the old game is the oracularized one:
each player measures at the oracularized question its seed's oracle half determines, and answers
the low-degree encoding of the outcome that its PCP question asks for.

`SyncStrategy.pushQ` is that strategy: at a new question `x'`, the operator for `a'` is the sum
of the old operators at `g x'` over the outcomes `f x'` sends to `a'`. It is projective because
distinct old outcomes are orthogonal.

* `isPCC_pushQ` — it is PCC when the old one is, provided every new pair of positive weight is
  read as an old pair of positive weight.
* `value_pushQ_eq_one` — it has value `1` when the old strategy's operators for a rejected pair
  at a pair of positive weight multiply to zero, and every old pair accepted there (with both
  old answers accepted against themselves wherever that pair is asked) is read as an accepted
  new pair.

This generalizes `SyncStrategy.pushTo` of `MIPRE/Foundations/OracularTyped` (the case of the
identity reading and an answer map independent of the question), but proves value `1` rather
than monotonicity, which is what a question-dependent answer map allows.
-/

namespace MIPRE

open Finset

namespace SyncStrategy

variable {X A : Type*} [Fintype X] [Fintype A] [DecidableEq A] {G : SynchronousGame X A}

/-- The measurement played at `x'`: the old measurement at `g x'`, its outcomes pushed forward
along `f x'`. -/
noncomputable def pushQMeas (S : SyncStrategy G) {X' A' : Type*} [Fintype A'] [DecidableEq A']
    (g : X' → X) (f : X' → A → A') :
    ProjectiveMeasurement X' A' (Matrix (Fin S.d) (Fin S.d) ℂ) where
  M x' a' := ∑ u ∈ univ.filter fun u => f x' u = a', S.P.M (g x') u
  selfAdjoint x' a' := by
    rw [star_sum]
    exact Finset.sum_congr rfl fun u _ => S.P.selfAdjoint (g x') u
  projective x' a' := by
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun u hu => ?_
    refine Finset.sum_eq_single_of_mem u hu ?_ |>.trans (S.P.projective (g x') u)
    intro v _ hvu
    exact S.orthogonal (g x') (Ne.symm hvu)
  normalized x' := by
    rw [Finset.sum_fiberwise_of_maps_to (fun u _ => mem_univ (f x' u))]
    exact S.P.normalized (g x')

/-- **The strategy read through `g` and `f`**, on another synchronous game. -/
noncomputable def pushQ (S : SyncStrategy G) {X' A' : Type*} [Fintype X'] [Fintype A']
    [DecidableEq A'] (G' : SynchronousGame X' A') (g : X' → X) (f : X' → A → A') :
    SyncStrategy G' :=
  ⟨S.d, S.d_pos, S.pushQMeas g f⟩

end SyncStrategy

end MIPRE


