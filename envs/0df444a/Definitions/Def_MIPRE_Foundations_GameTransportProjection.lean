-- Prove2me | Definitions.Def_MIPRE_Foundations_GameTransportProjection
-- name    : MIPRE_Foundations_GameTransportProjection
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T00:50:33.057194+00:00
-- url     : https://prove2.me/theorems/c1e525a4-ccb9-48d0-a8ef-8ebc78f567bb
-- title:
--   Definitions of GameTransportProjection: Projections of relabeled tensor-product strategies These equations expose the unchanged registers and state without…
-- statement:
--   The definitions of the module `MIPRE.Foundations.GameTransportProjection` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Projections of relabeled tensor-product strategies. These equations expose the unchanged registers and state without unfolding the game carried by a strategy. Measurement equations expose only the relabeling.
--
--   **Definitions** (2): `MIPRE.TensorProductStrategy.RelabelPAEq` (Literal equality of one relabeled Alice effect with a selected original effect.); `MIPRE.TensorProductStrategy.RelabelPBEq` (Literal equality of one relabeled Bob effect with a selected original effect.).
--
--   **Embedded lemmas** (5): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `relabel_PA_M`, `relabel_PB_M`, `relabel_dA`, `relabel_dB`, `relabel_ψ`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.GameTransportProjection` (`MIPRE/Foundations/GameTransportProjection.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 2 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/GameTransportProjection.lean

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/GameTransportProjection.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.ENat.Lattice
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_GameTransport

/-! # Projections of relabeled tensor-product strategies

These equations expose the unchanged registers and state without unfolding the
game carried by a strategy. Measurement equations expose only the relabeling.
-/

namespace MIPRE.TensorProductStrategy

variable {X Y A B X' Y' A' B' : Type*}
  [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
  [Fintype X'] [Fintype Y'] [Fintype A'] [Fintype B']
  {G : Game X Y A B} (S : TensorProductStrategy G) (G' : Game X' Y' A' B')
  (eX : X' → X) (eY : Y' → Y) (eA : A' ≃ A) (eB : B' ≃ B)

/-- Relabeling preserves Alice's register dimension. -/
@[simp] theorem relabel_dA : (S.relabel G' eX eY eA eB).dA = S.dA := rfl

/-- Relabeling preserves Bob's register dimension. -/
@[simp] theorem relabel_dB : (S.relabel G' eX eY eA eB).dB = S.dB := rfl

/-- Relabeling preserves the literal shared state. -/
@[simp] theorem relabel_ψ : (S.relabel G' eX eY eA eB).ψ = S.ψ := rfl

/-- Alice's relabeled effects are the original effects at relabeled questions and answers. -/
@[simp] theorem relabel_PA_M (x : X') (a : A') :
    (S.relabel G' eX eY eA eB).PA.M x a = S.PA.M (eX x) (eA a) := rfl

/-- Bob's relabeled effects are the original effects at relabeled questions and answers. -/
@[simp] theorem relabel_PB_M (y : Y') (b : B') :
    (S.relabel G' eX eY eA eB).PB.M y b = S.PB.M (eY y) (eB b) := rfl

/-- Literal equality of one relabeled Alice effect with a selected original effect. -/
def RelabelPAEq (x' : X') (a' : A') (x : X) (a : A) : Prop :=
  (S.relabel G' eX eY eA eB).PA.M x' a' = S.PA.M x a

/-- Literal equality of one relabeled Bob effect with a selected original effect. -/
def RelabelPBEq (y' : Y') (b' : B') (y : Y) (b : B) : Prop :=
  (S.relabel G' eX eY eA eB).PB.M y' b' = S.PB.M y b

end MIPRE.TensorProductStrategy


