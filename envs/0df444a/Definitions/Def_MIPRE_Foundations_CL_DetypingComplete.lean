-- Prove2me | Definitions.Def_MIPRE_Foundations_CL_DetypingComplete
-- name    : MIPRE_Foundations_CL_DetypingComplete
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T00:57:30.662181+00:00
-- url     : https://prove2.me/theorems/6ba69ac7-6e38-4cc3-9317-5c68df8a9d37
-- title:
--   Definitions of DetypingComplete: PCC completeness of finite-game detyping The complete strategy uses the input strategy's dimension and one common…
-- statement:
--   The definitions of the module `MIPRE.Foundations.CL.DetypingComplete` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). PCC completeness of finite-game detyping. The complete strategy uses the input strategy's dimension and one common measurement rule for both players. Invalid local graph views select a constant measurement. On jointly valid views, the original strategy is played on the same ordered edge and common content seed.
--
--   **Definitions** (1): `MIPRE.CL.Detyping.complete` (The input measurements on decoded questions, with a deterministic fallback.).
--
--   **Embedded lemmas** (3): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `failAt_zero_of_accepts`, `sample_dist_pos_iff`, `sample_failAt_zero`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.CL.DetypingComplete` (`MIPRE/Foundations/CL/DetypingComplete.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 15 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/CL/DetypingComplete.lean; blueprint lem:detype-game-completeness

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/CL/DetypingComplete.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Finset.Image
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Pi
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_CL_Closure
import Definitions.Def_MIPRE_Foundations_CL_Closure_B
import Definitions.Def_MIPRE_Foundations_GameTransport
import Definitions.Def_MIPRE_Foundations_GameDouble
import Definitions.Def_MIPRE_Foundations_GameAdapt
import Definitions.Def_MIPRE_Foundations_CL_Embedding
import Definitions.Def_MIPRE_Foundations_CL_Graph
import Definitions.Def_MIPRE_Foundations_CL_Detyping
import Definitions.Def_MIPRE_Foundations_CL_DetypingLaw
import Definitions.Def_MIPRE_Foundations_SampledGame
import Definitions.Def_MIPRE_Foundations_CL_DetypingGame
import Definitions.Def_MIPRE_Foundations_CL_DetypingCompleteSupport
import Theorems.Thm_MIPRE_SampledGame_dist_eq_card
import Theorems.Thm_MIPRE_SampledGame_one_sub_value
import Theorems.Thm_MIPRE_TensorProductStrategy_failAt_nonneg
import Theorems.Thm_MIPRE_TensorProductStrategy_sum_born

/-! # PCC completeness of finite-game detyping

The complete strategy uses the input strategy's dimension and one common
measurement rule for both players. Invalid local graph views select a constant
measurement. On jointly valid views, the original strategy is played on the
same ordered edge and common content seed.
-/

noncomputable section

namespace MIPRE.CL.Detyping

open Finset Classical Matrix Kronecker

theorem sample_dist_pos_iff {S X Y : Type*} [Fintype S] [Nonempty S]
    [Fintype X] [Fintype Y] (qA : S → X) (qB : S → Y) (x : X) (y : Y) :
    0 < SampledGame.dist qA qB x y ↔ ∃ s, qA s = x ∧ qB s = y := by
  rw [SampledGame.dist_eq_card, div_pos_iff_of_pos_right (by exact_mod_cast Fintype.card_pos)]
  simp only [Nat.cast_pos, Finset.card_pos, Finset.nonempty_def, Finset.mem_filter,
    Finset.mem_univ, true_and]

theorem sample_failAt_zero {U X Y A B : Type*} [Fintype U] [Nonempty U]
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (qA : U → X) (qB : U → Y) (D : X → Y → A → B → Bool)
    (S : TensorProductStrategy (SampledGame.game qA qB D)) (hS : S.value = 1) (u : U) :
    S.failAt (qA u) (qB u) = 0 := by
  have h := SampledGame.one_sub_value qA qB D S
  rw [hS, sub_self, eq_comm, div_eq_zero_iff] at h
  have hz : (Fintype.card U : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  exact (Finset.sum_eq_zero_iff_of_nonneg (fun v _ => S.failAt_nonneg (qA v) (qB v))).mp
    (h.resolve_right hz) u (Finset.mem_univ u)

theorem failAt_zero_of_accepts {X Y A B : Type*} [Fintype X] [Fintype Y]
    [Fintype A] [Fintype B] {G : Game X Y A B} (S : TensorProductStrategy G)
    (x : X) (y : Y) (h : ∀ a b, G.D x y a b = true) : S.failAt x y = 0 := by
  simp only [TensorProductStrategy.failAt, TensorProductStrategy.succAt, h,
    ↓reduceIte, one_mul, S.sum_born, sub_self]

variable {T ι A : Type*} [Fintype T] [DecidableEq T] [Fintype ι] [DecidableEq ι]
  [Fintype A] [DecidableEq A]

set_option linter.unusedSectionVars false

/-- The input measurements on decoded questions, with a deterministic fallback.
The outer doubling tag is ignored, so both players use literally the same rule. -/
def complete {ℓ : ℕ} (E : T → T → Prop) [DecidableRel E] (hne : (Graph.edges E).Nonempty)
    (P : Bool → T → CLFun (ZMod 2) ι ℓ)
    (D : Question T ι → Question T ι → A → A → Bool)
    (S : SyncStrategy (typedGame E hne P D).doubled) (a₀ : A) :
    SyncStrategy (game E P D).doubled where
  d := S.d
  d_pos := S.d_pos
  P :=
    { M := fun p a => match decodeQuestion E p.2 with
        | some q => S.P.M q a
        | none => if a = a₀ then 1 else 0
      selfAdjoint := fun p a => by
        cases decodeQuestion E p.2
        · split_ifs <;> simp
        · exact S.P.selfAdjoint _ _
      projective := fun p a => by
        cases decodeQuestion E p.2
        · split_ifs <;> simp
        · exact S.P.projective _ _
      normalized := fun p => by
        cases decodeQuestion E p.2
        · simp
        · exact S.P.normalized _ }

end MIPRE.CL.Detyping


