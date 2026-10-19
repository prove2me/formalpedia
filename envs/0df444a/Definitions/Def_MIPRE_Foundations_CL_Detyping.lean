-- Prove2me | Definitions.Def_MIPRE_Foundations_CL_Detyping
-- name    : MIPRE_Foundations_CL_Detyping
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-16T23:09:48.499828+00:00
-- url     : https://prove2.me/theorems/a207bbfa-0baf-4014-a209-547ffe6df17a
-- title:
--   Definitions of Detyping: Detyped conditionally linear functions The construction of `types.tex`, `def:detyped-CL`: run the graph sampler, then…
-- statement:
--   The definitions of the module `MIPRE.Foundations.CL.Detyping` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Detyped conditionally linear functions. The construction of `types.tex`, `def:detyped-CL`: run the graph sampler, then the selected typed presentation on an independent register. An invalid graph view selects a zero presentation that still consumes the whole content register. The conditional law retains the common content seed of both players. This file constructs the presentations and proves their law. The ambient program and its runtime are the separate `lem:detype-sampler` obligation.
--
--   **Definitions** (5): `MIPRE.CL.CLFun.zeroOn` (A zero presentation whose first factor consumes `S`, with empty later factors.); `MIPRE.CL.Detyping.Coord` (The graph register followed by the content register.); `MIPRE.CL.Detyping.presentation` (The detyped presentation has the two graph levels followed by the typed levels.); `MIPRE.CL.Detyping.select` (A graph view selects its decoded vertex exactly when its opposite neighbor bit is one.); `MIPRE.CL.Detyping.selected` (The selected content presentation, with a register-consuming zero fallback.).
--
--   **Embedded lemmas** (2): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `eval_truncate_zeroOn`, `eval_zeroOn`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.CL.Detyping` (`MIPRE/Foundations/CL/Detyping.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 6 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/CL/Detyping.lean; blueprint lem:detype-cl, lem:detype-queries

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/CL/Detyping.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Image
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Pi
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_CL_Closure
import Definitions.Def_MIPRE_Foundations_CL_Closure_B
import Definitions.Def_MIPRE_Foundations_CL_Embedding
import Definitions.Def_MIPRE_Foundations_CL_Graph

/-! # Detyped conditionally linear functions

The construction of `types.tex`, `def:detyped-CL`: run the graph sampler,
then the selected typed presentation on an independent register. An invalid
graph view selects a zero presentation that still consumes the whole content
register. The conditional law retains the common content seed of both players.

This file constructs the presentations and proves their law. The ambient
program and its runtime are the separate `lem:detype-sampler` obligation.
-/

noncomputable section

namespace MIPRE.CL

open Finset Classical

set_option linter.unusedSectionVars false

namespace CLFun

variable {F ι : Type*} [Semiring F] [DecidableEq ι]

/-- A zero presentation whose first factor consumes `S`, with empty later factors. -/
def zeroOn (S : Finset ι) : (ℓ : ℕ) → CLFun F ι ℓ
  | 0 => .zero
  | ℓ + 1 => .cons S 0 fun _ => zeroOn ∅ ℓ

/-- Every marginal of the fallback returns zero. -/
theorem eval_truncate_zeroOn [Fintype ι] (S : Finset ι) (ℓ j : ℕ) (x : ι → F) :
    ((zeroOn S ℓ).truncate j).eval x = 0 := by
  induction j generalizing S ℓ x with
  | zero => simp
  | succ j ih =>
    cases ℓ with
    | zero => exact eval_truncate_zero _ _ _
    | succ ℓ => simp [zeroOn, ih]

@[simp] theorem eval_zeroOn [Fintype ι] (S : Finset ι) (ℓ : ℕ) (x : ι → F) :
    (zeroOn S ℓ).eval x = 0 := by
  simpa using eval_truncate_zeroOn S ℓ ℓ x

end CLFun

namespace Detyping

variable {T ι : Type*} [Fintype T] [DecidableEq T] [Fintype ι] [DecidableEq ι]

/-- The graph register followed by the content register. -/
abbrev Coord (T ι : Type*) := Graph.Coord T ⊕ ι

/-- A graph view selects its decoded vertex exactly when its opposite neighbor bit is one.
On graph-sampler outputs this is the paper's nonzero opposite-block test. -/
def select (E : T → T → Prop) [DecidableRel E] (w : Bool)
    (g : Graph.Coord T → ZMod 2) : Option T :=
  match Graph.decode E (fun p => g (w, p)) with
  | some u => if g (!w, (true, u)) = 1 then some u else none
  | none => none

/-- The selected content presentation, with a register-consuming zero fallback. -/
def selected {ℓ : ℕ} (P : T → CLFun (ZMod 2) ι ℓ) (u : Option T) : CLFun (ZMod 2) ι ℓ :=
  match u with
  | some t => P t
  | none => CLFun.zeroOn univ ℓ

/-- The detyped presentation has the two graph levels followed by the typed levels. -/
def presentation {ℓ : ℕ} (E : T → T → Prop) [DecidableRel E] (w : Bool)
    (P : T → CLFun (ZMod 2) ι ℓ) : CLFun (ZMod 2) (Coord T ι) (ℓ + 2) :=
  ((Graph.presentation E w).embed .inl).concat fun x =>
    (selected P (select E w (pull .inl x))).embed .inr

end Detyping
end MIPRE.CL


