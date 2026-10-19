-- Prove2me | Definitions.Def_MIPRE_Foundations_CL_Product
-- name    : MIPRE_Foundations_CL_Product
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-16T23:09:41.886528+00:00
-- url     : https://prove2.me/theorems/18d01860-785b-4859-a84d-929ccbed8904
-- title:
--   Definitions of Product: Padding to a given level, and the product of two presentations Two constructions the answer-reduced sampler needs…
-- statement:
--   The definitions of the module `MIPRE.Foundations.CL.Product` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Padding to a given level, and the product of two presentations. Two constructions the answer-reduced sampler needs (`sec:ar-verifier`, `ld_compiler.tex`): its CL functions are the direct sums of the oracularized sampler's, with `ℓ` levels, and the downsized PCP sampler's, with three, on disjoint registers, at the common level `max ℓ 3`. * `CLFun.liftTo T L h P` pads `P` with trivial levels to exactly `L ≥ ℓ` levels (`liftN` pads by a number of levels, and `ℓ + (L - ℓ)` is not `L` by definition, so the level is cast along `castLevel`). Evaluation and exactness are unchanged (`eval_liftTo`,…
--
--   **Definitions** (3): `MIPRE.CL.CLFun.castLevel` (A presentation with `a` levels as one with `b = a` levels.); `MIPRE.CL.CLFun.liftTo` (**Pad to exactly `L` levels**, the extra levels trivial on `V_T`.); `MIPRE.CL.CLFun.prod` (**The product**: `P` on the left coordinates, `Q` on the right.).
--
--   **Embedded lemmas** (13): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `eval_castLevel`, `eval_liftTo`, `eval_truncate_lift`, `eval_truncate_liftN`, `eval_truncate_liftTo`, `factorOfPrefix_castLevel`, `mapOfPrefix_castLevel`, `mapOfPrefix_lift`, `mapOfPrefix_liftN`, `mapOfPrefix_liftTo`, ….
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.CL.Product` (`MIPRE/Foundations/CL/Product.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 5 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/CL/Product.lean; blueprint def:ar-typed-game

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/CL/Product.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Image
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Pi
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_CL_Closure
import Definitions.Def_MIPRE_Foundations_CL_Closure_B
import Definitions.Def_MIPRE_Foundations_CL_Embedding

/-!
# Padding to a given level, and the product of two presentations

Two constructions the answer-reduced sampler needs (`sec:ar-verifier`, `ld_compiler.tex`): its
CL functions are the direct sums of the oracularized sampler's, with `ℓ` levels, and the
downsized PCP sampler's, with three, on disjoint registers, at the common level `max ℓ 3`.

* `CLFun.liftTo T L h P` pads `P` with trivial levels to exactly `L ≥ ℓ` levels (`liftN` pads by
  a number of levels, and `ℓ + (L - ℓ)` is not `L` by definition, so the level is cast along
  `castLevel`). Evaluation and exactness are unchanged (`eval_liftTo`, `ExactlyOn.liftTo`).
* `CLFun.prod P Q` is the presentation on `ι ⊕ κ` running `P` on the left coordinates and `Q` on
  the right: the paper's direct sum on `V₁ ⊕ V₂`, as `directSum` of the two embeddings. It is
  exact on everything when both are (`ExactlyOn.prod`), and evaluates componentwise
  (`eval_prod`).
-/

noncomputable section

namespace MIPRE.CL.CLFun

open Finset

variable {F : Type*} [Semiring F] {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]

/-! ## Casting and padding the level -/

/-- A presentation with `a` levels as one with `b = a` levels. -/
def castLevel {a b : ℕ} (h : a = b) (P : CLFun F ι a) : CLFun F ι b := h ▸ P

@[simp] theorem eval_castLevel [Fintype ι] {a b : ℕ} (h : a = b) (P : CLFun F ι a) (x : ι → F) :
    (P.castLevel h).eval x = P.eval x := by
  subst h; rfl

@[simp] theorem truncate_castLevel {a b : ℕ} (h : a = b) (P : CLFun F ι a) (j : ℕ) :
    (P.castLevel h).truncate j = P.truncate j := by
  subst h; rfl

@[simp] theorem factorOfPrefix_castLevel [Fintype ι] {a b : ℕ} (h : a = b) (P : CLFun F ι a)
    (j : ℕ) (u : ι → F) : (P.castLevel h).factorOfPrefix j u = P.factorOfPrefix j u := by
  subst h; rfl

@[simp] theorem mapOfPrefix_castLevel [Fintype ι] {a b : ℕ} (h : a = b) (P : CLFun F ι a)
    (j : ℕ) (u : ι → F) : (P.castLevel h).mapOfPrefix j u = P.mapOfPrefix j u := by
  subst h; rfl

variable {ℓ : ℕ}

/-- **Pad to exactly `L` levels**, the extra levels trivial on `V_T`. -/
def liftTo (T : Finset ι) (L : ℕ) (h : ℓ ≤ L) (P : CLFun F ι ℓ) : CLFun F ι L :=
  (P.liftN T (L - ℓ)).castLevel (Nat.add_sub_cancel' h)

@[simp] theorem eval_liftTo [Fintype ι] (T : Finset ι) (L : ℕ) (h : ℓ ≤ L) (P : CLFun F ι ℓ)
    (x : ι → F) : (P.liftTo T L h).eval x = P.eval x := by
  simp [liftTo]

/-! ## The product of two presentations -/

/-- **The product**: `P` on the left coordinates, `Q` on the right. -/
def prod (P : CLFun F ι ℓ) (Q : CLFun F κ ℓ) : CLFun F (ι ⊕ κ) ℓ :=
  (P.embed (Function.Embedding.inl)).directSum (Q.embed (Function.Embedding.inr))

/-! ## The queries of a direct sum

A sampler answers marginal, linear-map and factor queries (`truncate`, `mapOfPrefix`,
`factorOfPrefix`). For a direct sum of presentations on disjoint register subspaces each query is
answered componentwise; for a padded presentation, as for the unpadded one. -/

variable [Fintype ι]

theorem sdiff_subset_compl_union {S S' T T' : Finset ι} (hS' : S' ⊆ T')
    (hTT' : Disjoint T T') : T \ S ⊆ (S ∪ S')ᶜ := fun i hi => by
  rw [Finset.mem_sdiff] at hi
  rw [Finset.mem_compl, Finset.mem_union]
  exact fun h => h.elim hi.2 fun h' => Finset.disjoint_left.mp hTT' hi.1 (hS' h')

theorem sdiff_subset_compl {S T : Finset ι} : T \ S ⊆ Sᶜ := fun _ hi =>
  Finset.mem_compl.mpr (Finset.mem_sdiff.mp hi).2

/-! ## The queries of a padded presentation -/

theorem eval_truncate_lift (T : Finset ι) (P : CLFun F ι ℓ) (j : ℕ) (x : ι → F) :
    ((P.lift T).truncate j).eval x = (P.truncate j).eval x := by
  induction j generalizing ℓ P T x with
  | zero => simp
  | succ j ih =>
    cases P with
    | zero => simp [lift, eval_truncate_zero]
    | cons S L next => simp only [lift, truncate_succ_cons, eval_cons, ih]

theorem mapOfPrefix_lift (T : Finset ι) (P : CLFun F ι ℓ) (j : ℕ) (u : ι → F) :
    (P.lift T).mapOfPrefix j u = P.mapOfPrefix j u := by
  induction P generalizing T j u with
  | zero => cases j <;> rfl
  | cons S L next ih =>
    cases j with
    | zero => rfl
    | succ j => exact ih _ _ _ _

theorem eval_truncate_liftN (T : Finset ι) (n : ℕ) (P : CLFun F ι ℓ) (j : ℕ) (x : ι → F) :
    ((P.liftN T n).truncate j).eval x = (P.truncate j).eval x := by
  induction n with
  | zero => rfl
  | succ n ih => rw [liftN, eval_truncate_lift, ih]

theorem mapOfPrefix_liftN (T : Finset ι) (n : ℕ) (P : CLFun F ι ℓ) (j : ℕ) (u : ι → F) :
    (P.liftN T n).mapOfPrefix j u = P.mapOfPrefix j u := by
  induction n with
  | zero => rfl
  | succ n ih => rw [liftN, mapOfPrefix_lift, ih]

@[simp] theorem eval_truncate_liftTo (T : Finset ι) (L : ℕ) (h : ℓ ≤ L) (P : CLFun F ι ℓ) (j : ℕ)
    (x : ι → F) : ((P.liftTo T L h).truncate j).eval x = (P.truncate j).eval x := by
  rw [liftTo, truncate_castLevel, eval_truncate_liftN]

@[simp] theorem mapOfPrefix_liftTo (T : Finset ι) (L : ℕ) (h : ℓ ≤ L) (P : CLFun F ι ℓ) (j : ℕ)
    (u : ι → F) : (P.liftTo T L h).mapOfPrefix j u = P.mapOfPrefix j u := by
  rw [liftTo, mapOfPrefix_castLevel, mapOfPrefix_liftN]

/-! ## The queries of a product -/

variable [Fintype κ]

end MIPRE.CL.CLFun

end


