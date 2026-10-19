-- Prove2me | Definitions.Def_MIPRE_Foundations_CL_Embedding
-- name    : MIPRE_Foundations_CL_Embedding
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-16T23:08:36.23346+00:00
-- url     : https://prove2.me/theorems/c51afac1-a81e-4455-91a8-0243d44317e8
-- title:
--   Definitions of Embedding: Embedding conditionally linear presentations in a larger register Extending a presentation by zero along an injection…
-- statement:
--   The definitions of the module `MIPRE.Foundations.CL.Embedding` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Embedding conditionally linear presentations in a larger register. Extending a presentation by zero along an injection preserves its evaluation, marginal, factor and linear-map queries. This puts the graph and content parts of detyping on disjoint registers without changing their query interfaces.
--
--   **Definitions** (4): `MIPRE.CL.CLFun.embed` (Extend every factor and map of a presentation along a coordinate injection.); `MIPRE.CL.RegLinear.embed` (The same register-linear operation on an embedded register.); `MIPRE.CL.pull` (Read the coordinates in the image of an embedding.); `MIPRE.CL.push` (Extend by zero outside the image of an embedding.).
--
--   **Embedded lemmas** (13): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `embed_apply`, `proj_push`, `pull_add`, `pull_proj`, `pull_push`, `pull_zero`, `push_add`, `push_apply`, `push_inl_left`, `push_inl_right`, ….
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.CL.Embedding` (`MIPRE/Foundations/CL/Embedding.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 2 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/CL/Embedding.lean; blueprint lem:detype-queries

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/CL/Embedding.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Image
import Mathlib.LinearAlgebra.Pi
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Basic

/-! # Embedding conditionally linear presentations in a larger register

Extending a presentation by zero along an injection preserves its evaluation,
marginal, factor and linear-map queries. This puts the graph and content parts
of detyping on disjoint registers without changing their query interfaces.
-/

noncomputable section

namespace MIPRE.CL

open Classical

set_option linter.unusedSectionVars false

variable {F ι κ : Type*} [Semiring F] [DecidableEq ι] [DecidableEq κ]

/-- Read the coordinates in the image of an embedding. -/
def pull (e : ι ↪ κ) (x : κ → F) : ι → F := fun i => x (e i)

/-- Extend by zero outside the image of an embedding. -/
def push (e : ι ↪ κ) (x : ι → F) : κ → F :=
  fun j => if h : ∃ i, e i = j then x h.choose else 0

@[simp] theorem push_apply (e : ι ↪ κ) (x : ι → F) (i : ι) : push e x (e i) = x i := by
  have h : ∃ a, e a = e i := ⟨i, rfl⟩
  rw [push, dif_pos h]
  congr 1
  exact e.injective h.choose_spec

@[simp] theorem pull_push (e : ι ↪ κ) (x : ι → F) : pull e (push e x) = x := by
  funext i
  exact push_apply e x i

@[simp] theorem push_zero (e : ι ↪ κ) : push e (0 : ι → F) = 0 := by
  funext j
  simp [push]

@[simp] theorem push_add (e : ι ↪ κ) (x y : ι → F) :
    push e (x + y) = push e x + push e y := by
  funext j
  simp only [push, Pi.add_apply]
  split_ifs <;> simp

@[simp] theorem pull_add (e : ι ↪ κ) (x y : κ → F) :
    pull e (x + y) = pull e x + pull e y := rfl

@[simp] theorem pull_zero (e : ι ↪ κ) : pull e (0 : κ → F) = 0 := rfl

@[simp] theorem push_inl_left (x : ι → F) (i : ι) :
    push (Function.Embedding.inl (β := κ)) x (Sum.inl i) = x i := push_apply _ _ _

@[simp] theorem push_inr_right (x : κ → F) (j : κ) :
    push (Function.Embedding.inr (α := ι)) x (Sum.inr j) = x j := push_apply _ _ _

@[simp] theorem push_inl_right (x : ι → F) (j : κ) :
    push Function.Embedding.inl x (Sum.inr j) = 0 := by simp [push]

@[simp] theorem push_inr_left (x : κ → F) (i : ι) :
    push Function.Embedding.inr x (Sum.inl i) = 0 := by simp [push]

/-- Restriction of the projection onto an embedded register. -/
theorem pull_proj (e : ι ↪ κ) (S : Finset ι) (x : κ → F) :
    pull e (proj (S.map e) x) = proj S (pull e x) := by
  funext i
  simp [pull]

/-- Projection commutes with extension by zero. -/
theorem proj_push (e : ι ↪ κ) (S : Finset ι) (x : ι → F) :
    proj (S.map e) (push e x) = push e (proj S x) := by
  funext j
  by_cases h : ∃ i, e i = j
  · obtain ⟨i, rfl⟩ := h
    simp
  · have hm : j ∉ S.map e := by
      simpa only [Finset.mem_map, not_exists, not_and] using
        fun i (_ : i ∈ S) => fun hi => h ⟨i, hi⟩
    simp [push, h, hm]

namespace RegLinear

/-- The same register-linear operation on an embedded register. -/
def embed (e : ι ↪ κ) {S : Finset ι} (L : RegLinear F S) : RegLinear F (S.map e) where
  toLinearMap :=
    { toFun := fun x => push e (L (pull e x))
      map_add' := fun x y => by simp
      map_smul' := fun c x => by
        change push e (L (c • pull e x)) = c • push e (L (pull e x))
        rw [map_smul]
        funext j
        simp only [push, Pi.smul_apply]
        split_ifs <;> simp }
  proj_comp_proj' x := by
    change proj (S.map e) (push e (L (pull e (proj (S.map e) x)))) = _
    rw [pull_proj, L.apply_proj, proj_push, L.proj_apply]
    rfl

@[simp] theorem embed_apply (e : ι ↪ κ) {S : Finset ι} (L : RegLinear F S) (x : κ → F) :
    L.embed e x = push e (L (pull e x)) := rfl

end RegLinear

namespace CLFun

variable {ℓ : ℕ}

/-- Extend every factor and map of a presentation along a coordinate injection. -/
def embed (e : ι ↪ κ) : {ℓ : ℕ} → CLFun F ι ℓ → CLFun F κ ℓ
  | _, zero => zero
  | _, cons S L next => cons (S.map e) (L.embed e) fun x => (next (pull e x)).embed e

variable [Fintype ι] [Fintype κ]

end CLFun
end MIPRE.CL


