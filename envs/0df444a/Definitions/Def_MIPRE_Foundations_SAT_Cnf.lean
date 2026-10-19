-- Prove2me | Definitions.Def_MIPRE_Foundations_SAT_Cnf
-- name    : MIPRE_Foundations_SAT_Cnf
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-16T23:08:21.59247+00:00
-- url     : https://prove2.me/theorems/fb7b94a9-472e-4750-bf35-432ba735349e
-- title:
--   Definitions of Cnf: 3SAT and decoupled 5SAT formulas Literals, clauses and satisfaction, for the succinct Cook–Levin theorem…
-- statement:
--   The definitions of the module `MIPRE.Foundations.SAT.Cnf` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). 3SAT and decoupled 5SAT formulas. Literals, clauses and satisfaction, for the succinct Cook–Levin theorem (`planning/succinct-cook-levin.md`). A 3SAT formula is a *set* of clauses, each of exactly three literals (a clause of fewer literals repeats one: `x ∨ x ∨ x`), and a decoupled 5SAT formula (`answer_reduction.tex`, "Decoupled 5SAT and its succinct descriptions") is a set of clauses with one literal from each of five blocks of variables, evaluated on five separate assignments. The literal `x^o` of the paper is `⟨x, o⟩`: positive when `o = true`.
--
--   **Definitions** (10): `MIPRE.SAT.Clause3` (A 3SAT clause.); `MIPRE.SAT.Clause3.eval` (The value of a clause.); `MIPRE.SAT.Clause5` (A decoupled 5SAT clause: one literal from each of five blocks.); `MIPRE.SAT.Clause5.eval` (The value of a decoupled clause on five assignments.); `MIPRE.SAT.Cnf3` (A 3SAT formula on the variables `V`: a set of clauses.); `MIPRE.SAT.Cnf3.Sat` (`w` satisfies every clause of `φ`.); `MIPRE.SAT.Cnf5` (A decoupled 5SAT formula.); `MIPRE.SAT.Cnf5.Sat` (The five assignments satisfy every clause of `φ`.); `MIPRE.SAT.Lit` (A literal: a variable and its sign (`pos = true` for `x`, `false` for `¬x`).); `MIPRE.SAT.Lit.eval` (The value of a literal under an assignment.).
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.SAT.Cnf` (`MIPRE/Foundations/SAT/Cnf.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/SAT/Cnf.lean

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/SAT/Cnf.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Data.Set.Basic

/-!
# 3SAT and decoupled 5SAT formulas

Literals, clauses and satisfaction, for the succinct Cook–Levin theorem
(`planning/succinct-cook-levin.md`). A 3SAT formula is a *set* of clauses, each of exactly
three literals (a clause of fewer literals repeats one: `x ∨ x ∨ x`), and a decoupled 5SAT
formula (`answer_reduction.tex`, "Decoupled 5SAT and its succinct descriptions") is a set
of clauses with one literal from each of five blocks of variables, evaluated on five
separate assignments. The literal `x^o` of the paper is `⟨x, o⟩`: positive when `o = true`.
-/

namespace MIPRE.SAT

/-- A literal: a variable and its sign (`pos = true` for `x`, `false` for `¬x`). -/
structure Lit (V : Type*) where
  var : V
  pos : Bool
  deriving DecidableEq

/-- The value of a literal under an assignment. -/
def Lit.eval {V : Type*} (w : V → Bool) (l : Lit V) : Bool := if l.pos then w l.var else !w l.var

/-- A 3SAT clause. -/
structure Clause3 (V : Type*) where
  l₁ : Lit V
  l₂ : Lit V
  l₃ : Lit V
  deriving DecidableEq

/-- The value of a clause. -/
def Clause3.eval {V : Type*} (w : V → Bool) (c : Clause3 V) : Bool :=
  c.l₁.eval w || c.l₂.eval w || c.l₃.eval w

/-- A 3SAT formula on the variables `V`: a set of clauses. -/
abbrev Cnf3 (V : Type*) := Set (Clause3 V)

/-- `w` satisfies every clause of `φ`. -/
def Cnf3.Sat {V : Type*} (φ : Cnf3 V) (w : V → Bool) : Prop := ∀ c ∈ φ, c.eval w = true

/-- A decoupled 5SAT clause: one literal from each of five blocks. -/
structure Clause5 (V₁ V₂ V₃ V₄ V₅ : Type*) where
  l₁ : Lit V₁
  l₂ : Lit V₂
  l₃ : Lit V₃
  l₄ : Lit V₄
  l₅ : Lit V₅

/-- The value of a decoupled clause on five assignments. -/
def Clause5.eval {V₁ V₂ V₃ V₄ V₅ : Type*} (w₁ : V₁ → Bool) (w₂ : V₂ → Bool) (w₃ : V₃ → Bool)
    (w₄ : V₄ → Bool) (w₅ : V₅ → Bool) (c : Clause5 V₁ V₂ V₃ V₄ V₅) : Bool :=
  c.l₁.eval w₁ || c.l₂.eval w₂ || c.l₃.eval w₃ || c.l₄.eval w₄ || c.l₅.eval w₅

/-- A decoupled 5SAT formula. -/
abbrev Cnf5 (V₁ V₂ V₃ V₄ V₅ : Type*) := Set (Clause5 V₁ V₂ V₃ V₄ V₅)

/-- The five assignments satisfy every clause of `φ`. -/
def Cnf5.Sat {V₁ V₂ V₃ V₄ V₅ : Type*} (φ : Cnf5 V₁ V₂ V₃ V₄ V₅) (w₁ : V₁ → Bool)
    (w₂ : V₂ → Bool) (w₃ : V₃ → Bool) (w₄ : V₄ → Bool) (w₅ : V₅ → Bool) : Prop :=
  ∀ c ∈ φ, c.eval w₁ w₂ w₃ w₄ w₅ = true

end MIPRE.SAT


