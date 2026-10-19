-- Prove2me | Definitions.Def_MIPRE_Foundations_SAT_Padding
-- name    : MIPRE_Foundations_SAT_Padding
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-16T23:12:34.297908+00:00
-- url     : https://prove2.me/theorems/a774a2bf-9017-4937-a8a1-5b75fba7a9f0
-- title:
--   Definitions of Padding: Padding decoupled descriptions The semantic content of `prop:exciting-padding-prop` in `answer_reduction.tex`
-- statement:
--   The definitions of the module `MIPRE.Foundations.SAT.Padding` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Padding decoupled descriptions. The semantic content of `prop:exciting-padding-prop` in `answer_reduction.tex`. The original clauses are embedded in the larger five blocks. Additional clauses force both answer tails to be blank tapes; the three auxiliary tails are free. In particular, the conclusion preserves `Circuit.DescribesDecider`, which specifies every answer bit, rather than merely preserving the accepted answer prefixes. The circuit construction and its running time are separate obligations.
--
--   **Definitions** (5): `MIPRE.SAT.Clause5.map` (Rename the variables in each of the five separate blocks.); `MIPRE.SAT.Cnf5.blockInclusion` (The inclusion of an old block into a larger one.); `MIPRE.SAT.Cnf5.extendBlock` (Extend a block arbitrarily by `false`; only the three auxiliary blocks use this.); `MIPRE.SAT.Cnf5.pad` (Embed the original clauses and force the two answer tails to contain blanks.); `_private.MIPRE.Foundations.SAT.Padding.0.MIPRE.SAT.Cnf5.falseLit`.
--
--   **Embedded lemmas** (4): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `eval_map`, `extendBlock_inclusion`, `eval_falseLit`, `lit_true_iff`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.SAT.Padding` (`MIPRE/Foundations/SAT/Padding.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 14 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/SAT/Padding.lean

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/SAT/Padding.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Pi
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_SAT_Circuit
import Definitions.Def_MIPRE_Foundations_SAT_Cnf
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_CL_Closure
import Definitions.Def_MIPRE_Foundations_CL_Closure_B
import Definitions.Def_MIPRE_Foundations_CL_Sampler
import Definitions.Def_MIPRE_Foundations_Verifier
import Definitions.Def_MIPRE_Foundations_SAT_Succinct
import Definitions.Def_MIPRE_Foundations_SAT_Decoupled

/-!
# Padding decoupled descriptions

The semantic content of `prop:exciting-padding-prop` in `answer_reduction.tex`.
The original clauses are embedded in the larger five blocks. Additional clauses
force both answer tails to be blank tapes; the three auxiliary tails are free.
In particular, the conclusion preserves `Circuit.DescribesDecider`, which specifies
every answer bit, rather than merely preserving the accepted answer prefixes.
The circuit construction and its running time are separate obligations.
-/

namespace MIPRE.SAT

namespace Clause5

variable {A B C D E A' B' C' D' E' : Type*}

/-- Rename the variables in each of the five separate blocks. -/
def map (f₁ : A → A') (f₂ : B → B') (f₃ : C → C') (f₄ : D → D') (f₅ : E → E')
    (c : Clause5 A B C D E) : Clause5 A' B' C' D' E' :=
  ⟨⟨f₁ c.l₁.var, c.l₁.pos⟩, ⟨f₂ c.l₂.var, c.l₂.pos⟩,
    ⟨f₃ c.l₃.var, c.l₃.pos⟩, ⟨f₄ c.l₄.var, c.l₄.pos⟩, ⟨f₅ c.l₅.var, c.l₅.pos⟩⟩

@[simp] theorem eval_map (f₁ : A → A') (f₂ : B → B') (f₃ : C → C')
    (f₄ : D → D') (f₅ : E → E') (c : Clause5 A B C D E)
    (w₁ : A' → Bool) (w₂ : B' → Bool) (w₃ : C' → Bool)
    (w₄ : D' → Bool) (w₅ : E' → Bool) :
    (c.map f₁ f₂ f₃ f₄ f₅).eval w₁ w₂ w₃ w₄ w₅ =
      c.eval (w₁ ∘ f₁) (w₂ ∘ f₂) (w₃ ∘ f₃) (w₄ ∘ f₄) (w₅ ∘ f₅) := rfl

end Clause5

namespace Cnf5

/-- The inclusion of an old block into a larger one. -/
def blockInclusion {n m : ℕ} (h : n ≤ m) : Fin (2 ^ n) → Fin (2 ^ m) :=
  Fin.castLE (Nat.pow_le_pow_right (by decide) h)

/-- Extend a block arbitrarily by `false`; only the three auxiliary blocks use this. -/
def extendBlock {n m : ℕ} (w : Fin (2 ^ n) → Bool) : Fin (2 ^ m) → Bool :=
  fun i => if h : (i : ℕ) < 2 ^ n then w ⟨i, h⟩ else false

@[simp] theorem extendBlock_inclusion {n m : ℕ} (h : n ≤ m) (w : Fin (2 ^ n) → Bool) :
    extendBlock (m := m) w ∘ blockInclusion h = w := by
  funext i
  simp [extendBlock, blockInclusion, i.isLt]

/-- Embed the original clauses and force the two answer tails to contain blanks. -/
def pad {ℓ r ℓ' r' : ℕ} (hℓ : ℓ ≤ ℓ') (hr : r ≤ r')
    (φ : Cnf5 (Fin (2 ^ ℓ)) (Fin (2 ^ ℓ))
      (Fin (2 ^ r)) (Fin (2 ^ r)) (Fin (2 ^ r))) :
    Cnf5 (Fin (2 ^ ℓ')) (Fin (2 ^ ℓ')) (Fin (2 ^ r')) (Fin (2 ^ r')) (Fin (2 ^ r')) :=
  (Clause5.map (blockInclusion hℓ) (blockInclusion hℓ)
    (blockInclusion hr) (blockInclusion hr) (blockInclusion hr) '' φ) ∪
  {c | (2 ^ ℓ ≤ (c.l₁.var : ℕ) ∧ c.l₁.pos = decide ((c.l₁.var : ℕ) % 2 = 0)) ∨
    (2 ^ ℓ ≤ (c.l₂.var : ℕ) ∧ c.l₂.pos = decide ((c.l₂.var : ℕ) % 2 = 0))}

def falseLit {n : ℕ} (w : Fin (2 ^ n) → Bool) : Lit (Fin (2 ^ n)) :=
  ⟨0, !(w 0)⟩

theorem eval_falseLit {n : ℕ} (w : Fin (2 ^ n) → Bool) :
    (falseLit w).eval w = false := by
  cases h : w 0 <;> simp [falseLit, Lit.eval, h]

theorem lit_true_iff {A : Type*} (w : A → Bool) (i : A) (o : Bool) :
    (⟨i, o⟩ : Lit A).eval w = true ↔ w i = o := by
  cases o <;> cases hw : w i <;> simp [Lit.eval, hw]

end Cnf5

namespace Circuit

end Circuit

end MIPRE.SAT


