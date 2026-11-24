-- Prove2me | Definitions.Def_Sensitivity214439_Phase0_Solutions_RankedBooleanConstruction
-- name    : Sensitivity214439_Phase0_Solutions_RankedBooleanConstruction
-- status  : Definition
-- author  : @yousofy
-- created : 2026-11-24T12:36:17.382215+00:00
-- url     : https://prove2.me/theorems/e5d8d469-333c-4ef7-b726-3fdb6908fe69
-- title:
--   Colored nested Boolean families and strict uniqueness
-- statement:
--   A colored ranked Boolean family is a predicate
--   $$
--   F:\mathrm{Color}\times\{0,\ldots,L-1\}\times\{0,1\}^{I}\longrightarrow\mathrm{Prop}.
--   $$
--   Uncolored acceptance means that some color accepts. Nesting means $F_c(j,x)\Rightarrow F_c(i,x)$ whenever $i\le j$. Strict uniqueness above core $k$ means that any two accepted colors at any ranks at least $k$ must be equal.
--
--   Passing a natural cutoff $a$ means accepting the finite rank equal to $a$. Cutoffs at least $L$ are therefore never passed, allowing a disabled hard cutoff to be represented by $L$.
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; task source lean/Solutions/RankedBooleanConstruction.lean lines 21–47; SHA256 78b3efc3296738360806709df16f0fc12a1a67ea886978d3e6d4cf057917c6a2; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset

namespace SensitivityRankedConstruction
end SensitivityRankedConstruction



/-!
# Ranked Boolean row families and concrete socket gates

The source checkpoint uses twelve nested levels and a row identity attached to
each accepting child. The definitions below retain that identity; in particular
paired targets require a common child identity. An input coordinate is an
actual Boolean bit, and every socket contains an independent copy of the child.

The structural gate lemmas establish zero-input and canonical-block properties.
They do not assert the checkpoint's quantitative sensitivity upper bounds.
-/

namespace SensitivityRankedConstruction

noncomputable section
open scoped Classical

abbrev RowFamily (I Color : Type) (L : ℕ) :=
  Color → Fin L → (I → Bool) → Prop

def accepts {I Color : Type} {L : ℕ} (row : RowFamily I Color L)
    (j : Fin L) (x : I → Bool) : Prop := ∃ c, row c j x

def Nested {I Color : Type} {L : ℕ} (row : RowFamily I Color L) : Prop :=
  ∀ c (i j : Fin L) x, i ≤ j → row c j x → row c i x

def StrictUnique {I Color : Type} {L : ℕ}
    (row : RowFamily I Color L) (core : ℕ) : Prop :=
  ∀ c d (i j : Fin L) x, core ≤ i.val → core ≤ j.val →
    row c i x → row d j x → c = d







/-- Natural cutoffs include `L`, which means that the child never passes.
This represents the disabled hard cutoff in the source certificates. -/
def passes {I Color : Type} {L : ℕ} (row : RowFamily I Color L)
    (cutoff : ℕ) (x : I → Bool) : Prop :=
  ∃ j : Fin L, j.val = cutoff ∧ accepts row j x





















end
end SensitivityRankedConstruction


