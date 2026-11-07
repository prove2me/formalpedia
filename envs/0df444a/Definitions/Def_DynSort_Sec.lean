-- Prove2me | Definitions.Def_DynSort_Sec
-- name    : DynSort_Sec
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:33:12.485726+00:00
-- url     : https://prove2.me/theorems/8d6ed35e-d31b-4844-8bc9-eac088659a51
-- title:
--   Sections of a Dynamic Sorting Tree and the element type $\mathrm{Elt}$
-- statement:
--   A **Dynamic Sorting Tree** (DST) is a recursively partitioned array. A level-$1$ section is a sorted array of cells. For $i\ge2$ a level-$i$ section consists of either one block, holding an original section $O$, or three blocks
--   $$O_1\;\big|\;T_2\,O_2\;\big|\;O_3,$$
--   a first block with original section $O_1$, a middle block with a transfer section $T_2$ followed by an original section $O_2$, and a last block with original section $O_3$; every child is a level-$(i-1)$ section. Read from left to right, the level-$1$ sections form the underlying array. A cell holds an element or is a **hole**; sizes count cells, the hole included.
--
--   The module also provides the cells of a section from left to right, its size, its stored elements and number of holes, the section at an **address** (the list of child indices from the root: $0$ for the original section of a single block and for $O_1$, $1$ for $T_2$, $2$ for $O_2$, $3$ for $O_3$), the absolute index of a section's first cell, and the removal of an element (leaving a hole).
--
--   Elements are pairs (value, identifier) of $\mathbb R\times\mathbb N$ ordered lexicographically: the paper's infinitesimal perturbation that makes all elements distinct.
--
--   **Formalization Note** The level is not stored in a section; it is an argument of the invariants and operations, and the section at address $a$ of a level-$d$ root has level $d-|a|$. An empty section is a chain of single blocks ending in an empty level-$1$ section.
-- source:
--   Azar, Bhore, Dey, Panigrahi, Vardi, Zhang, Online and Fully-Dynamic Sorting, STOC 2027 submission (manuscript sha256 da7f0d5ef6191ccaa6c70faec62234592c6d108cd2357bda3e5b6dac010acf6c), §4.1, pp.9–10 (PDF pp.11–12), Figures 2–3; §4.2, p.11 (ties)

import Mathlib

namespace DynSort

/-! # Sections of a Dynamic Sorting Tree

Y. Azar, S. Bhore, D. Dey, D. Panigrahi, O. Vardi, I. Zhang, *Online and Fully-Dynamic Sorting*,
STOC 2027 submission (manuscript sha256 da7f0d5e…), §4.1, pp.9–10 (PDF pp.11–12), Figures 2–3.

A level-1 section is a sorted array. For `i ≥ 2` a level-`i` section consists of one block, holding
an original section `O`, or of three blocks `O₁ | T₂ O₂ | O₃`: a first block (original section
`O₁`), a middle block (transfer section `T₂` followed by original section `O₂`) and a last block
(original section `O₃`); every child is a level-`(i − 1)` section. Arranged left to right, the
level-1 sections constitute the underlying array.

**Formalization Note.**
* `Sec α` has the three shapes `leaf cells`, `single O`, `three O₁ T₂ O₂ O₃`; the level is not
  stored but is the argument of the invariants and operations. A cell is `Option α`, `none` being
  the hole. Sizes count cells, the hole included (pp.12, 14).
* An empty section is a chain of `single`s ending in `leaf []`.
* A section inside a root is addressed by the list of child indices from the root: `0` for the
  original section of a single block and for `O₁`, `1` for `T₂`, `2` for `O₂`, `3` for `O₃`. A
  section at address `a` of a level-`d` root has level `d − a.length`.
* Elements are `Elt := ℝ ×ₗ ℕ`, a value and an identifier compared lexicographically: this is the
  paper's "infinitesimal perturbations to break ties" (p.11). `vals` reads the values.
-/

/-- **A section of a DST** (§4.1, p.10): a level-1 sorted array of cells, a single block, or three
blocks `O₁ | T₂ O₂ | O₃`. -/
inductive Sec (α : Type) where
  | leaf (cells : List (Option α))
  | single (O : Sec α)
  | three (O1 T2 O2 O3 : Sec α)
  deriving Repr, DecidableEq

/-- Elements of the A-DST: a real value and an identifier, ordered lexicographically. -/
abbrev Elt := ℝ ×ₗ ℕ

namespace Sec

variable {α : Type}

instance : Inhabited (Sec α) := ⟨leaf []⟩

/-- The cells of a section, left to right. -/
def flat : Sec α → List (Option α)
  | leaf c => c
  | single O => O.flat
  | three O1 T2 O2 O3 => O1.flat ++ T2.flat ++ O2.flat ++ O3.flat

/-- The number of cells, the hole included. -/
def size (S : Sec α) : ℕ := S.flat.length

/-- The stored elements, left to right. -/
def stored (S : Sec α) : List α := S.flat.filterMap id

/-- The number of holes. -/
def holes (S : Sec α) : ℕ := (S.flat.filter Option.isNone).length

/-- The section at an address (`none` if the address does not exist). -/
def get : Sec α → List ℕ → Option (Sec α)
  | S, [] => some S
  | single O, 0 :: a => O.get a
  | three O1 _ _ _, 0 :: a => O1.get a
  | three _ T2 _ _, 1 :: a => T2.get a
  | three _ _ O2 _, 2 :: a => O2.get a
  | three _ _ _ O3, 3 :: a => O3.get a
  | _, _ :: _ => none

/-- Replace the section at an address by its image under `f` (unchanged if it does not exist). -/
def modify (f : Sec α → Sec α) : Sec α → List ℕ → Sec α
  | S, [] => f S
  | single O, 0 :: a => single (modify f O a)
  | three O1 T2 O2 O3, 0 :: a => three (modify f O1 a) T2 O2 O3
  | three O1 T2 O2 O3, 1 :: a => three O1 (modify f T2 a) O2 O3
  | three O1 T2 O2 O3, 2 :: a => three O1 T2 (modify f O2 a) O3
  | three O1 T2 O2 O3, 3 :: a => three O1 T2 O2 (modify f O3 a)
  | S, _ :: _ => S

/-- The absolute index of the first cell of the section at an address. -/
def offset : Sec α → List ℕ → ℕ
  | _, [] => 0
  | single O, 0 :: a => O.offset a
  | three O1 _ _ _, 0 :: a => O1.offset a
  | three O1 T2 _ _, 1 :: a => O1.size + T2.offset a
  | three O1 T2 O2 _, 2 :: a => O1.size + T2.size + O2.offset a
  | three O1 T2 O2 O3, 3 :: a => O1.size + T2.size + O2.size + O3.offset a
  | _, _ :: _ => 0

/-- Apply `f` to every cell. -/
def mapCells (f : Option α → Option α) : Sec α → Sec α
  | leaf c => leaf (c.map f)
  | single O => single (O.mapCells f)
  | three O1 T2 O2 O3 => three (O1.mapCells f) (T2.mapCells f) (O2.mapCells f) (O3.mapCells f)

/-- Remove the element `e` from its cell, leaving a hole there. -/
def eraseElt [DecidableEq α] (e : α) (S : Sec α) : Sec α :=
  S.mapCells (fun c => if c = some e then none else c)

/-- The values of the stored elements of a section of `Elt`s, left to right. -/
def vals (S : Sec Elt) : List ℝ := S.stored.map (fun e => (ofLex e).1)

end Sec

end DynSort


