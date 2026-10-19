-- Prove2me | Definitions.Def_GraphColoring
-- name    : GraphColoring
-- status  : Definition
-- author  : @@bwdaugherty
-- created : 2026-10-16T20:24:48.825041+00:00
-- url     : https://prove2.me/theorems/50688edd-e8ae-4f12-8384-b9daf5f5f0fe
-- title:
--   Graph coloring types
-- statement:
--   A 2-coloring of K_n is a function assigning each edge a color (Red or Blue). A subset is monochromatic if all its edges have the same color.
-- source:
--   Custom definition for Ramsey theory

/-
Graph coloring definitions for Ramsey theory
These are custom definitions since Mathlib doesn't have them yet.
-/

import Mathlib.Data.Finset.Card
import Mathlib.Data.Fin.Basic

namespace Ramsey55

/-- A 2-coloring of edges of K_n (complete graph on n vertices).
    Colors are represented as Bool: true = Red, false = Blue.
    We only store colorings for i < j since edges are unordered. -/
def Coloring (n : ℕ) := {f : Fin n → Fin n → Bool // ∀ i j, f i j = f j i}

/-- Extract the coloring function from the subtype -/
def Coloring.toFun {n : ℕ} (χ : Coloring n) : Fin n → Fin n → Bool := χ.val

/-- Check if a set S ⊆ V(K_n) induces a monochromatic subgraph.
    S is monochromatic if all edges in S have the same color. -/
def IsMonochromatic {n : ℕ} (χ : Coloring n) (S : Finset (Fin n)) : Prop :=
  (∀ i j, i ∈ S → j ∈ S → i < j → χ.toFun i j = true) ∨
  (∀ i j, i ∈ S → j ∈ S → i < j → χ.toFun i j = false)

/-- A Ramsey witness: a coloring with no monochromatic K_s -/
structure RamseyWitness (n s : ℕ) where
  coloring : Coloring n
  no_mono : ∀ S : Finset (Fin n), S.card = s → ¬IsMonochromatic coloring S

end Ramsey55


