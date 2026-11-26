-- Prove2me | Definitions.Def_Sabidussi_CyclicWord
-- name    : Sabidussi_CyclicWord
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T04:07:54.552847+00:00
-- url     : https://prove2.me/theorems/e5e11af0-b2f0-4de3-8c17-573f431e502f
-- title:
--   Cyclic Word
-- statement:
--   Definitions and structural lemmas for Cyclic Word, from Upstream contributors (gexahedron/sabidussi-lean; see pinned Apache-2.0 LICENSE and README.md)'s pinned Sabidussi compatibility conjecture for finite Eulerian loop multigraphs development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/gexahedron/sabidussi-lean/blob/58307d74da99ec6e4fe28e012c30c83e369c54c3/Sabidussi/CyclicWord.lean

import Definitions.Def_Sabidussi_LocalPattern
import Definitions.Def_Sabidussi_OddBalance
import Definitions.Def_Sabidussi_Parity
import Mathlib.Data.Finset.Sort
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Order.Interval.Finset.Fin
set_option autoImplicit true
namespace Sabidussi
namespace CyclicWord
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]
structure Word where
  n : ℕ
  letter : Fin (n + 1) → V
namespace Word
variable (W : Word (V := V))
abbrev Pos := Fin (W.n + 1)
def prev (i : W.Pos) : W.Pos := (finRotate (W.n + 1)).symm i
abbrev Occurrence (v : V) := {i : W.Pos // W.letter i = v}
instance (v : V) : Fintype (W.Occurrence v) :=
  Subtype.fintype fun i : W.Pos ↦ W.letter i = v
def incidentColor (x : W.Pos → Color) {v : V} (o : W.Occurrence v) (s : Fin 2) : Color :=
  if s = 0 then x (W.prev o.1) else x o.1
structure Coloring where
  color : W.Pos → Color
  transition_ne : ∀ i, color (W.prev i) ≠ color i
  color_even : ∀ (v : V) (z : Color),
    Even (Fintype.card {os : W.Occurrence v × Fin 2 // W.incidentColor color os.1 os.2 = z})
end Word
section LocalPattern
def localQuadraticContribution (n : ℕ) (c : Fin 3) : F₂ :=
  (∑ i, quadratic (localDifference n c i)) +
    ∑ i, ∑ j, if j < i then bracket (localDifference n c i) (localDifference n c j) else 0
end LocalPattern
namespace Word
section Frames
variable (W : Word (V := V))
noncomputable def occurrenceOrderIsoFin
    (hmin : ∀ v, 2 ≤ Fintype.card (W.Occurrence v)) (v : V) :
    W.Occurrence v ≃o Fin (Fintype.card (W.Occurrence v) - 2 + 2) :=
  (Fintype.orderIsoFinOfCardEq (W.Occurrence v)
    (Nat.sub_add_cancel (hmin v)).symm).symm
noncomputable def frameDifference
    (hmin : ∀ v, 2 ≤ Fintype.card (W.Occurrence v))
    (v : V) (c : Fin 3) (o : W.Occurrence v) : Color :=
  localDifference (Fintype.card (W.Occurrence v) - 2) c (W.occurrenceOrderIsoFin hmin v o)
end Frames
section Interaction
variable (W : Word (V := V))
noncomputable def interaction
    (hmin : ∀ v, 2 ≤ Fintype.card (W.Occurrence v))
    (v u : V) (cv cu : Fin 3) : F₂ :=
  if v = u then 0 else
    ∑ i : W.Occurrence v, ∑ j : W.Occurrence u,
      if j.1 < i.1 then
        bracket (W.frameDifference hmin v cv i) (W.frameDifference hmin u cu j)
      else 0
end Interaction
section DifferencesAndPrefixes
variable (W : Word (V := V))
noncomputable def chosenDifference
    (hmin : ∀ v, 2 ≤ Fintype.card (W.Occurrence v))
    (choice : V → Fin 3) (i : W.Pos) : Color :=
  W.frameDifference hmin (W.letter i) (choice (W.letter i)) ⟨i, rfl⟩
def prefixColor (y : W.Pos → Color) (i : W.Pos) : Color :=
  ∑ j ∈ Finset.Iic i, y j
def orderedLetterInteraction (y : W.Pos → Color) (v u : V) : F₂ :=
  ∑ i : W.Occurrence v, ∑ j : W.Occurrence u,
    if j.1 < i.1 then bracket (y i.1) (y j.1) else 0
end DifferencesAndPrefixes
end Word
end CyclicWord
end Sabidussi


