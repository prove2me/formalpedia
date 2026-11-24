-- Prove2me | Definitions.Def_Sensitivity214439_PairedSemantic_Solutions_CopyGraphPopulation
-- name    : Sensitivity214439_PairedSemantic_Solutions_CopyGraphPopulation
-- status  : Definition
-- author  : @yousofy
-- created : 2026-11-24T19:45:36.262076+00:00
-- url     : https://prove2.me/theorems/d89aa9df-e999-447c-968b-4d1c9a81f87e
-- title:
--   Disjoint copies of induced conflict graphs
-- statement:
--   For a finite family of finite vertex subsets $S_c$ of a graph $G$, the copy-vertex type is the dependent disjoint union of tagged vertices $(c,v)$ with $v\in S_c$. Two copy vertices are adjacent precisely when their tags agree and their original vertices are adjacent in $G$. This construction keeps different marker-indexed copies disjoint even when the original subsets overlap.
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; checked task source lean/Solutions/CopyGraphPopulation.lean lines 14–19; SHA256 85a3bfd1a112a309991510267a172686b2463acf7d058d438334fcdf13dbbb51; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Ring.Fin
import Mathlib.Combinatorics.SimpleGraph.Extremal.Turan
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto

namespace SensitivityActiveSocketPopulation
end SensitivityActiveSocketPopulation
namespace SensitivityCopyGraphPopulation
end SensitivityCopyGraphPopulation
namespace SensitivityGraphPopulation
end SensitivityGraphPopulation



/-! Disjoint copies of induced conflict graphs, with exact integral edge bounds. -/
namespace SensitivityCopyGraphPopulation

noncomputable section
open scoped Classical BigOperators
open SensitivityGraphPopulation SensitivityActiveSocketPopulation
set_option autoImplicit false

variable {C V : Type} [Fintype C]

abbrev CopyVertex (sets : C → Finset V) := Σ c, {v // v ∈ sets c}

def copyGraph (G : SimpleGraph V) (sets : C → Finset V) : SimpleGraph (CopyVertex sets) where
  Adj a b := a.1 = b.1 ∧ G.Adj a.2.val b.2.val
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => G.ne_of_adj h.2 rfl⟩




















end
end SensitivityCopyGraphPopulation


