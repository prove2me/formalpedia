-- Prove2me | Definitions.Def_StableMSR_BinaryTreeDP_Recurrence
-- name    : StableMSR_BinaryTreeDP_Recurrence
-- status  : Definition
-- author  : @lreyzin
-- created : 2026-11-14T09:07:26.82454+00:00
-- url     : https://prove2.me/theorems/a1ebe386-05bb-4adb-89ae-072b5d4dc9ae
-- title:
--   Finite bag-table recurrence and global assignment semantics
-- statement:
--   For a binary bag plan and a nonnegative count cap $K$, the table recurrence enumerates allowed valid bag assignments, joins compatible child entries, discards counts greater than $K$, and retains minimum weight for each assignment/count key. Global evaluation means that one assignment simultaneously realizes all local choices and valid predicates, with counts and weights summed over the plan. The total retained table volume and the number of raw leaf choices and join triples are also defined. These finite semantic definitions do not assert an instruction-level implementation or execution-time bound.
-- source:
--   Stable sum-of-radii clustering recovery: finite tree-decomposition dynamic programming.

import Definitions.Def_StableMSR_BinaryTreeDP_Plan
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
open scoped Classical
namespace StableMSR.Recovery.TreeDP
abbrev Entry (V X : Type*) := (V → X) × (ℕ × ℝ)

noncomputable def accepted {V X : Type*} (d : BagData V X) : Finset (V → X) :=
  d.choices.filter d.valid

noncomputable def minimize {V X : Type*} (A : Finset (Entry V X)) : Finset (Entry V X) :=
  A.filter (fun a => ∀ b ∈ A, b.1 = a.1 → b.2.1 = a.2.1 → a.2.2 ≤ b.2.2)

noncomputable def trim {V X : Type*} (cap : ℕ) (A : Finset (Entry V X)) : Finset (Entry V X) :=
  A.filter (fun a => a.2.1 ≤ cap)

noncomputable def leafEntries {V X : Type*} (d : BagData V X) : Finset (Entry V X) :=
  (accepted d).image (fun a => (a,(d.count a,d.weight a)))

noncomputable def joinEntries {V X : Type*} [DecidableEq V]
    (d : BagData V X) (leftBag rightBag : Finset V)
    (L R : Finset (Entry V X)) : Finset (Entry V X) :=
  (((accepted d ×ˢ L) ×ˢ R).filter (fun p =>
    AgreeOn (d.bag ∩ leftBag) p.1.1 p.1.2.1 ∧
    AgreeOn (d.bag ∩ rightBag) p.1.1 p.2.1)).image (fun p =>
      (p.1.1,(d.count p.1.1 + p.1.2.2.1 + p.2.2.1,
        d.weight p.1.1 + p.1.2.2.2 + p.2.2.2)))

/-- The executable finite tree recurrence: bag choices, separator agreement,
child-table joins, count truncation, then a minimum cost per bag/count key. -/
noncomputable def solve {V X : Type*} [DecidableEq V] (cap : ℕ) : Plan V X → Finset (Entry V X)
  | .leaf d => minimize (trim cap (leafEntries d))
  | .branch d L R => minimize (trim cap
      (joinEntries d L.root.bag R.root.bag (solve cap L) (solve cap R)))

inductive GlobalEvaluates {V X : Type*} [DecidableEq V] : Plan V X → (V → X) → ℕ → ℝ → Prop
  | leaf (d : BagData V X) (whole a : V → X)
      (ha : a ∈ d.choices) (hv : d.valid a) (hag : AgreeOn d.bag whole a) :
      GlobalEvaluates (.leaf d) whole (d.count a) (d.weight a)
  | branch (d : BagData V X) (L R : Plan V X)
      (whole a : V → X) (jl jr : ℕ) (wl wr : ℝ)
      (ha : a ∈ d.choices) (hv : d.valid a) (hag : AgreeOn d.bag whole a)
      (hl : GlobalEvaluates L whole jl wl) (hr : GlobalEvaluates R whole jr wr) :
      GlobalEvaluates (.branch d L R) whole (d.count a+jl+jr) (d.weight a+wl+wr)

noncomputable def Plan.tableVolume {V X : Type*} [DecidableEq V] (cap : ℕ) : Plan V X → ℕ
  | .leaf d => (solve cap (.leaf d)).card
  | .branch d L R => (solve cap (.branch d L R)).card + L.tableVolume cap + R.tableVolume cap

noncomputable def Plan.rawCandidateVolume {V X : Type*} [DecidableEq V]
    (cap : ℕ) : Plan V X → ℕ
  | .leaf d => d.choices.card
  | .branch d L R => d.choices.card * (solve cap L).card * (solve cap R).card +
      L.rawCandidateVolume cap + R.rawCandidateVolume cap

end StableMSR.Recovery.TreeDP


