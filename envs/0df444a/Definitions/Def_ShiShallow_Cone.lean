-- Prove2me | Definitions.Def_ShiShallow_Cone
-- name    : ShiShallow_Cone
-- status  : Definition
-- author  : @Goku
-- created : 2026-09-10T03:52:25.94133+00:00
-- url     : https://prove2.me/theorems/15aa98a9-abbe-4bfc-b204-513c4568b1d5
-- title:
--   Causal cones of layered circuits
-- statement:
--   The backward causal cone of a set of wires: one layer step adjoins the support of every gate meeting the incoming set, and coneOf folds this over the layers. Each gate is tested against the incoming set rather than the accumulator, which is correct exactly under LayerOk.
-- source:
--   Original work by Yueheng Shi (Apache-2.0), formalised in Lean 4 with Mathlib.

/-
Copyright (c) 2026 Yueheng Shi. All rights reserved.
Released under the Apache License, Version 2.0.
Authors: Yueheng Shi

Shallow quantum circuits and causal cones.

MODIFICATIONS made for publication on Prove2me: declarations are grouped into a definition bundle;
no statement or proof was otherwise altered.

Built against Mathlib (Apache-2.0) at revision 0df444a360eaa60ab8c11dca51a86af692955474.
-/
import Mathlib
import Definitions.Def_ShiShallow_Circuit

namespace ShiShallow

/-- One backward step of the causal cone: adjoin the support of every gate in the layer that
touches `S`. -/
def coneStep {n : ℕ} (l : List (Instr n)) (S : Finset (Fin n)) : Finset (Fin n) :=
  l.foldr (fun g acc => if (g.support ∩ S).Nonempty then g.support ∪ acc else acc) S

/-- The causal cone of `S`, propagated backwards through the layers (the last layer acts on
`S` first). -/
def coneOf {n : ℕ} (c : Layered n) (S : Finset (Fin n)) : Finset (Fin n) :=
  c.foldr coneStep S

/-- `coneStep` tests each gate against the **incoming** set, not against the accumulator.
That is deliberate: within a layer whose supports are pairwise disjoint no cascading can
occur, and testing against the accumulator would over-approximate the cone. -/
theorem coneStep_cons {n : ℕ} (g : Instr n) (t : List (Instr n)) (S : Finset (Fin n)) :
    coneStep (g :: t) S =
      if (g.support ∩ S).Nonempty then g.support ∪ coneStep t S else coneStep t S := rfl

theorem coneStep_nil {n : ℕ} (S : Finset (Fin n)) : coneStep [] S = S := rfl

theorem coneOf_cons {n : ℕ} (l : List (Instr n)) (t : Layered n) (S : Finset (Fin n)) :
    coneOf (l :: t) S = coneStep l (coneOf t S) := rfl

theorem coneOf_nil {n : ℕ} (S : Finset (Fin n)) : coneOf ([] : Layered n) S = S := rfl

end ShiShallow


