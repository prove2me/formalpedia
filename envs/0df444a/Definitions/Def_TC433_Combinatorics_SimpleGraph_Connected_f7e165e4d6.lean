-- Prove2me | Definitions.Def_TC433_Combinatorics_SimpleGraph_Connected_f7e165e4d6
-- name    : TC433_Combinatorics_SimpleGraph_Connected_f7e165e4d6
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T16:31:33.787564+00:00
-- url     : https://prove2.me/theorems/9966b9b1-171c-4380-ba62-db873a4371a1
-- title:
--   TauCeti: Combinatorics / SimpleGraph / Connected
-- statement:
--   Compatibility port of the definitions and proved supporting lemmas in TauCeti.Combinatorics.SimpleGraph.Connected for the concrete CFSG catalog. This module does not assert the classification theorem.
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/6e0c6acab5f4c6f42e5f5bab9bd5e4e84f74c380/TauCeti/Combinatorics/SimpleGraph/Connected.lean

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
# Connectedness of a graph numbered so that neighbours descend

A graph on `Fin n` whose every vertex other than `0` has a neighbour with a smaller number is
connected: a strong induction on the number of a vertex walks it down to `0`. Numbering the
vertices of a diagram this way is what makes connectedness of the Dynkin diagrams, finite and
affine alike, a two-line check, and this file states the induction once for all of them.

## Main results

* `TauCeti.SimpleGraph.connected_fin_of_exists_adj_lt`: a graph on `Fin n` in which every nonzero
  vertex has an adjacent vertex with a smaller number is connected.
-/

public section
set_option backward.isDefEq.respectTransparency.types false

namespace TauCeti

namespace SimpleGraph

/-- **A graph on `Fin n` in which every vertex other than `0` has a neighbour with a smaller number
is connected.** Every vertex reaches `0` by descending along such neighbours. -/
theorem connected_fin_of_exists_adj_lt {n : ℕ} {G : SimpleGraph (Fin n)} (hn : 0 < n)
    (h : ∀ i : Fin n, (i : ℕ) ≠ 0 → ∃ j : Fin n, (j : ℕ) < (i : ℕ) ∧ G.Adj j i) :
    G.Connected := by
  let z : Fin n := ⟨0, hn⟩
  have hreach (i : Fin n) : G.Reachable z i := by
    induction hi : (i : ℕ) using Nat.strong_induction_on generalizing i with
    | _ k ih =>
        rcases eq_or_ne k 0 with rfl | hk
        · have hiz : i = z := Fin.ext (by simpa [z] using hi)
          rw [hiz]
        · obtain ⟨j, hji, hadj⟩ := h i (hi ▸ hk)
          exact (ih (j : ℕ) (hi ▸ hji) j rfl).trans hadj.reachable
  have : Nonempty (Fin n) := ⟨z⟩
  exact ⟨fun i j ↦ (hreach i).symm.trans (hreach j)⟩

end SimpleGraph

end TauCeti


