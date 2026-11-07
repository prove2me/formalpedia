-- Prove2me | Definitions.Def_VDCyclePack_IsFracPacking
-- name    : VDCyclePack_IsFracPacking
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T13:09:33.428194+00:00
-- url     : https://prove2.me/theorems/ad3d0b26-e269-4525-a5ca-0d38358e784b
-- title:
--   Fractional cycle packing: a feasible solution of the natural LP (1)
-- statement:
--   A **fractional packing** of a finite graph $G$ is a weighting $x$ of its cycles with
--   $$
--   x_C\ge 0\quad\text{for every cycle } C,\qquad \sum_{C\ni v}x_C\le 1\quad\text{for every vertex } v .
--   $$
--   These are the constraints of the natural LP (1).
--
--   Lemma 4.1 computes an optimal fractional packing, and Lemmas 4.3 and 6.4 bound the weight that any fractional packing puts outside the candidate family.
--
--   **Formalization Note** The weights are a function on all subgraphs; only its values on cycles are constrained.
-- source:
--   Kundu–Lochet, Nearly Tight Approximation for Vertex-Disjoint Cycle Packing (STOC 2027 submission manuscript, preprint basis, sha256 95f2e61a…cacb1), (1), p.3, and Section 3, p.9

import Mathlib
import Definitions.Def_VDCyclePack_load

namespace VDCyclePack

/-- **Fractional cycle packing: a feasible solution of the natural LP (1).**
Kundu–Lochet, *Nearly Tight Approximation for Vertex-Disjoint Cycle Packing* (STOC 2027
submission manuscript), (1), p.3, and Section 3, p.9: "The natural LP relaxation (1) assigns a nonnegative
variable x_C to every cycle C of G, with Σ_{C∋v} x_C ≤ 1 for every vertex v ... We call a feasible
solution a fractional packing".

`IsFracPacking G x` says `x C ≥ 0` for every cycle `C` of `G` and the load at every vertex is at
most one.

**Formalization Note.** Weights are a function on all subgraphs; only its values on cycles are
constrained or read. -/
def IsFracPacking {V : Type*} [Fintype V] (G : SimpleGraph V) (x : G.Subgraph → ℝ) : Prop :=
  (∀ C ∈ cycles G, 0 ≤ x C) ∧ ∀ v, load G x v ≤ 1

end VDCyclePack


