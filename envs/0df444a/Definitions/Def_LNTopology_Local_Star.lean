-- Prove2me | Definitions.Def_LNTopology_Local_Star
-- name    : LNTopology_Local_Star
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T06:27:06.609984+00:00
-- url     : https://prove2.me/theorems/89a1b4d1-46a6-47bb-82b4-42e74e9ed45a
-- title:
--   §3.3 / App. C, pp. 9, 13 — the star network with hub h for a flow F
-- statement:
--   Given a payment flow $F=(f_i)_{i\in V}$ and a node $h\in V$, the star with hub $h$ is the network in which every node $i\neq h$ has exactly one channel, to $h$, carrying net flow $f_i$ from $i$ to $h$, and there are no other channels:
--   $$
--   \lambda_{i,h}=f_i,\qquad \lambda_{h,i}=-f_i\qquad (i\neq h),
--   $$
--   and $\lambda_{i,j}=0$ when neither $i$ nor $j$ is $h$, or $i=j=h$.
--
--   The star is the natural candidate for a globally cheap topology studied in §3.3; Corollary 3.11 shows it is not cost-minimizing once there are two net payers and two net payees.
--
--   **Formalization Note** Under the row-sum convention $\sum_j\lambda_{i,j}=f_i$, the star supports $F$ exactly when $\sum_i f_i=0$ (the hub's row is $-\sum_{i\neq h}f_i$). A node $i\neq h$ with $f_i=0$ gets $\lambda_{i,h}=0$, i.e. no channel, as the paper's convention $\lambda_{u,v}=0$ for absent channels requires. The paper's proof of Theorem 3.10 writes $\lambda_{0,i}=f_i$ with the opposite sign convention; the two stars are mirror images under $F\mapsto-F$. Under `open LNTopology.Local` the name `star` clashes with Mathlib's `Star.star`; write `LNTopology.Local.star` or work inside the namespace.
-- source:
--   Guasoni, Huberman & Shikhelman, Lightning Network Economics: Topology, SSRN 4439190 (version of Feb. 3, 2023), p. 9 (PDF 10), §3.3; p. 13 (PDF 14), App. C, proof of Corollary 3.11

import Mathlib

namespace LNTopology.Local

/-- The star network with hub `h` for the flow `f` (SSRN 4439190, §3.3, p. 9, and App. C,
p. 13): every node `i ≠ h` has a single channel, to `h`, carrying net flow `f i` from `i` to `h`;
there are no other channels. Under the row-sum convention of `Supports`, it supports `f`
exactly when `∑ i, f i = 0`. -/
def star {V : Type*} [DecidableEq V] (f : V → ℝ) (h : V) : V → V → ℝ :=
  fun i j =>
    if j = h ∧ i ≠ h then f i
    else if i = h ∧ j ≠ h then -f j
    else 0

end LNTopology.Local


