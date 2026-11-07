-- Prove2me | Definitions.Def_ContinualCounting_belowRange
-- name    : ContinualCounting_belowRange
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:41:41.927529+00:00
-- url     : https://prove2.me/theorems/0018dd27-0517-4e0d-b740-b9172505ee5a
-- title:
--   The noise below a node: $z^{<u}_i$, $\max^{<u}(z)$, $\min^{<u}(z)$
-- statement:
--   For a node $u$ and a leaf $i\in\mathcal L(\mathcal T^u)$,
--   $$z^{<u}_i:=\sum_{v\in(\mathcal V(\mathcal T^u)\setminus\{u\})\cap\mathrm{Anc}(i)}b_v,$$
--   the contribution to $z_i$ from nodes strictly below $u$. Further $\max^{<u}(z):=\max_{i\in\mathcal L(\mathcal T^u)}z^{<u}_i$ and $\min^{<u}(z):=\min_{i\in\mathcal L(\mathcal T^u)}z^{<u}_i$.
--
--   The range $\max^{<u}(z)-\min^{<u}(z)$ is the quantity shown to grow going up the tree.
--
--   **Formalization Note** The maximum and minimum are `⨆`, `⨅` over the finite set $\mathcal L(\mathcal T^u)$, which is nonempty at every node of the tree.
-- source:
--   Bairaktari, Dahl, Larsen, The Binary Tree Mechanism is Optimal for Differentially Private Continual Counting, arXiv:2607.00876 (sha256 986e6426…), §5, p.18 (PDF p.19)

import Mathlib
import Definitions.Def_ContinualCounting_Node

set_option autoImplicit false

namespace ContinualCounting

/-- `z^{<u}_i := ∑_{v ∈ (V(T^u) ∖ {u}) ∩ Anc(i)} b_v`, the part of `z_i` contributed strictly below `u`
(Bairaktari, Dahl, Larsen, arXiv:2607.00876, sha256 986e6426…, §5, p.18), for `i ∈ L(T^u)`. -/
noncomputable def noiseBelow (h : ℕ) (u : Node) (z : Fin (2 ^ h) → ℝ) (i : Fin (2 ^ h)) : ℝ :=
  ∑ v ∈ ((treeV h u).erase u).filter (fun v => IsUnder h v i), coef h v z

/-- `max^{<u}(z) := max_{i ∈ L(T^u)} z^{<u}_i`, p.18.

**Formalization Note.** A `⨆` over the finite set `L(T^u)`, which is nonempty for every node of the
tree; the empty-set value `0` of a real `⨆` is reached only by pairs that are not nodes, and no
statement uses those. -/
noncomputable def belowMax (h : ℕ) (u : Node) (z : Fin (2 ^ h) → ℝ) : ℝ :=
  ⨆ i : {i : Fin (2 ^ h) // IsUnder h u i}, noiseBelow h u z i

/-- `min^{<u}(z) := min_{i ∈ L(T^u)} z^{<u}_i`, p.18, with the same convention as `belowMax`. -/
noncomputable def belowMin (h : ℕ) (u : Node) (z : Fin (2 ^ h) → ℝ) : ℝ :=
  ⨅ i : {i : Fin (2 ^ h) // IsUnder h u i}, noiseBelow h u z i

/-- The range `max^{<u}(z) − min^{<u}(z)`. -/
noncomputable def belowRange (h : ℕ) (u : Node) (z : Fin (2 ^ h) → ℝ) : ℝ :=
  belowMax h u z - belowMin h u z

end ContinualCounting


