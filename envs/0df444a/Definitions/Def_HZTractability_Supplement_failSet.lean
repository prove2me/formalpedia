-- Prove2me | Definitions.Def_HZTractability_Supplement_failSet
-- name    : HZTractability_Supplement_failSet
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:28:48.405901+00:00
-- url     : https://prove2.me/theorems/a2ddeb77-ac7e-4bca-92da-dc5b4edbcc15
-- title:
--   The vertices at which the $\kappa$-threshold constraint fails
-- statement:
--   Let $G=(V,E)$ be a threshold-game graph, $\kappa$ a tolerance and $z\in\mathbb R^V$. The **failure set** of $z$ is the set of vertices $v$ at which the $\kappa$-threshold constraint
--   $$\sum_{u:u\to v}z_u>\tfrac12+\kappa\implies z_v\le\kappa,\qquad \sum_{u:u\to v}z_u<\tfrac12-\kappa\implies z_v\ge1-\kappa$$
--   is violated, i.e. $\sum_{u\to v}z_u>\frac12+\kappa$ and $z_v>\kappa$, or $\sum_{u\to v}z_u<\frac12-\kappa$ and $z_v<1-\kappa$. A self-loop $v\to v$ contributes $z_v$ once.
--
--   Its cardinality is the number of failed vertices bounded in Theorem 5.7 and in the weak threshold problem (Definition 5.3).
--
--   **Formalization Note** The failure condition is the exact negation of the per-vertex clause of the published `HZTractability.IsThresholdSol`; its $[0,1]$ clause is not part of the count.
-- source:
--   Panageas, Shein, Taherijam, Vazirani, Exploring the Tractability Frontier of Hylland–Zeckhauser Models, arXiv:2610.35848 (held version, sha256 74b7bf9f…), §5.1, p.20 (PDF p.22); Definition 5.3 and Theorem 5.7, pp.21–23 (PDF pp.23–25)

import Mathlib
import Definitions.Def_HZTractability_ThrGraph

set_option autoImplicit false

namespace HZTractability.Supplement

open Classical in
/-- **The vertices at which the κ-threshold constraint fails** (Panageas–Shein–Taherijam–Vazirani,
arXiv:2610.35848, held version, sha256 74b7bf9f…, §5.1, p.20 (PDF 22): "the constraint at v is
∑_{u:u→v} z_u > 1/2 + κ ⟹ z_v ≤ κ, ∑_{u:u→v} z_u < 1/2 − κ ⟹ z_v ≥ 1 − κ"; counted in Definition 5.3
and Theorem 5.7, p.23 (PDF 25)).

`v` fails when `∑_{u→v} z_u > 1/2 + κ` and `z_v > κ`, or `∑_{u→v} z_u < 1/2 − κ` and `z_v < 1 − κ`:
the exact negation of the per-vertex clause of the published `IsThresholdSol`. The sum runs over the
`u` with `u → v`; a self-loop `v → v` counts once.

**Formalization Note** The `[0, 1]` clause of `IsThresholdSol` is not a per-vertex threshold
constraint and is not counted (it holds for every clipped decoded vector). -/
noncomputable def failSet (κ : ℝ) (G : ThrGraph) (z : Fin G.n → ℝ) : Finset (Fin G.n) :=
  Finset.univ.filter fun v =>
    (1 / 2 + κ < ∑ u ∈ Finset.univ.filter (fun u => G.adj u v = true), z u ∧ κ < z v) ∨
    (∑ u ∈ Finset.univ.filter (fun u => G.adj u v = true), z u < 1 / 2 - κ ∧ z v < 1 - κ)

end HZTractability.Supplement


