-- Prove2me | Definitions.Def_HZTractability_IsThresholdSol
-- name    : HZTractability_IsThresholdSol
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T04:08:34.834664+00:00
-- url     : https://prove2.me/theorems/7c6ffdad-00bb-484e-956a-43be440a7c46
-- title:
--   $\kappa$-threshold solution (Definition 2.1)
-- statement:
--   Let $G=(V,E)$ be a directed graph and $0<\kappa<1/2$. A **$\kappa$-threshold solution** of $G$ is a vector $z\in[0,1]^V$ such that, at every vertex $v$,
--   $$
--   \sum_{u:\,u\to v}z_u>\tfrac12+\kappa\ \Longrightarrow\ z_v\le\kappa,\qquad
--   \sum_{u:\,u\to v}z_u<\tfrac12-\kappa\ \Longrightarrow\ z_v\ge 1-\kappa .
--   $$
--   If the incoming sum lies in $[1/2-\kappa,1/2+\kappa]$, any $z_v\in[0,1]$ is allowed. A self-loop at $v$ contributes $z_v$ to the incoming sum at $v$.
--
--   Threshold games are the source problem of the paper's reduction.
--
--   **Formalization Note** The predicate is stated for every real $\kappa$; the range $0<\kappa<1/2$ is a hypothesis where needed.
-- source:
--   Panageas, Shein, Taherijam, Vazirani, Exploring the Tractability Frontier of Hylland–Zeckhauser Models, arXiv:2610.35848 (held version, sha256 74b7bf9f…), Definition 2.1, p.6 (PDF p.8)

import Mathlib
import Definitions.Def_HZTractability_ThrGraph

namespace HZTractability

/-- **κ-threshold solution** (Panageas–Shein–Taherijam–Vazirani, arXiv:2610.35848, held version,
sha256 74b7bf9f…, Definition 2.1, p.6 (PDF 8)): "a vector z ∈ [0, 1]^V satisfying, at every vertex
v, ∑_{u : u→v} z_u > 1/2 + κ ⟹ z_v ≤ κ, ∑_{u : u→v} z_u < 1/2 − κ ⟹ z_v ≥ 1 − κ."

If the incoming sum lies in `[1/2 − κ, 1/2 + κ]` any `z_v ∈ [0, 1]` is allowed. A self-loop
`v → v` contributes `z_v` to the incoming sum at `v`.

**Formalization Note** Definition 2.1 is for `0 < κ < 1/2`; the predicate is stated for every real
`κ` and the range is a hypothesis where it is needed. -/
def IsThresholdSol (κ : ℝ) (G : ThrGraph) (z : Fin G.n → ℝ) : Prop :=
  (∀ v, 0 ≤ z v ∧ z v ≤ 1) ∧
  ∀ v, ((1 / 2 + κ < ∑ u ∈ Finset.univ.filter (fun u => G.adj u v = true), z u) → z v ≤ κ) ∧
    ((∑ u ∈ Finset.univ.filter (fun u => G.adj u v = true), z u < 1 / 2 - κ) → 1 - κ ≤ z v)

end HZTractability


