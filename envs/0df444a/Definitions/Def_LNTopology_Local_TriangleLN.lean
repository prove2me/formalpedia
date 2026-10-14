-- Prove2me | Definitions.Def_LNTopology_Local_TriangleLN
-- name    : LNTopology_Local_TriangleLN
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T06:27:04.443158+00:00
-- url     : https://prove2.me/theorems/7bc5ae2a-8a39-4d24-a5c0-761aa00543b4
-- title:
--   Theorem 3.1 / Figure 1, p. 6 — the network on three nodes u, v, w with net flows a (u→v), b (v→w), d (u→w)
-- statement:
--   For three nodes $u,v,w$ of $V$ and real numbers $a,b,d$, let $T_{u,v,w}(a,b,d)$ be the network whose only channels are a channel between $u$ and $v$ with net flow $a$ from $u$ to $v$, a channel between $v$ and $w$ with net flow $b$ from $v$ to $w$, and a channel between $u$ and $w$ with net flow $d$ from $u$ to $w$:
--   $$
--   \lambda_{u,v}=a,\ \lambda_{v,u}=-a,\quad \lambda_{v,w}=b,\ \lambda_{w,v}=-b,\quad \lambda_{u,w}=d,\ \lambda_{w,u}=-d,
--   $$
--   and $\lambda_{i,j}=0$ for every other pair. A coefficient $0$ means that channel is absent.
--
--   This encodes the three configurations of Theorem 3.1 and Figure 1: $T_{u,v,w}(\lambda_1,\lambda_2,0)$ is the chain $\overrightarrow{uv}^{\lambda_1},\overrightarrow{vw}^{\lambda_2}$; $T_{u,v,w}(0,\lambda_2-\lambda_1,\lambda_1)$ is $\overrightarrow{uw}^{\lambda_1},\ {}^{\lambda_1}\overleftrightarrow{vw}^{\lambda_2}$; and $T_{u,v,w}(\lambda_1-\lambda_2,0,\lambda_2)$ is ${}^{\lambda_2}\overleftrightarrow{uv}^{\lambda_1},\ \overrightarrow{uw}^{\lambda_2}$.
--
--   **Formalization Note** The definition is meant for pairwise distinct $u,v,w$, which every theorem using it assumes; for coinciding nodes the case split simply takes the first matching clause. In the paper's notation ${}^{a}\overleftrightarrow{xy}^{b}$, node $y$ sends $a$ and $x$ sends $b$, so the net flow from $x$ to $y$ is $b-a$ (§2.1, p. 4).
-- source:
--   Guasoni, Huberman & Shikhelman, Lightning Network Economics: Topology, SSRN 4439190 (version of Feb. 3, 2023), p. 6 (PDF 7), Theorem 3.1 and Figure 1; channel notation p. 4 (PDF 5), §2.1

import Mathlib

namespace LNTopology.Local

/-- The network on the three nodes `u, v, w` with net flow `a` from `u` to `v`, `b` from `v` to
`w` and `d` from `u` to `w` (and the negatives in the opposite direction), and no other channel.
It encodes the three structures of Theorem 3.1 and Figure 1 (SSRN 4439190, p. 6):
`triangleLN u v w λ₁ λ₂ 0` is `u →^{λ₁} v, v →^{λ₂} w`; `triangleLN u v w 0 (λ₂ - λ₁) λ₁` is
`u →^{λ₁} w, λ₁ ←→_{vw} λ₂`; `triangleLN u v w (λ₁ - λ₂) 0 λ₂` is `λ₂ ←→_{uv} λ₁, u →^{λ₂} w`.
Intended for pairwise distinct `u, v, w`. -/
def triangleLN {V : Type*} [DecidableEq V] (u v w : V) (a b d : ℝ) : V → V → ℝ :=
  fun i j =>
    if i = u ∧ j = v then a
    else if i = v ∧ j = u then -a
    else if i = v ∧ j = w then b
    else if i = w ∧ j = v then -b
    else if i = u ∧ j = w then d
    else if i = w ∧ j = u then -d
    else 0

end LNTopology.Local


