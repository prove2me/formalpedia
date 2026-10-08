-- Prove2me | Definitions.Def_IsingLTL_BeliefProp_BallApprox
-- name    : IsingLTL_BeliefProp_BallApprox
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T01:16:22.287481+00:00
-- url     : https://prove2.me/theorems/42a10c54-dd6f-4ad1-9d46-df605a3c9157
-- title:
--   Balls $\mathsf B_{i_*}(r)$, their border, and the BP approximation $\nu_U$ of local marginals (2.12)
-- statement:
--   Let $G=(V,E)$ be a finite graph and $i_*\in V$. The **ball** $U=\mathsf B_{i_*}(r)$ is the set of vertices at graph distance at most $r$ from $i_*$ (also the subgraph it induces), $E_U$ its edge set, and $\partial U$ its **border**, the vertices at distance exactly $r$ from $i_*$. "$\mathsf B_{i_*}(t)$ is a tree" means that the subgraph induced on the ball is acyclic.
--
--   For each $i\in\partial U$ let $j(i)$ be a fixed neighbour of $i$ in $U$, and let $\nu^*$ be a BP message family. The **BP approximation** of the marginal on $U$ is the distribution
--   $$\nu_U(\underline x_U)=\frac1{z_U}\exp\Big\{\beta\sum_{(i,j)\in E_U}x_ix_j+B\sum_{i\in U\setminus\partial U}x_i\Big\}\prod_{i\in\partial U}\nu^*_{i\to j(i)}(x_i),$$
--   and $\mu_U$ denotes the marginal on $U$ of the Ising model (1.1) on $G$ with constant field $B$.
--
--   These are the two distributions compared in Theorem 2.7.
--
--   **Formalization Note** Distances are extended natural numbers: vertices in other connected components are at distance $+\infty$ and never belong to a ball.
-- source:
--   Dembo & Montanari, Ising Models on Locally Tree-Like Graphs, arXiv:0804.4726v3, p. 4 (B_i(t)), p. 7, eq. (2.12) and the paragraph before it

import Mathlib
import Definitions.Def_IsingLTL_BeliefProp_IsingModel

namespace IsingLTL.BeliefProp

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The ball `B_{i*}(r)` of radius `r` around `i*` in `G`: the vertices at graph distance at most
`r` from `i*` (arXiv:0804.4726v3, p. 4 and p. 7).

Formalization Note: the distance is `SimpleGraph.edist`, which is `⊤` between vertices of
different components, so unreachable vertices are never in the ball. -/
noncomputable def ball (G : SimpleGraph V) (istar : V) (r : ℕ) : Finset V :=
  Finset.univ.filter (fun v => G.edist istar v ≤ (r : ℕ∞))

/-- The border `∂U` of `U = B_{i*}(r)`: its vertices at distance exactly `r` from `i*`
(arXiv:0804.4726v3, p. 7). -/
noncomputable def border (G : SimpleGraph V) (istar : V) (r : ℕ) : Finset V :=
  Finset.univ.filter (fun v => G.edist istar v = (r : ℕ∞))

/-- "`B_{i*}(t)` is a tree" (arXiv:0804.4726v3, Theorem 2.7, p. 8): the subgraph induced by `G`
on the ball is acyclic (it is connected by construction). -/
def IsTreeBall (G : SimpleGraph V) (istar : V) (t : ℕ) : Prop :=
  (G.induce (↑(ball G istar t) : Set V)).IsAcyclic

/-- Unnormalized weight of (2.12):
`exp{β ∑_{(i,j)∈E_U} x_i x_j + B ∑_{i∈U\∂U} x_i} ∏_{i∈∂U} ν*_{i→j(i)}(x_i)`, with `E_U` the
edges induced on `U = B_{i*}(r)` (each counted once: half the ordered-pair sum). -/
noncomputable def nuUWeight (G : SimpleGraph V) [DecidableRel G.Adj] (β B : ℝ)
    (νstar : V → V → Bool → ℝ) (istar : V) (r : ℕ) (jsel : V → V)
    (y : {v // v ∈ ball G istar r} → Bool) : ℝ := by
  classical
  exact Real.exp (β * ((∑ u : {v // v ∈ ball G istar r}, ∑ w : {v // v ∈ ball G istar r},
        if G.Adj u.1 w.1 then spin (y u) * spin (y w) else 0) / 2)
      + B * ∑ u : {v // v ∈ ball G istar r}, if u.1 ∈ border G istar r then 0 else spin (y u))
    * ∏ u : {v // v ∈ ball G istar r},
        if u.1 ∈ border G istar r then νstar u.1 (jsel u.1) (y u) else 1

/-- The BP approximation `ν_U` of the marginal on `U = B_{i*}(r)` (arXiv:0804.4726v3, (2.12),
p. 7): `ν_U(x_U) = (1/z_U) exp{β ∑_{(i,j)∈E_U} x_i x_j + B ∑_{i∈U\∂U} x_i} ∏_{i∈∂U} ν*_{i→j(i)}(x_i)`,
where `j(i) = jsel i` is a fixed neighbour of `i ∈ ∂U` in `U` and `ν*` a BP message family. -/
noncomputable def nuU (G : SimpleGraph V) [DecidableRel G.Adj] (β B : ℝ)
    (νstar : V → V → Bool → ℝ) (istar : V) (r : ℕ) (jsel : V → V)
    (y : {v // v ∈ ball G istar r} → Bool) : ℝ :=
  nuUWeight G β B νstar istar r jsel y / ∑ y', nuUWeight G β B νstar istar r jsel y'

/-- The marginal `μ_U` on `U = B_{i*}(r)` of the Ising model (1.1) on the finite graph `G` with
inverse temperature `β` and constant field `B` (arXiv:0804.4726v3, p. 7). -/
noncomputable def muU (G : SimpleGraph V) [DecidableRel G.Adj] (β B : ℝ) (istar : V) (r : ℕ) :
    ({v // v ∈ ball G istar r} → Bool) → ℝ :=
  marginalOn Finset.univ (ball G istar r) (isingOn G β (fun _ => B) ∅ Finset.univ)

end IsingLTL.BeliefProp


