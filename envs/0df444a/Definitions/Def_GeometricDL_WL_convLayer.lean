-- Prove2me | Definitions.Def_GeometricDL_WL_convLayer
-- name    : GeometricDL_WL_convLayer
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:19:50.794487+00:00
-- url     : https://prove2.me/theorems/2289ddd9-486e-4e65-809a-4f896b9fe380
-- title:
--   Convolutional GNN layer, eq. (33), with coefficient $c_{uv}=\kappa(h_u,h_v,|N_u|,|N_v|)$
-- statement:
--   Let $G=(V,E)$ be a finite graph and $h:V\to H$ the current node states (the features $x$ for the first layer). A **convolutional GNN layer** maps $h$ to new states
--
--   $$h'_u=\varphi\Big(h_u,\ \bigoplus_{v\in N_u} c_{uv}\,\psi(h_v)\Big),\qquad c_{uv}=\kappa\big(h_u,h_v,|N_u|,|N_v|\big),$$
--
--   where $\psi:H\to M$ maps states to a real vector space $M$, $\bigoplus$ is a permutation-invariant aggregator of the multiset $\{\!\{c_{uv}\psi(h_v):v\in N_u\}\!\}$ (sum, mean, maximum, …), $\varphi$ is the update, and the coefficient $c_{uv}$ (the importance of $v$ for $u$) is a fixed function $\kappa$ of the two endpoints' states and degrees.
--
--   This coefficient class contains the constants the paper has in mind: entries of $A$ on edges, the Kipf–Welling normalisation $1/\sqrt{d_ud_v}$, mean aggregation $1/d_u$, Laplacian entries on edges, and look-up tables $c(x_u,x_v)$.
--
--   **Formalization Note** The paper calls $c_{uv}$ "a constant that often directly depends on the entries in $A$". Read as an arbitrary function of $A$, the mission's goal is false (see the goal theorem). The coefficient is therefore restricted to a local function of the endpoints. The aggregator is an arbitrary function of the multiset of messages; every such function is permutation-invariant, and every permutation-invariant aggregator is one.
-- source:
--   Bronstein, Bruna, Cohen & Veličković, Geometric Deep Learning, arXiv:2104.13478v2, §5.3, eq. (33), printed p. 79 (PDF p. 83); aggregator ⊕, ψ, φ, printed p. 78 (PDF p. 82)

import Mathlib
import Definitions.Def_GeometricDL_WL_nbhd

namespace GeometricDL.WL

/-- **Convolutional GNN layer, eq. (33) (with the coefficient read as a local function).**
Bronstein, Bruna, Cohen & Veličković, *Geometric Deep Learning*, arXiv:2104.13478v2, §5.3,
eq. (33), printed p. 79 (PDF p. 83): "In the convolutional flavour … the features of the
neighbourhood nodes are directly aggregated with fixed weights, h_u = φ(x_u, ⊕_{v∈N_u} c_uv ψ(x_v)).
(33) Here, c_uv specifies the importance of node v to node u's representation. It is a constant
that often directly depends on the entries in A representing the structure of the graph."
p. 78 (PDF 82): "permutation invariance is ensured by aggregating features from X_{N_u}
(potentially transformed, by means of some function ψ) with some permutation-invariant function
⊕, and then updating the features of node u, by means of some function φ."

Given the current node states `h : V → H`, the output at node `u` is
`φ (h u) (agg {{ κ (h u) (h v) |N_u| |N_v| • ψ (h v) : v ∈ N_u }})`.

**Formalization Note.** The coefficient is `c_uv = κ(h_u, h_v, |N_u|, |N_v|)` for an arbitrary
`κ`: a function of the two endpoints' current states and degrees (`|N_u|` is the size of the
neighbourhood (11)). This covers the coefficients the paper names (edge entries of `A`, the
Kipf–Welling normalisation `1/√(d_u d_v)`, mean aggregation `1/d_u`, Laplacian entries on edges,
the look-up table `c(x_u, x_v)`), but not coefficients that read global structure of `A`.
The aggregator `⊕` is an arbitrary function `agg` of the multiset of messages (every function of a
multiset is permutation-invariant). Messages live in a real vector space `M`. -/
def convLayer {V : Type*} [Fintype V] {H M A H' : Type*} [AddCommMonoid M] [Module ℝ M]
    (κ : H → H → ℕ → ℕ → ℝ) (ψ : H → M) (agg : Multiset M → A) (φ : H → A → H')
    (E : V → V → Prop) [DecidableRel E] (h : V → H) (u : V) : H' :=
  φ (h u) (agg ((nbhd E u).val.map
    (fun v => κ (h u) (h v) (nbhd E u).card (nbhd E v).card • ψ (h v))))

end GeometricDL.WL


