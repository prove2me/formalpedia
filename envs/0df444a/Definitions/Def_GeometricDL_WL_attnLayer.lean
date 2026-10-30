-- Prove2me | Definitions.Def_GeometricDL_WL_attnLayer
-- name    : GeometricDL_WL_attnLayer
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:20:22.508131+00:00
-- url     : https://prove2.me/theorems/2b27dc7d-2561-420c-aac3-159551aea26e
-- title:
--   Attentional GNN layer, eq. (34)
-- statement:
--   Let $G=(V,E)$ be a finite graph and $h:V\to H$ the current node states. An **attentional GNN layer** maps $h$ to
--
--   $$h'_u=\varphi\Big(h_u,\ \bigoplus_{v\in N_u} a(h_u,h_v)\,\psi(h_v)\Big),$$
--
--   where $a:H\times H\to\mathbb R$ is an attention mechanism computing the coefficients $\alpha_{uv}=a(h_u,h_v)$, $\psi:H\to M$ maps into a real vector space, $\bigoplus$ is a permutation-invariant aggregator, and $\varphi$ is the update.
--
--   In the attentional flavour the weights depend on the features of the two endpoints, rather than being fixed in advance.
--
--   **Formalization Note** The aggregator is an arbitrary function of the multiset of messages; the neighbourhood is (11).
-- source:
--   Bronstein, Bruna, Cohen & Veličković, Geometric Deep Learning, arXiv:2104.13478v2, §5.3, eq. (34), printed p. 79 (PDF p. 83)

import Mathlib
import Definitions.Def_GeometricDL_WL_nbhd

namespace GeometricDL.WL

/-- **Attentional GNN layer, eq. (34).**
Bronstein, Bruna, Cohen & Veličković, *Geometric Deep Learning*, arXiv:2104.13478v2, §5.3,
eq. (34), printed p. 79 (PDF p. 83): "In the attentional flavour … the interactions are implicit
h_u = φ(x_u, ⊕_{v∈N_u} a(x_u, x_v)ψ(x_v)). (34) Here, a is a learnable self-attention mechanism that
computes the importance coefficients α_uv = a(x_u, x_v) implicitly."

Given the current node states `h : V → H`, the output at node `u` is
`φ (h u) (agg {{ a (h u) (h v) • ψ (h v) : v ∈ N_u }})`.

**Formalization Note.** `agg` is an arbitrary function of the multiset of messages (the
permutation-invariant `⊕`); messages live in a real vector space `M`; the neighbourhood is (11). -/
def attnLayer {V : Type*} [Fintype V] {H M A H' : Type*} [AddCommMonoid M] [Module ℝ M]
    (a : H → H → ℝ) (ψ : H → M) (agg : Multiset M → A) (φ : H → A → H')
    (E : V → V → Prop) [DecidableRel E] (h : V → H) (u : V) : H' :=
  φ (h u) (agg ((nbhd E u).val.map (fun v => a (h u) (h v) • ψ (h v))))

end GeometricDL.WL


