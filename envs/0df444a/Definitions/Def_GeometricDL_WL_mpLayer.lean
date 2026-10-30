-- Prove2me | Definitions.Def_GeometricDL_WL_mpLayer
-- name    : GeometricDL_WL_mpLayer
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:20:53.228994+00:00
-- url     : https://prove2.me/theorems/7d546976-0940-4335-a17b-17b4fe6a136a
-- title:
--   Message-passing GNN layer, eq. (35)
-- statement:
--   Let $G=(V,E)$ be a finite graph and $h:V\to H$ the current node states. A **message-passing GNN layer** maps $h$ to
--
--   $$h'_u=\varphi\Big(h_u,\ \bigoplus_{v\in N_u}\psi(h_u,h_v)\Big),$$
--
--   where $\psi(h_u,h_v)$ is the message sent from $v$ to $u$, $\bigoplus$ is a permutation-invariant aggregator of the multiset of messages, and $\varphi$ is the update.
--
--   This is the most general of the three flavours: the message may depend arbitrarily on both endpoints.
--
--   **Formalization Note** Messages may lie in any type; the aggregator is an arbitrary function of the multiset of messages; the neighbourhood is (11).
-- source:
--   Bronstein, Bruna, Cohen & Veličković, Geometric Deep Learning, arXiv:2104.13478v2, §5.3, eq. (35), printed p. 79 (PDF p. 83)

import Mathlib
import Definitions.Def_GeometricDL_WL_nbhd

namespace GeometricDL.WL

/-- **Message-passing GNN layer, eq. (35).**
Bronstein, Bruna, Cohen & Veličković, *Geometric Deep Learning*, arXiv:2104.13478v2, §5.3,
eq. (35), printed p. 79 (PDF p. 83): "the message-passing flavour … amounts to computing
arbitrary vectors (“messages”) across edges, h_u = φ(x_u, ⊕_{v∈N_u} ψ(x_u, x_v)). (35) Here, ψ is a
learnable message function, computing v's vector sent to u".

Given the current node states `h : V → H`, the output at node `u` is
`φ (h u) (agg {{ ψ (h u) (h v) : v ∈ N_u }})`.

**Formalization Note.** `agg` is an arbitrary function of the multiset of messages (the
permutation-invariant `⊕`); messages may live in any type `M`; the neighbourhood is (11). -/
def mpLayer {V : Type*} [Fintype V] {H M A H' : Type*}
    (ψ : H → H → M) (agg : Multiset M → A) (φ : H → A → H')
    (E : V → V → Prop) [DecidableRel E] (h : V → H) (u : V) : H' :=
  φ (h u) (agg ((nbhd E u).val.map (fun v => ψ (h u) (h v))))

end GeometricDL.WL


