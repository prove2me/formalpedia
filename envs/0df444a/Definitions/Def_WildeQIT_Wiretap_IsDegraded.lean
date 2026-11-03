-- Prove2me | Definitions.Def_WildeQIT_Wiretap_IsDegraded
-- name    : WildeQIT_Wiretap_IsDegraded
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T04:27:37.735864+00:00
-- url     : https://prove2.me/theorems/1a36682c-40c1-423a-beed-7527652dd67b
-- title:
--   Physically degraded wiretap channel $X\to Y\to Z$
-- statement:
--   A wiretap channel $N\equiv p_{Y,Z|X}$ is **physically degraded** if $X\to Y\to Z$ is a Markov chain, that is, if there is a classical channel $p_{Z|Y}$ from Bob's alphabet to Eve's such that
--
--   $$
--   p_{Y,Z|X}(y,z|x)=p_{Z|Y}(z|y)\,p_{Y|X}(y|x)\qquad\text{for all }x,y,z,
--   $$
--
--   where $p_{Y|X}(y|x)=\sum_z p_{Y,Z|X}(y,z|x)$ is Bob's marginal channel. Bob can then simulate Eve's channel $p_{Z|X}(z|x)=\sum_y p_{Z|Y}(z|y)p_{Y|X}(y|x)$ by processing his own output.
--
--   For degraded channels the auxiliary variable in the private information is unnecessary (Proposition 13.2.1).
--
--   **Formalization Note** Alphabets are finite types (the book's setting) and information is measured in bits ($\log_2$). Distributions are the published `WildeQIT.FinDist`, channels the published `WildeQIT.Channel`, and $I(\cdot\,;\cdot)$ is the published `WildeQIT.mutualInfo` of a joint distribution (first component against second).
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Section 13.2.2, p. 399 (definition of a physically degraded wiretap channel, eq. (13.72))

import Definitions.Def_WildeQIT_Wiretap_WiretapChannel

namespace WildeQIT.Wiretap

open WildeQIT

/-- **Physically degraded wiretap channel.**
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, §13.2.2, p. 399: a wiretap
channel is physically degraded if `X → Y → Z` is a Markov chain, that is, the channel factors as
`p_{Y,Z|X}(y, z|x) = p_{Z|Y}(z|y) p_{Y|X}(y|x)` for some channel `p_{Z|Y}` that Bob can apply to his
output to simulate Eve's channel.

`IsDegraded N` says that there is a classical channel `D` from Bob's alphabet to Eve's with
`N(y, z|x) = N_Y(y|x) · D(z|y)` for all `x, y, z`, where `N_Y(y|x) = ∑_z N(y, z|x)` is Bob's
marginal channel. -/
def IsDegraded {α β γ : Type} [Fintype β] [Fintype γ] (N : WiretapChannel α β γ) : Prop :=
  ∃ D : Channel β γ, ∀ x y z, (N x).prob (y, z) = (N x).fst.prob y * (D y).prob z

end WildeQIT.Wiretap


