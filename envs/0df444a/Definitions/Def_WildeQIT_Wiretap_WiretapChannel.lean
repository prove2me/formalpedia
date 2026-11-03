-- Prove2me | Definitions.Def_WildeQIT_Wiretap_WiretapChannel
-- name    : WildeQIT_Wiretap_WiretapChannel
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T04:27:01.077331+00:00
-- url     : https://prove2.me/theorems/0d7a840f-297f-4d03-b5d8-22d06ea4c9bb
-- title:
--   Classical wiretap channel $p_{Y,Z|X}$
-- statement:
--   A **classical wiretap channel** $N$ is a conditional probability distribution
--
--   $$
--   p_{Y,Z|X}(y,z|x),\qquad x\in\mathcal X,\ y\in\mathcal Y,\ z\in\mathcal Z,
--   $$
--
--   with finite alphabets. Alice holds the input $X$, Bob receives $Y$, and the eavesdropper Eve receives $Z$; for each input letter $x$, $p_{Y,Z|X}(\cdot,\cdot|x)$ is a joint distribution of Bob's and Eve's outputs.
--
--   This is the three-party model of Section 13.2 on which the private information is defined.
--
--   **Formalization Note** Alphabets are finite types (the book's setting) and information is measured in bits ($\log_2$). Distributions are the published `WildeQIT.FinDist`, channels the published `WildeQIT.Channel`, and $I(\cdot\,;\cdot)$ is the published `WildeQIT.mutualInfo` of a joint distribution (first component against second). A wiretap channel is a classical channel from $\mathcal X$ to pairs $(y,z)\in\mathcal Y\times\mathcal Z$, Bob's output first.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Section 13.2, eq. (13.55), p. 396

import Definitions.Def_WildeQIT_Channel

namespace WildeQIT.Wiretap

open WildeQIT

/-- **A classical wiretap channel.**
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, §13.2, (13.55), p. 396: the
wiretap channel `N` has conditional probability density `p_{Y,Z|X}(y, z|x)`; Alice holds the
input `X`, Bob receives `Y` and Eve receives `Z`.

`WiretapChannel α β γ` is a classical channel from the input alphabet `α` to pairs
`(y, z) ∈ β × γ` (Bob's output first, Eve's second): `(N x).prob (y, z) = p_{Y,Z|X}(y, z|x)`. -/
abbrev WiretapChannel (α β γ : Type) [Fintype β] [Fintype γ] := Channel α (β × γ)

end WildeQIT.Wiretap


