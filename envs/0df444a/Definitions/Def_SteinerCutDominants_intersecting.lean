-- Prove2me | Definitions.Def_SteinerCutDominants_intersecting
-- name    : SteinerCutDominants_intersecting
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:14:41.062715+00:00
-- url     : https://prove2.me/theorems/b114726b-6d91-49cb-8c60-7d2e42d72385
-- title:
--   The family $I(W,\mathcal L)$
-- statement:
--   For a family $\mathcal L$ of subsets of $V$ and $W\subseteq V$,
--   $$
--   I(W,\mathcal L)=\{L\in\mathcal L : W\text{ and }L\text{ intersect}\}.
--   $$
--   If $\mathcal L$ is laminar and $W\notin\mathcal L$, this is the subfamily that prevents $W$ from being added to $\mathcal L$ while maintaining laminarity.
-- source:
--   Conforti, Kaibel, Steiner Cut Dominants, arXiv:2209.14802v2, §3, p.6

import Mathlib

namespace SteinerCutDominants

/-- `I(W, 𝓛) = {L ∈ 𝓛 : W and L intersect}` (Conforti, Kaibel, *Steiner Cut Dominants*,
arXiv:2209.14802v2, §3, p.6). The filter condition is `Intersect W A`, spelled out. -/
def intersecting {V : Type} [DecidableEq V] (W : Finset V) (L : Finset (Finset V)) :
    Finset (Finset V) :=
  L.filter fun A => (W ∩ A).Nonempty ∧ (W \ A).Nonempty ∧ (A \ W).Nonempty

end SteinerCutDominants


