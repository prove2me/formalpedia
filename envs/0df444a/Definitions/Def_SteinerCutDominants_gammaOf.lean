-- Prove2me | Definitions.Def_SteinerCutDominants_gammaOf
-- name    : SteinerCutDominants_gammaOf
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:15:14.763157+00:00
-- url     : https://prove2.me/theorems/faa9a368-9b1c-4376-87a7-c68e6418ce3b
-- title:
--   The minimum cut weight $\gamma_a(G,T)$
-- statement:
--   For a vector $a$ of edge weights, $\gamma_a(G,T)$ is the minimum $a$-weight of a $T$-Steiner cut in $(G,T)$:
--   $$
--   \gamma_a(G,T)=\min\{a\cdot\chi(\delta(S)) : \delta(S)\text{ is a }T\text{-Steiner cut}\}.
--   $$
--   For $a\ge 0$, the largest $b$ for which $ax\ge b$ is valid for $\mathrm{CUT}_+(G,T)$ is $\gamma_a(G,T)$.
--
--   **Formalization Note** The minimum is a real `sInf` over the finite set of $T$-Steiner cuts. It is used only for $|T|\ge 2$, when that set is nonempty, so the infimum is attained.
-- source:
--   Conforti, Kaibel, Steiner Cut Dominants, arXiv:2209.14802v2, §2, p.4

import Mathlib
import Definitions.Def_SteinerCutDominants_cutVec
import Definitions.Def_SteinerCutDominants_IsSteinerCut

open Matrix

namespace SteinerCutDominants

/-- `γ_a(G, T)`: the minimum `a`-weight of a `T`-Steiner cut of `G` (Conforti, Kaibel,
*Steiner Cut Dominants*, arXiv:2209.14802v2, §2, p.4).

**Formalization Note** A real `sInf` over the image of the finite set of `T`-Steiner cuts. That set
is nonempty when `2 ≤ T.card`, the only case in which `gammaOf` is used, so the infimum is attained
and the junk value `sInf ∅ = 0` does not occur. -/
noncomputable def gammaOf {V : Type} [DecidableEq V] (G : SimpleGraph V) [Fintype G.edgeSet]
    (T : Finset V) (a : G.edgeSet → ℝ) : ℝ :=
  sInf ((fun S : Finset V => a ⬝ᵥ cutVec G S) '' {S | IsSteinerCut T S})

end SteinerCutDominants


