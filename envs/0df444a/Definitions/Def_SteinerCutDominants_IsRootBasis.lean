-- Prove2me | Definitions.Def_SteinerCutDominants_IsRootBasis
-- name    : SteinerCutDominants_IsRootBasis
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:17:49.31578+00:00
-- url     : https://prove2.me/theorems/4b08d2dc-df4b-4cfc-8621-bb2fc78dde54
-- title:
--   Root basis indexed by a family of sets
-- statement:
--   $\delta(S)$ ($S\in\mathcal L$) is a **root basis** of $c$: all $\delta(S)$ are roots of $c$, and the vectors $\chi(\delta(S))$, $S\in\mathcal L$, form a basis of $\mathbb R^{E(G)}$.
-- source:
--   Conforti, Kaibel, Steiner Cut Dominants, arXiv:2209.14802v2, §2, p.4; §4, p.7

import Mathlib
import Definitions.Def_SteinerCutDominants_IsRoot
import Definitions.Def_SteinerCutDominants_WSG_wR

namespace SteinerCutDominants

/-- `δ(S)` (`S ∈ 𝓛`) is a root basis: a basis of `ℝ^{E(G)}` consisting of roots of `c` (Conforti,
Kaibel, *Steiner Cut Dominants*, arXiv:2209.14802v2, §2, p.4). -/
def IsRootBasis (H : WSG) (L : Finset (Finset H.V)) : Prop :=
  (∀ S ∈ L, IsRoot H S) ∧
    LinearIndependent ℝ (fun S : L => cutVec H.G (S : Finset H.V)) ∧
    Submodule.span ℝ (Set.range fun S : L => cutVec H.G (S : Finset H.V)) = ⊤

end SteinerCutDominants


