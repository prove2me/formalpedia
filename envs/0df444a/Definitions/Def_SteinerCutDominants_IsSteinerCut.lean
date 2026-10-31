-- Prove2me | Definitions.Def_SteinerCutDominants_IsSteinerCut
-- name    : SteinerCutDominants_IsSteinerCut
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:14:20.273272+00:00
-- url     : https://prove2.me/theorems/1f08dd54-43e5-4607-926b-b34357e3c814
-- title:
--   $T$-Steiner cut
-- statement:
--   For a terminal set $T$, the cut $\delta(S)$ is a **$T$-Steiner cut** if
--   $$
--   T\cap S\neq\emptyset\quad\text{and}\quad T\setminus S\neq\emptyset .
--   $$
--   So a $T$-Steiner cut separates two terminals. For $T=\{s,t\}$ these are the $s$-$t$ cuts, and for $T=V(G)$ all cuts.
-- source:
--   Conforti, Kaibel, Steiner Cut Dominants, arXiv:2209.14802v2, §1, p.1

import Mathlib

namespace SteinerCutDominants

/-- `S` defines a `T`-Steiner cut: `T ∩ S ≠ ∅` and `T \ S ≠ ∅` (Conforti, Kaibel,
*Steiner Cut Dominants*, arXiv:2209.14802v2, §1, p.1). -/
def IsSteinerCut {V : Type} [DecidableEq V] (T S : Finset V) : Prop :=
  (T ∩ S).Nonempty ∧ (T \ S).Nonempty

end SteinerCutDominants


