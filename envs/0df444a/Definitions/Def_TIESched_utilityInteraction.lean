-- Prove2me | Definitions.Def_TIESched_utilityInteraction
-- name    : TIESched_utilityInteraction
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:46:44.561413+00:00
-- url     : https://prove2.me/theorems/cef82d62-be3a-4b86-84d8-c28daeac55a6
-- title:
--   Utility interaction $V^J_i$
-- statement:
--   For a fractional mechanism family with normalized utilities $u$, a finite job set $J$, a report $p_J$ and a machine $i$, the **utility interaction** is
--   $$V^J_i(p_J)=\sum_{S\subseteq J}(-1)^{|J|-|S|}\,u^S_i(p_S),$$
--   with $u^\emptyset_i=0$. For example $V^{\{a,b\}}_i=u^{\{a,b\}}_i-u^{\{a\}}_i-u^{\{b\}}_i$. It is the utility counterpart of the allocation interaction; §5 shows it vanishes for $|J|\ge m$ after the padding and smoothing constructions.
-- source:
--   Wang, Xu, Zhang, Tight Analysis of Randomized Truthful Scheduling: An (m+1)/2 Lower Bound, arXiv:2611.05142 (artifact sha256 a89db2da…), §5.1, p.20

import Mathlib
import Definitions.Def_TIESched_interaction

set_option autoImplicit false

namespace TIESched

/-- **Utility interaction** of a mechanism family (arXiv:2611.05142, §5.1, p.20): for a finite job
set `J`, `V^J_i(p_J) = Σ_{S ⊆ J} (−1)^{|J|−|S|} u^S_i(p_S)`, where `u` is the normalized utility of
the family (p.7) and `u^∅_i = 0`.

**Formalization Note.** `u^S_i` is `normalizedUtility M S · i`, which is `0` on the empty job set
automatically; `p_S` is `restrictReport p S`. -/
noncomputable def utilityInteraction {m : ℕ} (M : FracMech m) (J : Finset ℕ) (p : Fin m → J → ℝ)
    (i : Fin m) : ℝ :=
  ∑ S ∈ J.powerset, (-1 : ℝ) ^ (J.card - S.card) * normalizedUtility M S (restrictReport p S) i

end TIESched


