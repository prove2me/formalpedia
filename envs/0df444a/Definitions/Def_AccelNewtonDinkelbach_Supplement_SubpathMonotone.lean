-- Prove2me | Definitions.Def_AccelNewtonDinkelbach_Supplement_SubpathMonotone
-- name    : AccelNewtonDinkelbach_Supplement_SubpathMonotone
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T01:01:05.126256+00:00
-- url     : https://prove2.me/theorems/10aa683b-452c-4e5f-b38c-f95cf1211e62
-- title:
--   Subpath monotonicity at a source node (Definition 4.9)
-- statement:
--   A sequence of paths $(P^{(1)},\ldots,P^{(\ell)})$ from $u$ has **subpath monotonicity at $u$** when, for $i<j$ and every shared node $v\ne u$,
--
--   $$\gamma(P^{(i)}_{uv})\le\gamma(P^{(j)}_{uv}).$$
--
--   Lean expresses $P_{uv}$ as the unique prefix ending at $v$; the paths are simple in every theorem that uses the predicate.
-- source:
--   Dadush, Koh, Natura, Végh, arXiv:2004.08634v4, Definition 4.9, p.17

import Mathlib
import Definitions.Def_AccelNewtonDinkelbach_Supplement_Grapevine

namespace AccelNewtonDinkelbach.Supplement

set_option autoImplicit false

namespace M2VPI

variable {n m ℓ : ℕ} {M : M2VPI n m} {A : Fin m → Prop} {u : Fin n}

/-- Definition 4.9, stated using the unique prefixes of simple paths. -/
def SubpathMonotone (P : Fin ℓ → M.SplitWalk A u) : Prop :=
  ∀ i j : Fin ℓ, i < j → ∀ v : SplitNode n, v ≠ some u →
    ∀ Qi Qj : M.SplitWalk A u,
      Qi.start = some u → Qi.finish = v → Qi.edges <+: (P i).edges →
      Qj.start = some u → Qj.finish = v → Qj.edges <+: (P j).edges →
      Qi.walkGain ≤ Qj.walkGain

end M2VPI

end AccelNewtonDinkelbach.Supplement


