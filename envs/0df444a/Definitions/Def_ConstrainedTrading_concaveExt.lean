-- Prove2me | Definitions.Def_ConstrainedTrading_concaveExt
-- name    : ConstrainedTrading_concaveExt
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:19:38.596981+00:00
-- url     : https://prove2.me/theorems/716416ca-affd-45b3-8d27-8228b873c9e1
-- title:
--   Concave extension $\hat f$ of a discrete function
-- statement:
--   The **concave extension** of $f:\mathbb Z^E\to\mathbb R\cup\{-\infty\}$ is the function $\hat f:\mathbb R^E\to[-\infty,+\infty]$,
--   $$
--   \hat f(x)=\sup\Bigl\{\sum_{z\in S}\lambda_z f(z)\ :\ S\subseteq\mathbb Z^E\text{ finite},\ \lambda>0\text{ on }S,\ \sum_{z\in S}\lambda_z=1,\ \sum_{z\in S}\lambda_z z=x\Bigr\}.
--   $$
--   It is the smallest concave function above $f$ built from finite convex combinations; $\hat f(x)=-\infty$ when $x$ is not in the convex hull of $\operatorname{dom} f$. The relaxations studied in the paper (problem (2), Lemma 3.1, Problem EA) maximize concave extensions over a polymatroid.
--
--   **Formalization Note** The paper defines the convex extension with a min (Definition 2.8) and the concave extension by negation (Definition 2.9). Here the concave case is a supremum in `EReal`, since a general $f$ need not attain it; the supremum of the empty set is $-\infty$. This is the convex-combination hull, not the closed concave closure.
-- source:
--   Kizilkale, Vohra, Constrained Trading Networks, arXiv:2008.09757v1, Definitions 2.8–2.9, p.5

import Mathlib
import Definitions.Def_ConstrainedTrading_IsConvexRep
import Definitions.Def_ConstrainedTrading_repValue

namespace ConstrainedTrading

/-- The **concave extension** `f̂ : ℝ^E → ℝ ∪ {±∞}` of `f : ℤ^E → ℝ ∪ {−∞}` (Kizilkale–Vohra,
*Constrained Trading Networks*, arXiv:2008.09757v1, Definitions 2.8–2.9, p.5):
`f̂(x) = sup { Σ_z λ_z f(z) : Σ_z λ_z z = x, λ ≥ 0, Σ_z λ_z = 1 }`, the supremum over all
finite convex representations of `x` by integer points.

**Formalization Note** Definition 2.9 defines `f̂` through the convex extension (Definition
2.8) of `−f`, written there with `min`; for the concave case this is the `max`, taken here as a
supremum in `EReal` because a general `f` need not attain it (reading R3 of the mission:
the convex-combination hull, not the closed concave closure). The supremum of the empty set is
`⊥ = −∞`, so `f̂(x) = −∞` for `x` outside the convex hull of `dom f`. Representations use finite
supports with positive weights (`IsConvexRep`), and values are computed by `repValue`. -/
noncomputable def concaveExt {E : Type*} (f : (E → ℤ) → WithBot ℝ) (x : E → ℝ) : EReal :=
  sSup {v : EReal | ∃ (S : Finset (E → ℤ)) (wt : (E → ℤ) → ℝ),
    IsConvexRep x S wt ∧ v = repValue f S wt}

end ConstrainedTrading


