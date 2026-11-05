-- Prove2me | Definitions.Def_BauerleRiederMDP_ConvexModels_ConcaveOnVia
-- name    : BauerleRiederMDP_ConvexModels_ConcaveOnVia
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:22:48.554906+00:00
-- url     : https://prove2.me/theorems/ce424938-971c-4a5a-84b8-b15b401be940
-- title:
--   Concavity of a $[-\infty,\infty)$-valued function on a subset of $\mathbb R^d$
-- statement:
--   Let $X$ be placed in a real vector space $V$ by $\iota$. A function $f:X\to[-\infty,\infty]$ is **concave on** $D\subseteq X$ if
--   $$
--   \alpha f(p)+(1-\alpha)f(q)\le f(z)
--   $$
--   whenever $p,q,z\in D$, $\alpha\in[0,1]$ and $\iota(z)=\alpha\iota(p)+(1-\alpha)\iota(q)$.
--
--   This is the concavity used in Proposition 2.4.18 and Theorem 2.4.19, both for functions on $E$ and for functions of $(x,a)$ on $D_n$.
--
--   **Formalization Note** Computed in `EReal` ($\alpha\cdot(-\infty)=-\infty$ for $\alpha>0$, $0\cdot(-\infty)=0$); for $[-\infty,\infty)$-valued functions this is convexity of the hypograph.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), Proposition 2.4.18 and Theorem 2.4.19, pp.36–37 (PDF pp.51–52): 'concave' (no numbered definition)

import Mathlib

namespace BauerleRiederMDP.ConvexModels

/-- **Concavity of a `[−∞, ∞)`-valued function on a subset of `ℝ^d` or of `ℝ^d × ℝ^m`**
(Bäuerle & Rieder, *Markov Decision Processes with Applications to Finance* (2011), §2.4.4,
Proposition 2.4.18 and Theorem 2.4.19, pp.36–37, PDF pp.51–52, where "concave" is used
without a numbered definition). With the points of `X` placed in a real vector space `V` by
`ι`, a function `f : X → [−∞, ∞]` is concave on `D ⊆ X` if
`α f(p) + (1 − α) f(q) ≤ f(z)` whenever `p, q, z ∈ D`, `α ∈ [0, 1]` and
`ι(z) = α ι(p) + (1 − α) ι(q)`.

**Formalization Note.** Computed in `EReal` with real scalars cast into `EReal`
(`α · (−∞) = −∞` for `α > 0`, `0 · (−∞) = 0`). For `[−∞, ∞)`-valued functions this is
convexity of the hypograph; a point with value `−∞` imposes no constraint as an endpoint,
as in the usual convention. The definition does not itself require `ι '' D` to be convex. -/
def ConcaveOnVia {X V : Type*} [AddCommGroup V] [Module ℝ V] (ι : X → V) (D : Set X)
    (f : X → EReal) : Prop :=
  ∀ ⦃p⦄, p ∈ D → ∀ ⦃q⦄, q ∈ D → ∀ ⦃z⦄, z ∈ D → ∀ ⦃α β : ℝ⦄, 0 ≤ α → 0 ≤ β → α + β = 1 →
    ι z = α • ι p + β • ι q → (α : EReal) * f p + (β : EReal) * f q ≤ f z

end BauerleRiederMDP.ConvexModels


