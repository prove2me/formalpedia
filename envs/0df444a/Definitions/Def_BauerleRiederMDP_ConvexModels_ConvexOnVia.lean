-- Prove2me | Definitions.Def_BauerleRiederMDP_ConvexModels_ConvexOnVia
-- name    : BauerleRiederMDP_ConvexModels_ConvexOnVia
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:22:48.1852+00:00
-- url     : https://prove2.me/theorems/b3f3c5f9-4f01-4dd1-83b2-e8bbc2957788
-- title:
--   Convexity of a $[-\infty,\infty)$-valued function on a subset of $\mathbb R^d$
-- statement:
--   Let $X$ be a set placed in a real vector space $V$ by a map $\iota$ (in this mission the inclusion $E\subset\mathbb R^d$, or $D_n\subset E\times A\subset\mathbb R^d\times\mathbb R^m$). A function $f:X\to[-\infty,\infty]$ is **convex on** $D\subseteq X$ if
--   $$
--   f(z)\le\alpha f(p)+(1-\alpha)f(q)
--   $$
--   whenever $p,q,z\in D$, $\alpha\in[0,1]$ and $\iota(z)=\alpha\iota(p)+(1-\alpha)\iota(q)$.
--
--   This is the notion of convexity used in §2.4.4 for value functions, which may take the value $-\infty$.
--
--   **Formalization Note** The right side is computed in `EReal` with $\alpha\cdot(-\infty)=-\infty$ for $\alpha>0$ and $0\cdot(-\infty)=0$; for functions without the value $+\infty$ this is convexity of the epigraph. The definition does not require $\iota(D)$ to be convex; the theorems assume it where the book does.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), §2.4.4, pp.34–38 (PDF pp.49–53): 'convex' for functions on $E\subset\mathbb R^d$ (no numbered definition)

import Mathlib

namespace BauerleRiederMDP.ConvexModels

/-- **Convexity of a `[−∞, ∞)`-valued function on a subset of `ℝ^d`** (Bäuerle & Rieder,
*Markov Decision Processes with Applications to Finance* (2011), §2.4.4, pp.34–38, PDF
pp.49–53, where `E ⊂ ℝ^d`, `A ⊂ ℝ^m` and "convex" is used without a numbered definition).
The points of `X` are placed in a real vector space `V` by `ι` (for `E ⊂ ℝ^d` the inclusion
`Subtype.val`; for `D_n ⊂ E × A` the inclusion `Prod.map Subtype.val Subtype.val` into
`ℝ^d × ℝ^m`). A function `f : X → [−∞, ∞]` is convex on `D ⊆ X` if
`f(z) ≤ α f(p) + (1 − α) f(q)` whenever `p, q, z ∈ D`, `α ∈ [0, 1]` and
`ι(z) = α ι(p) + (1 − α) ι(q)`.

**Formalization Note.** The right side is computed in `EReal` with real scalars cast into
`EReal`, so `α · (−∞) = −∞` for `α > 0` and `0 · (−∞) = 0`. For functions with values in
`[−∞, ∞)` (no `+∞`) this is the usual convexity of an extended-real function, i.e. convexity
of its epigraph; the value `−∞` is allowed, as in the book's `IM(E)`. The definition does not
require `ι '' D` to be convex: where the book says "`v` is convex" the underlying set is
convex by the standing hypotheses (e.g. "E is convex"). -/
def ConvexOnVia {X V : Type*} [AddCommGroup V] [Module ℝ V] (ι : X → V) (D : Set X)
    (f : X → EReal) : Prop :=
  ∀ ⦃p⦄, p ∈ D → ∀ ⦃q⦄, q ∈ D → ∀ ⦃z⦄, z ∈ D → ∀ ⦃α β : ℝ⦄, 0 ≤ α → 0 ≤ β → α + β = 1 →
    ι z = α • ι p + β • ι q → f z ≤ (α : EReal) * f p + (β : EReal) * f q

end BauerleRiederMDP.ConvexModels


