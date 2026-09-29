-- Prove2me | Definitions.Def_Supermodularity_Monotonicity_IncreasingDifferencesOn
-- name    : Supermodularity_Monotonicity_IncreasingDifferencesOn
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-18T05:26:19.821713+00:00
-- url     : https://prove2.me/theorems/b6832073-b8e1-44aa-8009-4ef1e126203d
-- title:
--   Increasing differences of a function of two variables on a subset of a product
-- statement:
--   Let $X$ and $T$ be **partially ordered sets** and let $f : X \times T \to \mathbb{R}$ be a
--   real-valued function, viewed as a curried map $f(x,t)$, restricted to a subset $S \subseteq
--   X \times T$. For $t \in T$ write $S_t = \{x \in X : (x,t) \in S\}$ for the **section** of
--   $S$ at $t$. The function $f(x,t)$ has **increasing differences** in $(x,t)$ on $S$ if, for
--   every $t' \prec t''$ in $T$,
--
--   $$
--   x \;\longmapsto\; f(x,t'') - f(x,t')
--   $$
--
--   is monotone (order-preserving) as a function of $x$ on $S_{t'} \cap S_{t''}$. Equivalently,
--   for $x' \preceq x''$ both in $S_{t'} \cap S_{t''}$,
--
--   $$
--   f(x'',t'') - f(x'',t') \;\ge\; f(x',t'') - f(x',t').
--   $$
--
--   Increasing differences is Topkis's cardinal notion of **complementarity** between the
--   decision variable $x$ and the parameter $t$: the marginal gain from increasing $t$ is
--   itself increasing in $x$. Taking $S = X \times T$ (the whole product) recovers "$f$ has
--   increasing differences in $(x,t)$ on $X \times T$," the hypothesis used in Theorem 2.8.1
--   and (in its strict form) Theorem 2.8.4.
--
--   **Formalization Note** The definition is stated for an arbitrary subset $S$ of $X \times
--   T$ so that the same declaration also instantiates the book's general definition (Section
--   2.6.1) restricted to two of finitely many coordinates; this mission only uses the case
--   $S = \mathrm{Set.univ}$. Following the book's own convention, the outer quantification is
--   over the *strict* order $t' \prec t''$ on $T$ (with the inner monotonicity a *non-strict*
--   order-preservation in $x$); the case $t' = t''$ is vacuous content (the constant zero map
--   is trivially monotone) and is not part of the definition's substance.
-- source:
--   Topkis, Supermodularity and Complementarity, Princeton University Press, 2011, p. 42, Section 2.6.1 (definition of increasing differences)

import Mathlib

namespace Supermodularity.Monotonicity

/-- `IncreasingDifferencesOn f S` says the real-valued function `f : X → T → ℝ` has
increasing differences in `(x, t)` on `S ⊆ X × T`: for every `t' ≺ t''` in `T`, the map
`x ↦ f x t'' - f x t'` is monotone on the intersection of the sections of `S` at `t'`
and at `t''`. -/
def IncreasingDifferencesOn {X T : Type*} [PartialOrder X] [PartialOrder T]
    (f : X → T → ℝ) (S : Set (X × T)) : Prop :=
  ∀ ⦃t' t'' : T⦄, t' < t'' →
    MonotoneOn (fun x : X => f x t'' - f x t')
      ({x : X | (x, t') ∈ S} ∩ {x : X | (x, t'') ∈ S})

end Supermodularity.Monotonicity


