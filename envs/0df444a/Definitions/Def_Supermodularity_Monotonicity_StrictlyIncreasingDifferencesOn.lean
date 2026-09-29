-- Prove2me | Definitions.Def_Supermodularity_Monotonicity_StrictlyIncreasingDifferencesOn
-- name    : Supermodularity_Monotonicity_StrictlyIncreasingDifferencesOn
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-18T05:26:40.197528+00:00
-- url     : https://prove2.me/theorems/cefe9829-d8b6-44b8-afae-00490b14a768
-- title:
--   Strictly increasing differences of a function of two variables on a subset of a product
-- statement:
--   With $X$, $T$, $f$, $S$ and the section $S_t$ as in `IncreasingDifferencesOn`, the
--   function $f(x,t)$ has **strictly increasing differences** in $(x,t)$ on $S$ if, for every
--   $t' \prec t''$ in $T$, the map
--
--   $$
--   x \;\longmapsto\; f(x,t'') - f(x,t')
--   $$
--
--   is *strictly* monotone as a function of $x$ on $S_{t'} \cap S_{t''}$: for $x' \prec x''$
--   both in $S_{t'} \cap S_{t''}$,
--
--   $$
--   f(x'',t'') - f(x'',t') \;>\; f(x',t'') - f(x',t').
--   $$
--
--   This is the strengthening of increasing differences used in Theorem 2.8.4, where it
--   upgrades the conclusion from "the optimal-solution sets are ordered by the induced set
--   order" to "every optimal solution at the larger parameter dominates every optimal solution
--   at the smaller one."
--
--   **Formalization Note** As with `IncreasingDifferencesOn`, the outer quantification over
--   $T$ is the strict order $t' \prec t''$, matching the book's own definition; only the case
--   $S = \mathrm{Set.univ}$ is used in this mission.
-- source:
--   Topkis, Supermodularity and Complementarity, Princeton University Press, 2011, p. 42, Section 2.6.1 (definition of increasing differences)

import Mathlib

namespace Supermodularity.Monotonicity

/-- `StrictlyIncreasingDifferencesOn f S` says the real-valued function `f : X → T → ℝ`
has strictly increasing differences in `(x, t)` on `S ⊆ X × T`: for every `t' ≺ t''` in
`T`, the map `x ↦ f x t'' - f x t'` is strictly monotone on the intersection of the
sections of `S` at `t'` and at `t''`. -/
def StrictlyIncreasingDifferencesOn {X T : Type*} [PartialOrder X] [PartialOrder T]
    (f : X → T → ℝ) (S : Set (X × T)) : Prop :=
  ∀ ⦃t' t'' : T⦄, t' < t'' →
    StrictMonoOn (fun x : X => f x t'' - f x t')
      ({x : X | (x, t') ∈ S} ∩ {x : X | (x, t'') ∈ S})

end Supermodularity.Monotonicity


