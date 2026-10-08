-- Prove2me | Definitions.Def_MonotoneCompStatics_Monotonicity_StrictSingleCrossing
-- name    : MonotoneCompStatics_Monotonicity_StrictSingleCrossing
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:28:31.431875+00:00
-- url     : https://prove2.me/theorems/75c6b7e5-4e4b-4150-bc58-d81d300b9a69
-- title:
--   Strict single crossing property
-- statement:
--   Let $X$ and $T$ be partially ordered sets and $f:X\times T\to\mathbb R$. The **strict single crossing property in $(x;t)$** requires, whenever $x''<x'$ and $t''<t'$,
--
--   $$f(x'',t'')\le f(x',t'')\ \Longrightarrow\ f(x'',t')<f(x',t').$$
--
--   This strengthened condition makes every maximizing selection increase when the parameter increases.
--
--   **Formalization Note** The order comparisons $x''<x'$ and $t''<t'$ are strict, and $f$ is curried in Lean.
-- source:
--   Milgrom and Shannon, Monotone Comparative Statics, Econometrica 62 (1994), p. 160 (PDF 5), definition of strict single crossing

import Mathlib

namespace MonotoneCompStatics.Monotonicity

def StrictSingleCrossing {X T : Type*} [PartialOrder X] [PartialOrder T] (f : X → T → ℝ) : Prop :=
  ∀ ⦃x' x'' : X⦄, x'' < x' → ∀ ⦃t' t'' : T⦄, t'' < t' →
    f x'' t'' ≤ f x' t'' → f x'' t' < f x' t'

end MonotoneCompStatics.Monotonicity


