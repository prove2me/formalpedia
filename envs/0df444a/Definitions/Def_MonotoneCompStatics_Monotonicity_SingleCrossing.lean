-- Prove2me | Definitions.Def_MonotoneCompStatics_Monotonicity_SingleCrossing
-- name    : MonotoneCompStatics_Monotonicity_SingleCrossing
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:28:28.352994+00:00
-- url     : https://prove2.me/theorems/8e16cf63-d48e-45ff-b772-cde90ef41279
-- title:
--   Single crossing property in choice and parameter
-- statement:
--   Let $X$ and $T$ be partially ordered sets and $f:X\times T\to\mathbb R$. The **single crossing property in $(x;t)$** says that, whenever $x''<x'$ and $t''<t'$, both preference implications hold:
--
--   $$f(x'',t'')<f(x',t'')\ \Longrightarrow\ f(x'',t')<f(x',t'),\qquad
--   f(x'',t'')\le f(x',t'')\ \Longrightarrow\ f(x'',t')\le f(x',t').$$
--
--   Thus an increase in the parameter preserves both strict and weak rankings of ordered choices.
--
--   **Formalization Note** Lean represents $f$ in curried form, $f:X\to T\to\mathbb R$. Both comparisons of distinct choices and parameters are strict; the two preference implications differ in strength.
-- source:
--   Milgrom and Shannon, Monotone Comparative Statics, Econometrica 62 (1994), p. 160 (PDF 5), definition of single crossing

import Mathlib

namespace MonotoneCompStatics.Monotonicity

def SingleCrossing {X T : Type*} [PartialOrder X] [PartialOrder T] (f : X → T → ℝ) : Prop :=
  ∀ ⦃x' x'' : X⦄, x'' < x' → ∀ ⦃t' t'' : T⦄, t'' < t' →
    (f x'' t'' < f x' t'' → f x'' t' < f x' t') ∧
    (f x'' t'' ≤ f x' t'' → f x'' t' ≤ f x' t')

end MonotoneCompStatics.Monotonicity


