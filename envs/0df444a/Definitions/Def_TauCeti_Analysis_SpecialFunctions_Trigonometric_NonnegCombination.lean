-- Prove2me | Definitions.Def_TauCeti_Analysis_SpecialFunctions_Trigonometric_NonnegCombination
-- name    : TauCeti_Analysis_SpecialFunctions_Trigonometric_NonnegCombination
-- status  : Definition
-- author  : @riccardo.brasca
-- created : 2026-09-29T19:31:10.606954+00:00
-- url     : https://prove2.me/theorems/9a55d032-8a7a-4a40-84f5-7f7397f4ab35
-- title:
--   Nonnegative trigonometric combinations
-- statement:
--   Given a finite index set $s$, real weights $c_i$, and natural frequencies $m_i$, define
--
--   $$
--   T(z)=\sum_{i\in s}c_i\operatorname{Re}(z^{m_i}).
--   $$
--
--   The boundary nonnegativity condition requires $T(z)\geq0$ whenever $|z|=1$. This packages the trigonometric positivity used for Euler products.
--
--   **Formalization Note.** These foundational declarations are transplanted from the Tau Ceti contributors' [original source](https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/Analysis/SpecialFunctions/Trigonometric/NonnegCombination.lean) (Apache-2.0, commit `948fe4751b1fe528b6d580c522ca5d743d47f185`), with compatibility adaptations for Lean 4.33.1. Mathematical proofs requiring separate theorem nodes are published separately.
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/Analysis/SpecialFunctions/Trigonometric/NonnegCombination.lean

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# Nonnegative trigonometric combinations

This file packages finite trigonometric combinations that are nonnegative on the complex unit
circle. It also transfers their pointwise nonnegativity to the closed unit disk and the Taylor
series of `-log (1 - z)`, giving a reusable logarithmic inequality.

## Main declarations

* `TauCeti.trigonometricCombination` is a finite weighted cosine combination.
* `TauCeti.IsNonnegativeTrigonometricCombination` asserts nonnegativity on the unit circle.
* `TauCeti.trigonometricCombination_nonneg_of_boundary` extends this nonnegativity to the closed
  unit disk.
* `TauCeti.sum_re_neg_log_one_sub_nonneg` transfers boundary nonnegativity to logarithms in the
  open unit disk.

## Provenance

The logarithmic transfer generalizes the private lemma `re_log_comb_nonneg'` in the
`DirichletCharacter` namespace of Mathlib's
`Mathlib/NumberTheory/LSeries/Nonvanishing.lean`, due to Michael Stoll and David Loeffler, from
the fixed `3-4-1` weights to an arbitrary finite nonnegative combination.

This is part of Layer 8.2 of `TauCetiRoadmap/ArithmeticDirichletSeries/README.md`.
-/

 section

namespace TauCeti

open Complex

noncomputable section

variable {ι : Type*}

/-- The real trigonometric combination with weights `c` and frequencies `m`, evaluated at a
complex phase `z`. On the unit circle, `(z ^ k).re` is a cosine. -/
def trigonometricCombination
    (s : Finset ι) (c : ι → ℝ) (m : ι → ℕ) (z : ℂ) : ℝ :=
  ∑ i ∈ s, c i * (z ^ m i).re



/-- The assertion that a finite trigonometric combination is nonnegative at every complex phase
on the unit circle. -/
abbrev IsNonnegativeTrigonometricCombination
    (s : Finset ι) (c : ι → ℝ) (m : ι → ℕ) : Prop :=
  ∀ z : ℂ, ‖z‖ = 1 → 0 ≤ trigonometricCombination s c m z

variable {s : Finset ι} {c : ι → ℝ} {m : ι → ℕ}





end

end TauCeti

end
end


