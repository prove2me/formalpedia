-- Prove2me | Definitions.Def_TauCeti_Analysis_PositiveDefinite_FourierAtom
-- name    : TauCeti_Analysis_PositiveDefinite_FourierAtom
-- status  : Definition
-- author  : @riccardo.brasca
-- created : 2026-09-29T19:26:56.440349+00:00
-- url     : https://prove2.me/theorems/48a45b6e-dea8-4777-a8c3-c9de497c0ec2
-- title:
--   Fourier atoms
-- statement:
--   For a real inner-product space $V$ and a frequency $q\in V$, the Fourier atom is the additive character
--
--   $$
--   v\longmapsto\exp\bigl(-2\pi i\langle v,q\rangle\bigr).
--   $$
--
--   It fixes the Fourier normalization used in the analytic argument.
--
--   **Formalization Note.** These foundational declarations are transplanted from the Tau Ceti contributors' [original source](https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/Analysis/PositiveDefinite/FourierAtom.lean) (Apache-2.0, commit `948fe4751b1fe528b6d580c522ca5d743d47f185`), with compatibility adaptations for Lean 4.33.1. Mathematical proofs requiring separate theorem nodes are published separately.
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/Analysis/PositiveDefinite/FourierAtom.lean

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Matrix.Order
import Mathlib.MeasureTheory.Function.L1Space.Integrable

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# Fourier atoms

This file records the spatial Fourier atom used by the positive-definite and Bochner APIs.
It uses Mathlib's `2π` Fourier convention.

## Main declarations

* `TauCeti.fourierAtom`: the spatial atom `v ↦ exp (-2πi⟪v, q⟫)`.
* `TauCeti.posSemidef_fourierAtom`: the subtraction kernel attached to a
  Fourier atom is positive definite.
* `TauCeti.continuous_fourierAtom`: Fourier atoms are continuous in the spatial variable.
* `TauCeti.norm_fourierAtom`: Fourier atoms have unit norm.
* `TauCeti.integrable_fourierAtom`: Fourier atoms are integrable against a finite measure.
* `TauCeti.fourierAtom_zero_left` and `TauCeti.fourierAtom_zero_right`: a Fourier atom is `1`
  when either argument is `0`.
-/

 section

open Complex ComplexConjugate
open scoped ComplexOrder

namespace TauCeti

variable {V : Type*} [SeminormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The Fourier atom at frequency `q`, using Mathlib's `2π` Fourier convention. -/
 noncomputable def fourierAtom (q : V) (v : V) : ℂ :=
  (Real.fourierChar (-(inner ℝ v q)) : ℂ)



















end TauCeti

end
end


