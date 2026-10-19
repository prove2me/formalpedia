-- Prove2me | Definitions.Def_MIPRE_Foundations_Closeness
-- name    : MIPRE_Foundations_Closeness
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-16T23:08:40.475582+00:00
-- url     : https://prove2.me/theorems/448edf5e-b2db-404f-b031-33606584fada
-- title:
--   Definitions of Closeness: The Hilbert--Schmidt closeness calculus Every soundness argument in the pipeline compares two families of operators in…
-- statement:
--   The definitions of the module `MIPRE.Foundations.Closeness` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The Hilbert--Schmidt closeness calculus. Every soundness argument in the pipeline compares two families of operators in the *state-dependent* distance `∑_a ‖(M_a - N_a)|ψ⟩‖²` and then passes from closeness of the families to closeness of the values, losing a square root. For a *synchronous* strategy the state is the normalized trace itself, so that distance is the normalized Hilbert--Schmidt distance of `MIPRE/Foundations/Distances.lean`, and the whole calculus follows from Cauchy--Schwarz for `MIPRE.hsInner`. This file is that calculus, and nothing about games. * `MIPRE.ntr` — the real part…
--
--   **Definitions** (1): `MIPRE.ntr` (The real part of the dimension-normalized trace, `τ(M) = Tr(M)/d`.).
--
--   **Embedded lemmas** (1): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `ntr_zero`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.Closeness` (`MIPRE/Foundations/Closeness.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 2 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Closeness.lean

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Closeness.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.ENat.Lattice
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances

/-!
# The Hilbert--Schmidt closeness calculus

Every soundness argument in the pipeline compares two families of operators in the
*state-dependent* distance `∑_a ‖(M_a - N_a)|ψ⟩‖²` and then passes from closeness of the
families to closeness of the values, losing a square root. For a *synchronous* strategy the
state is the normalized trace itself, so that distance is the normalized Hilbert--Schmidt
distance of `MIPRE/Foundations/Distances.lean`, and the whole calculus follows from
Cauchy--Schwarz for `MIPRE.hsInner`.

This file is that calculus, and nothing about games.

* `MIPRE.ntr` — the real part of the normalized trace `Tr(M)/d`, with the identities the
  arguments use: additive, tracial (`ntr_mul_comm`), `ntr 1 = 1`;
* `hsNormSq_add`, `hsNormSq_sub` — the parallelogram expansion, which is where the cross term
  `2⟨A, B⟩` that Cauchy--Schwarz then bounds comes from;
* `re_hsInner_le`, `abs_re_hsInner_le` — **Cauchy--Schwarz** for the normalized
  Hilbert--Schmidt inner product;
* `sum_abs_re_hsInner_le` — Cauchy--Schwarz once more, over a finite index set: the form the
  arguments actually use, with the two sums of squared norms on the right;
* `sum_mul_sqrt_le` — the averaging step `𝔼 √f ≤ √(𝔼 f)`, again Cauchy--Schwarz.

## Implementation notes

`hsInner A B = τ(Aᴴ B)` is the inner product of a genuine inner product space (Mathlib's
`Matrix.toMatrixInnerProductSpace` at the identity), but that structure is a
`noncomputable def` rather than an instance, so using it would mean carrying `letI` through
every statement. Cauchy--Schwarz is instead proved here from the entrywise formula and
`Real.sum_sqrt_mul_sqrt_le`, which is the same proof and costs one lemma.
-/

namespace MIPRE

open Finset ComplexOrder Matrix

variable {n : Type*} [Fintype n]

/-! ## The normalized trace as a real number -/

/-- The real part of the dimension-normalized trace, `τ(M) = Tr(M)/d`. Outcome probabilities
of a synchronous strategy are values of this, and so is every quantity the closeness calculus
manipulates. -/
noncomputable def ntr (M : Matrix n n ℂ) : ℝ := M.trace.re / (Fintype.card n : ℝ)

@[simp] theorem ntr_zero : ntr (0 : Matrix n n ℂ) = 0 := by simp [ntr]

/-! ## The Hilbert--Schmidt inner product, in terms of `ntr` -/

/-! ## Cauchy--Schwarz -/

/-! ## Projections

A *projection* here is what a projective measurement's operators are: self-adjoint and
idempotent. Under the normalized trace the squared Hilbert--Schmidt norm of a projection, and
of a product of two projections, collapses to a normalized trace, which is what turns the
closeness calculus into statements about outcome probabilities. -/

section OneSub

variable [DecidableEq n]

end OneSub

/-! ## The closeness estimate

The one inequality the soundness argument needs, and the only place a Cauchy--Schwarz is
spent before the value comparison. Three families of projections: `O` a measurement, and `C`,
`D` such that the products `C D` are a measurement too. Then the squared distance between
`C_i D_i` and `O_i` is bounded by three times the two *disagreements* `τ(O_i(1 - D_i))` and
`τ(O_i(1 - C_i))` --- linearly, with no square root. Writing `C_i O_i = O_i - X_i` and
`D_i O_i = O_i - Y_i`, the two disagreements are exactly `∑ ‖X_i‖²` and `∑ ‖Y_i‖²`, and the
only term that is not one of them is `∑ ⟨Y_i, X_i⟩`, which Cauchy--Schwarz and the
arithmetic-geometric mean inequality bound by half their sum. -/

section Estimate

variable [DecidableEq n]

end Estimate

/-! ## The averaging step -/

end MIPRE


