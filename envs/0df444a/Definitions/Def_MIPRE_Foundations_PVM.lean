-- Prove2me | Definitions.Def_MIPRE_Foundations_PVM
-- name    : MIPRE_Foundations_PVM
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-16T23:08:30.243985+00:00
-- url     : https://prove2.me/theorems/114afc74-68e8-4b94-b4f9-47575157bf0b
-- title:
--   Definitions of PVM: Observables of a projective measurement A projective measurement `P : Λ → Matrix n n ℂ` and a weighting `ε : Λ → ℂ`…
-- statement:
--   The definitions of the module `MIPRE.Foundations.PVM` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Observables of a projective measurement. A projective measurement `P : Λ → Matrix n n ℂ` and a weighting `ε : Λ → ℂ` give the operator `pvmObs P ε = ∑_a ε a • P a`. The one fact worth isolating is that this is a **ring homomorphism** in `ε`: `pvmObs P ε * pvmObs P δ = pvmObs P (ε * δ)`, `pvmObs P 1 = 1`, because the projections are mutually orthogonal (`IsPVM.orthogonal`). Everything the rigidity arguments want about signed sums of a projective measurement follows: with `ε` valued in `{±1}`, `pvmObs P ε` is a self-adjoint reflection; two weightings of the *same* measurement commute, whatever…
--
--   **Definitions** (1): `MIPRE.IsPVM` (A **projective measurement** on `Matrix n n ℂ`: self-adjoint idempotents summing to one.).
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.PVM` (`MIPRE/Foundations/PVM.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/PVM.lean

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/PVM.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef

/-!
# Observables of a projective measurement

A projective measurement `P : Λ → Matrix n n ℂ` and a weighting `ε : Λ → ℂ` give the operator
`pvmObs P ε = ∑_a ε a • P a`. The one fact worth isolating is that this is a **ring
homomorphism** in `ε`:

`pvmObs P ε * pvmObs P δ = pvmObs P (ε * δ)`,  `pvmObs P 1 = 1`,

because the projections are mutually orthogonal (`IsPVM.orthogonal`). Everything the rigidity
arguments want about signed sums of a projective measurement follows: with `ε` valued in
`{±1}`, `pvmObs P ε` is a self-adjoint reflection; two weightings of the *same* measurement
commute, whatever they are; and if `ε δ η` is constantly `s` then `pvmObs P ε * pvmObs P δ *
pvmObs P η = s • 1` exactly.

That last one is what a linear-constraint-system game's Alice-side dilation buys: the three
reflections of one constraint commute and multiply to the constraint's sign, with no error
term. Blueprint `lem:ms-direct-anticomm` is the consumer.
-/

noncomputable section

namespace MIPRE

open Finset Matrix
open scoped ComplexOrder MatrixOrder

variable {n Λ : Type*} [Fintype n] [DecidableEq n] [Fintype Λ] [DecidableEq Λ]

/-- A **projective measurement** on `Matrix n n ℂ`: self-adjoint idempotents summing to one.
Stated as a predicate on a bare family rather than a bundled structure, because the families
this is applied to arrive from `exists_projective_dilation` in exactly this shape. -/
structure IsPVM (P : Λ → Matrix n n ℂ) : Prop where
  /-- Each element is self-adjoint. -/
  isSelfAdjoint : ∀ a, (P a)ᴴ = P a
  /-- Each element is idempotent. -/
  idem : ∀ a, P a * P a = P a
  /-- The elements sum to one. -/
  sum_eq_one : ∑ a, P a = 1

namespace IsPVM

variable {P : Λ → Matrix n n ℂ}

end IsPVM

/-! ## The observable of a weighting -/

variable {P : Λ → Matrix n n ℂ}

end MIPRE

end


