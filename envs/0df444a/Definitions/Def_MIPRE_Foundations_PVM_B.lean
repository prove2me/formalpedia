-- Prove2me | Definitions.Def_MIPRE_Foundations_PVM_B
-- name    : MIPRE_Foundations_PVM_B
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T00:50:27.93763+00:00
-- url     : https://prove2.me/theorems/f7ce8299-58f7-439f-bb91-b72cb35e1787
-- title:
--   Definitions of PVM (addendum): Observables of a projective measurement A projective measurement `P : Λ → Matrix n n ℂ` and a weighting `ε : Λ → ℂ`…
-- statement:
--   The definitions of the module `MIPRE.Foundations.PVM` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Observables of a projective measurement. A projective measurement `P : Λ → Matrix n n ℂ` and a weighting `ε : Λ → ℂ` give the operator `pvmObs P ε = ∑_a ε a • P a`. The one fact worth isolating is that this is a **ring homomorphism** in `ε`: `pvmObs P ε * pvmObs P δ = pvmObs P (ε * δ)`, `pvmObs P 1 = 1`, because the projections are mutually orthogonal (`IsPVM.orthogonal`). Everything the rigidity arguments want about signed sums of a projective measurement follows: with `ε` valued in `{±1}`, `pvmObs P ε` is a self-adjoint reflection; two weightings of the *same* measurement commute, whatever…
--
--   This bundle **adds** the declarations below to the already published bundle `MIPRE_Foundations_PVM` of the same module, which the new statements of this upload need and the earlier bundle left out.
--
--   **Definitions** (1): `MIPRE.pvmObs` (`∑_a ε a • P a`, the operator a weighting of a projective measurement's outcomes defines.).
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.PVM` (`MIPRE/Foundations/PVM.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 1 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/PVM.lean

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/PVM.lean (delta bundle: declarations the new statements need that the published bundle Def_MIPRE_Foundations_PVM does not carry);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Definitions.Def_MIPRE_Foundations_PVM
import Theorems.Thm_MIPRE_IsPVM_orthogonal

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

namespace IsPVM

variable {P : Λ → Matrix n n ℂ}

end IsPVM

/-! ## The observable of a weighting -/

/-- `∑_a ε a • P a`, the operator a weighting of a projective measurement's outcomes
defines. -/
def pvmObs (P : Λ → Matrix n n ℂ) (ε : Λ → ℂ) : Matrix n n ℂ := ∑ a, ε a • P a

variable {P : Λ → Matrix n n ℂ}

end MIPRE

end


