-- Prove2me | Definitions.Def_MIPRE_Foundations_Commutation
-- name    : MIPRE_Foundations_Commutation
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T00:54:35.3337+00:00
-- url     : https://prove2.me/theorems/396c3af1-b371-4402-a91c-c945cd2e80fb
-- title:
--   Definitions of Commutation: The commutation analysis Blueprint `lem:commutation-analysis` (the paper's, in `games.tex`), and the two facts it runs…
-- statement:
--   The definitions of the module `MIPRE.Foundations.Commutation` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The commutation analysis. Blueprint `lem:commutation-analysis` (the paper's, in `games.tex`), and the two facts it runs on. It is the step that turns *consistency with a joint measurement on the other side* into *approximate commutation on one side*, and it is the only place in the Pauli appendix where projectivity of a measurement is genuinely used.
--
--   **Definitions** (1): `MIPRE.IsPVM.toPOVM` (**A projective measurement, as a POVM.** The same bridge as `ProjectiveMeasurement.toPOVM`, for the bare-family form `IsPVM` that the…).
--
--   **Embedded lemmas** (1): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `toPOVM_mats`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.Commutation` (`MIPRE/Foundations/Commutation.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 8 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Commutation.lean; blueprint def:expanded-state

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Commutation.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Tactic.IntervalCases
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Foundations_Closeness
import Definitions.Def_MIPRE_Foundations_OpBound
import Definitions.Def_MIPRE_Foundations_StateDistance
import Definitions.Def_MIPRE_Foundations_POVMValue
import Definitions.Def_MIPRE_Foundations_CrossConsistency
import Definitions.Def_MIPRE_Foundations_PVM
import Theorems.Thm_MIPRE_IsPVM_nonneg

/-!
# The commutation analysis

Blueprint `lem:commutation-analysis` (the paper's, in `games.tex`), and the two facts it runs on.
It is the step that turns *consistency with a joint measurement on the other side* into
*approximate commutation on one side*, and it is the only place in the Pauli appendix where
projectivity of a measurement is genuinely used.

## The shape

Alice has two POVMs `A_b` and `C_c`; Bob has one **projective** measurement `P_{b,c}` whose
outcome is the pair. If each of Alice's is cross-party close to the corresponding marginal of
Bob's, then Alice's two commute on the state:

```
A_b (x) Id ~ Id (x) P_b   and   C_c (x) Id ~ Id (x) P_c    =>    [A_b, C_c] (x) Id ~ 0 .
```

The proof moves both products to the *same* operator on Bob's side, `Id (x) P_{b,c}`, and that is
where projectivity enters: for a projective measurement with a product outcome set the two
marginals commute and multiply to the joint element (`IsPVM.marg_mul_marg`). Nothing else about
`P` is used.

## What the steps need

Each step multiplies a known deviation by an operator *in front*. The fact that lets it is the
paper's `fact:add-a-proj`: if `sum_i F_i^dag F_i <= Id` then `sum_i ||F_i v||^2 <= ||v||^2`, so
putting a family in front of a deviation costs nothing and *adds* its index to the sum. For a
POVM that hypothesis is `A_b^2 <= A_b` and `sum_b A_b = Id`, with no projectivity
(`sum_aOp_conjTranspose_mul_self_le_one`).

The constant is `16 delta`: each side of the commutator reaches `Id (x) P_{b,c}` in two steps
(`4 delta` after one triangle inequality), and the commutator is one more triangle
(`2 * 4 + 2 * 4`). No square root anywhere.
-/

noncomputable section

namespace MIPRE

open Finset Matrix
open scoped ComplexOrder MatrixOrder

-- Every statement here mentions both factors of the joint space, and the two `DecidableEq`s are
-- needed for matrix multiplication on it; omitting them declaration by declaration would be a
-- dozen `omit` lines with no consumer.
set_option linter.unusedSectionVars false

/-! ## The quadratic form is monotone -/

section Qform

variable {N : Type*} [Fintype N] [DecidableEq N]

end Qform

/-! ## Adding an operator in front

`fact:add-a-proj`. Stated on the norm rather than on a distance, because that is the form both
uses need: the family in front contributes its own index to the sum, and the deviation it is
applied to does not change. -/

section AddInFront

variable {N : Type*} [Fintype N] [DecidableEq N]

end AddInFront

/-! ## A projective measurement is a POVM -/

/-- **A projective measurement, as a POVM.** The same bridge as
`ProjectiveMeasurement.toPOVM`, for the bare-family form `IsPVM` that the rigidity arguments
produce. -/
def IsPVM.toPOVM {n Λ : Type*} [Fintype n] [DecidableEq n] [Fintype Λ] [DecidableEq Λ]
    {P : Λ → Matrix n n ℂ} (h : IsPVM P) : POVM Λ n where
  mats a := ⟨P a, by
    rw [selfAdjoint.mem_iff, Matrix.star_eq_conjTranspose, h.isSelfAdjoint]⟩
  nonneg a := Subtype.coe_le_coe.mp (h.nonneg a)
  normalized := by
    apply Subtype.ext
    rw [AddSubmonoidClass.coe_finsetSum]
    exact h.sum_eq_one

@[simp] theorem IsPVM.toPOVM_mats {n Λ : Type*} [Fintype n] [DecidableEq n] [Fintype Λ]
    [DecidableEq Λ] {P : Λ → Matrix n n ℂ} (h : IsPVM P) (a : Λ) :
    ((h.toPOVM.mats a).val) = P a := rfl

/-! ## Replacing one side of a cross-party deviation -/

section TwoStep

variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]

end TwoStep

/-! ## Marginals of a coarse-grained POVM -/

section MapMarginal

variable {d : Type*} [Fintype d] [DecidableEq d]

end MapMarginal

/-! ## The two hypotheses of the steps, for the operators they are applied to -/

section Families

variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]

end Families

/-! ## The marginals of a projective measurement with a product outcome set -/

section Marginals

variable {N B C : Type*} [Fintype N] [DecidableEq N] [Fintype B] [DecidableEq B]
  [Fintype C] [DecidableEq C]

end Marginals

/-! ## The analysis

Stated for abstract families in one matrix algebra --- the two parties enter only through the
hypotheses `hcomm`, `hcomm'` (the factors commute) and `hmul`, `hmul'` (Bob's two marginals
multiply to the joint element). That keeps the algebra in a single type, and `commutation_analysis`
below is the instance where the families are `aOp` and `bOp` of a POVM and a projective
measurement. -/

section Analysis

variable {N : Type*} [Fintype N] [DecidableEq N] {B C : Type*} [Fintype B] [Fintype C]
  {v : N → ℂ} {δ : ℝ}

end Analysis

/-! ## The instance: a POVM pair on Alice against a projective measurement on Bob -/

section Instance

variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
  {B C : Type*} [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C]

/-! ### From the POVM elements to the observables

The last step of the paper's commuting case: expanding a two-outcome observable as `Id - 2 M_1`,
the commutator of two such observables is **exactly** four times the commutator of the two
`M_1`'s, because the identity commutes with everything. So the transfer costs a factor `16` in the
squared norm and no approximation at all. -/

end Instance

end MIPRE

end


