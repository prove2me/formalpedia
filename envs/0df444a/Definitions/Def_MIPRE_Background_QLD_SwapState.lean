-- Prove2me | Definitions.Def_MIPRE_Background_QLD_SwapState
-- name    : MIPRE_Background_QLD_SwapState
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T01:43:16.977365+00:00
-- url     : https://prove2.me/theorems/9da99773-804e-4413-b143-e88ca4e8b16c
-- title:
--   Definitions of SwapState: The swap isometry's state estimate (`lem:qld-swap`, item 1) `MIPRE/Background/QLD/SwapUnitary.lean` proves the two…
-- statement:
--   The definitions of the module `MIPRE.Background.QLD.SwapState` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The swap isometry's state estimate (`lem:qld-swap`, item 1). `MIPRE/Background/QLD/SwapUnitary.lean` proves the two halves of item 1 separately: the algebra (`swapU_conj_wTilde_X`, `swapU_conj_wTilde_Z`: conjugation by the swap map carries the exact Pauli observables to bare generalized Paulis, with no error at all), the identity the estimate rests on (`twirl_mul_twirl`: the product of the two Weyl twirls is the maximally entangled projector), and the arithmetic that turns two near-invariances into a closeness (`norm_sub_sq_le_of_re_inner_ge`, `re_inner_ge_of_two_close`,…
--
--   **Definitions** (1): `MIPRE.QLD.auxVec` (The state the swap isometry lands on: an auxiliary vector on the two parties' non-ancilla registers, tensored with the maximally entangled…).
--
--   **Formalization Note** The bundle is the module `MIPRE.Background.QLD.SwapState` (`MIPRE/Background/QLD/SwapState.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 26 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/QLD/SwapState.lean; blueprint lem:qld-swap

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/QLD/SwapState.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Tactic.IntervalCases
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_Closeness
import Definitions.Def_MIPRE_Foundations_OpBound
import Definitions.Def_MIPRE_Foundations_OpBound_B
import Definitions.Def_MIPRE_Foundations_StateDistance
import Definitions.Def_MIPRE_Foundations_StateDistance_B
import Definitions.Def_MIPRE_Foundations_POVMValue
import Definitions.Def_MIPRE_Foundations_Sign
import Definitions.Def_MIPRE_Foundations_CrossConsistency
import Definitions.Def_MIPRE_Foundations_CrossConsistency_B
import Definitions.Def_MIPRE_Foundations_PVM
import Definitions.Def_MIPRE_Foundations_PVM_B
import Definitions.Def_MIPRE_Foundations_Commutation
import Definitions.Def_MIPRE_Foundations_Dilation
import Definitions.Def_MIPRE_Foundations_Expanded
import Definitions.Def_MIPRE_Foundations_LowDegree_SchwartzZippel
import Definitions.Def_MIPRE_Foundations_LowDegree_Anticomm
import Definitions.Def_MIPRE_Foundations_Weyl
import Definitions.Def_MIPRE_Foundations_Parseval
import Definitions.Def_MIPRE_Foundations_Linearity
import Definitions.Def_MIPRE_Foundations_Sandwich
import Definitions.Def_MIPRE_Foundations_WeylEPR
import Definitions.Def_MIPRE_Background_QLD_ExactPauli
import Definitions.Def_MIPRE_Background_QLD_SwapUnitary

/-!
# The swap isometry's state estimate (`lem:qld-swap`, item 1)

`MIPRE/Background/QLD/SwapUnitary.lean` proves the two halves of item 1 separately: the algebra
(`swapU_conj_wTilde_X`, `swapU_conj_wTilde_Z`: conjugation by the swap map carries the exact Pauli
observables to bare generalized Paulis, with no error at all), the identity the estimate rests on
(`twirl_mul_twirl`: the product of the two Weyl twirls is the maximally entangled projector), and
the arithmetic that turns two near-invariances into a closeness
(`norm_sub_sq_le_of_re_inner_ge`, `re_inner_ge_of_two_close`, `norm_sub_normalize_sq_le`). What it
does not do is put them together on a state, because `twirl_mul_twirl` lives on the two ancilla
halves alone and the state lives on all four registers.

This file is that assembly. On the space `R x (T x T)` --- the two parties' non-ancilla registers
as one index `R`, their two ancilla halves adjacent as `T x T` --- the twirls act through `bOp`,
their product is `bOp eprProj` by `twirl_mul_twirl`, and the range of `bOp eprProj` is exactly the
vectors of the form `aux (x) EPR` (`bOp_eprProj_mulVec`). So a state that is nearly invariant under
both twirls is close to a product `aux (x) EPR`, which is item 1.

The self-consistency that supplies the two near-invariances --- `W~^e(u-tilde)` on one party agrees
with `W~^e(u-tilde)` on the other, on average over a *uniform* `u-tilde` --- is the paper's second
item of `lem:qld-construct-the-paulis` and is a hypothesis here, not a conclusion. It is the piece
of stage 5 that remains.
-/

noncomputable section

namespace MIPRE.QLD

open Finset Matrix MIPRE MIPRE.Weyl
open scoped Kronecker ComplexOrder MatrixOrder

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ## The twirl is a self-adjoint contraction -/

section Twirl

variable {N : Type*} [Fintype N]

end Twirl

section TwirlWeyl

end TwirlWeyl

/-! ## The maximally entangled projector -/

section EprProj

end EprProj

/-! ## Item 1 of `lem:qld-swap` -/

section Item1

variable {R : Type*} [Fintype R] [DecidableEq R]

/-- The state the swap isometry lands on: an auxiliary vector on the two parties' non-ancilla
registers, tensored with the maximally entangled pair. -/
def auxVec (aux : R → ℂ) : R × ((n → F) × (n → F)) → ℂ := fun p => aux p.1 * epr p.2

end Item1

/-! ## The combinatorial core of the self-consistency chain

`lem:qld-pauli-selfcons` --- the paper's second item of `lem:qld-construct-the-paulis`, and the
hypothesis of `exists_auxVec_close` above --- turns on one algebraic identity, the justification of
its display `eq:qld-pulling-2b`: the syndrome projector at the probe `u-tilde` and the syndrome
projector at the probe `ind_m(u)` multiply to the projector onto the outcomes satisfying both
conditions. That identity is here; the approximation steps around it are not. -/

section Joint

end Joint

end MIPRE.QLD

end


