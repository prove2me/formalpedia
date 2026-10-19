-- Prove2me | Definitions.Def_MIPRE_Foundations_POVMValue
-- name    : MIPRE_Foundations_POVMValue
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-16T23:08:33.017912+00:00
-- url     : https://prove2.me/theorems/2257bf95-7d65-4c0c-9bd6-a7687cc70fa4
-- title:
--   Definitions of POVMValue: The value of a POVM strategy, and its conditional failures `MIPRE.TensorProductStrategy` is projective by construction,…
-- statement:
--   The definitions of the module `MIPRE.Foundations.POVMValue` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The value of a POVM strategy, and its conditional failures. `MIPRE.TensorProductStrategy` is projective by construction, which is the right definition of the quantum value (`lem:povm-value-eq` says allowing POVMs changes nothing). But a *soundness* argument often has to start from an arbitrary POVM strategy --- blueprint `lem:ms-direct-anticomm` is stated for one, and its whole point is that no projectivity is assumed --- so this file gives the unbundled value of a POVM strategy and the conditional failure probabilities that soundness arguments actually consume. Nothing here is bundled into a…
--
--   **Definitions** (4): `MIPRE.bornProb` (`⟨ψ| E_A ⊗ E_B |ψ⟩`, the Born-rule probability of an outcome pair.); `MIPRE.condFail` (The failure probability *conditioned* on the question pair `(x, y)`.); `MIPRE.condWin` (The accepted probability at a fixed question pair.); `MIPRE.povmValue` (**The value of a POVM strategy**: the average over question pairs of the accepted probability.).
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.POVMValue` (`MIPRE/Foundations/POVMValue.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 1 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/POVMValue.lean

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/POVMValue.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.ENat.Lattice
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Definitions.Def_MIPRE_Foundations_Games

/-!
# The value of a POVM strategy, and its conditional failures

`MIPRE.TensorProductStrategy` is projective by construction, which is the right definition of
the quantum value (`lem:povm-value-eq` says allowing POVMs changes nothing). But a *soundness*
argument often has to start from an arbitrary POVM strategy --- blueprint
`lem:ms-direct-anticomm` is stated for one, and its whole point is that no projectivity is
assumed --- so this file gives the unbundled value of a POVM strategy and the conditional
failure probabilities that soundness arguments actually consume.

Nothing here is bundled into a structure: the data is a state and two question-indexed families
of POVMs on arbitrary finite local spaces, which is how it arrives.

## Main definitions

- `MIPRE.bornProb`: `⟨ψ| E_A ⊗ E_B |ψ⟩`, as a real;
- `MIPRE.povmValue`: the value of a POVM strategy;
- `MIPRE.condFail`: the failure probability *conditioned* on a question pair.

## Main statements

- `MIPRE.sum_bornProb`: the Born probabilities of a pair of POVMs sum to one on a unit vector;
- `MIPRE.one_sub_povmValue_eq`: the failure probability is the average of the conditional ones;
- `MIPRE.condFail_le_div`: a conditional failure is at most the failure probability divided by
  the question pair's weight. This is the step that turns "fails with probability `ε`" into a
  bound on each subtest, and the division by the weight is why soundness constants carry the
  number of subtests.
-/

noncomputable section

namespace MIPRE

open Finset Matrix Kronecker
open scoped ComplexOrder MatrixOrder

/-! ## Linearity of the quadratic form and of the Kronecker product

Mathlib states neither over a `Finset` sum. -/

/-! ## Born probabilities -/

variable {X Y A B : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]

/-- `⟨ψ| E_A ⊗ E_B |ψ⟩`, the Born-rule probability of an outcome pair. -/
def bornProb (ψ : dA × dB → ℂ) (EA : Matrix dA dA ℂ) (EB : Matrix dB dB ℂ) : ℝ :=
  (star ψ ⬝ᵥ ((EA ⊗ₖ EB) *ᵥ ψ)).re

/-! ## The value and the conditional failures -/

/-- The accepted probability at a fixed question pair. -/
def condWin (G : Game X Y A B) (ψ : dA × dB → ℂ) (MA : X → POVM A dA) (MB : Y → POVM B dB)
    (x : X) (y : Y) : ℝ :=
  ∑ a, ∑ b, (if G.D x y a b then 1 else 0)
    * bornProb ψ (((MA x).mats a).val) (((MB y).mats b).val)

/-- **The value of a POVM strategy**: the average over question pairs of the accepted
probability. For a projective strategy this is `TensorProductStrategy.value`. -/
def povmValue (G : Game X Y A B) (ψ : dA × dB → ℂ) (MA : X → POVM A dA)
    (MB : Y → POVM B dB) : ℝ :=
  ∑ x, ∑ y, G.μ x y * condWin G ψ MA MB x y

/-- The failure probability *conditioned* on the question pair `(x, y)`. -/
def condFail (G : Game X Y A B) (ψ : dA × dB → ℂ) (MA : X → POVM A dA) (MB : Y → POVM B dB)
    (x : X) (y : Y) : ℝ :=
  1 - condWin G ψ MA MB x y

variable {G : Game X Y A B} {ψ : dA × dB → ℂ} {MA : X → POVM A dA} {MB : Y → POVM B dB}

end MIPRE

end


