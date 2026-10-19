-- Prove2me | Definitions.Def_MIPRE_Foundations_Expanded
-- name    : MIPRE_Foundations_Expanded
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T01:40:00.348644+00:00
-- url     : https://prove2.me/theorems/8b2e54cc-1f56-44c7-85f3-f3a02fdd0e04
-- title:
--   Definitions of Expanded: The expanded state, and an inert ancilla The expansion stage of the Pauli appendix (`sec:expanding`) adjoins a…
-- statement:
--   The definitions of the module `MIPRE.Foundations.Expanded` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The expanded state, and an inert ancilla. The expansion stage of the Pauli appendix (`sec:expanding`) adjoins a maximally entangled pair of ancilla registers to each player and then **re-bipartitions**: Alice's party becomes her own register together with her half of the ancilla, and Bob's becomes his register together with the *other* half. This file is that construction, for an arbitrary ancilla state.
--
--   **Definitions** (3): `MIPRE.POVM.kron` (**The product of two POVMs**, on the two systems of one party: outcomes the pairs, elements the Kronecker products.); `MIPRE.expEquiv` (The reindexing that separates the two systems from the two parties.); `MIPRE.expVec` (**The expanded state**: the strategy's state on the original registers, tensored with an ancilla state whose two halves go to the two…).
--
--   **Embedded lemmas** (1): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `kron_mats`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.Expanded` (`MIPRE/Foundations/Expanded.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 13 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Expanded.lean; blueprint def:expanded-state

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Expanded.lean (definition bundle: declarations the uploaded statements rest on);
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
import Definitions.Def_MIPRE_Foundations_OpBound_B
import Definitions.Def_MIPRE_Foundations_StateDistance
import Definitions.Def_MIPRE_Foundations_StateDistance_B
import Definitions.Def_MIPRE_Foundations_POVMValue
import Definitions.Def_MIPRE_Foundations_Sign
import Definitions.Def_MIPRE_Foundations_CrossConsistency
import Definitions.Def_MIPRE_Foundations_CrossConsistency_B
import Definitions.Def_MIPRE_Foundations_PVM
import Definitions.Def_MIPRE_Foundations_PVM_B
import Theorems.Thm_MIPRE_IsPVM_coarse
import Theorems.Thm_MIPRE_POVM_posSemidef
import Theorems.Thm_MIPRE_kronecker_sum_right
import Theorems.Thm_MIPRE_sum_kronecker_left

/-!
# The expanded state, and an inert ancilla

The expansion stage of the Pauli appendix (`sec:expanding`) adjoins a maximally entangled pair of
ancilla registers to each player and then **re-bipartitions**: Alice's party becomes her own
register together with her half of the ancilla, and Bob's becomes his register together with the
*other* half. This file is that construction, for an arbitrary ancilla state.

## The one thing it has to support

Every statement of the expansion stage is a norm on the expanded state, and the operators that
appear are of the form `M (x) N` --- the strategy's own operator on the original register, the
ancilla's on the adjoined one. Two facts carry all of them:

* `mulVec_kron_expVec`: such an operator acts on a product state factor by factor, so the whole
  computation splits;
* `norm_evec_expVec`: the norm of a product state is the product of the norms.

Together they say that an operator with an **inert ancilla**, `M (x) Id`, has the same state-norm
on the expanded state as `M` has on the original one, provided the ancilla state is a unit vector
(`norm_stateVec_expVec_kron_one`). That is what lets a bound proved before the expansion be used
after it, which is how the expansion stage consumes `lem:qld-obs-commutation`.
-/

noncomputable section

namespace MIPRE

open Finset Matrix
open scoped Kronecker ComplexOrder MatrixOrder

variable {dA dB anc anc' : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
  [Fintype anc] [DecidableEq anc] [Fintype anc'] [DecidableEq anc']

set_option linter.unusedSectionVars false

/-- **The expanded state**: the strategy's state on the original registers, tensored with an
ancilla state whose two halves go to the two *different* parties. -/
def expVec (ψ : dA × dB → ℂ) (e : anc × anc' → ℂ) : (dA × anc) × (dB × anc') → ℂ :=
  fun p => ψ (p.1.1, p.2.1) * e (p.1.2, p.2.2)

/-- The reindexing that separates the two systems from the two parties. -/
def expEquiv (dA dB anc anc' : Type*) :
    ((dA × anc) × (dB × anc')) ≃ ((dA × dB) × (anc × anc')) where
  toFun p := ((p.1.1, p.2.1), (p.1.2, p.2.2))
  invFun q := ((q.1.1, q.2.1), (q.1.2, q.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

/-! ## Born probabilities on the expanded state

The expansion stage's consistency statements are about a measurement of product form, and what
they need is that its Born probabilities *factorize*. That is the same computation as
`mulVec_kron_expVec` with an operator on each party, plus the observation that both factors are
real because both operators are positive. -/

/-! ## Data processing, at the Born level

The state-dependent distance has **no** data-processing inequality --- NW19 states theirs for the
consistency distance and the remark following it gives a counterexample for `approx`. What is true,
and what every coarse-graining in the appendix uses, is that applying the *same* post-processing to
both players can only increase the probability that they agree. That is a statement about Born
probabilities, and it is proved here so that no consumer is tempted by the other form. -/

/-! ## The product measurement -/

/-- **The product of two POVMs**, on the two systems of one party: outcomes the pairs, elements the
Kronecker products. -/
def POVM.kron {ι κ : Type*} [Fintype ι] [Fintype κ] (P : POVM ι dA) (Q : POVM κ anc) :
    POVM (ι × κ) (dA × anc) where
  mats p := ⟨((P.mats p.1).val) ⊗ₖ ((Q.mats p.2).val), by
    rw [selfAdjoint.mem_iff, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_kronecker,
      ← Matrix.star_eq_conjTranspose, ← Matrix.star_eq_conjTranspose, (P.mats p.1).2,
      (Q.mats p.2).2]⟩
  nonneg p := Subtype.coe_le_coe.mp (Matrix.nonneg_iff_posSemidef.mpr
    ((P.posSemidef p.1).kronecker (Q.posSemidef p.2)))
  normalized := by
    apply Subtype.ext
    rw [AddSubmonoidClass.coe_finsetSum]
    show ∑ p : ι × κ, ((P.mats p.1).val) ⊗ₖ ((Q.mats p.2).val) = 1
    rw [Fintype.sum_prod_type]
    rw [show (∑ i : ι, ∑ j : κ, ((P.mats i).val) ⊗ₖ ((Q.mats j).val))
        = ∑ i : ι, ((P.mats i).val) ⊗ₖ (∑ j : κ, ((Q.mats j).val)) from
      Finset.sum_congr rfl fun i _ => (kronecker_sum_right _ _ _).symm]
    rw [show (∑ j : κ, ((Q.mats j).val)) = 1 from by
        rw [← AddSubmonoidClass.coe_finsetSum, Q.normalized]; rfl]
    rw [← sum_kronecker_left, show (∑ i : ι, ((P.mats i).val)) = 1 from by
        rw [← AddSubmonoidClass.coe_finsetSum, P.normalized]; rfl,
      Matrix.one_kronecker_one]

@[simp] theorem POVM.kron_mats {ι κ : Type*} [Fintype ι] [Fintype κ] (P : POVM ι dA)
    (Q : POVM κ anc) (p : ι × κ) :
    (((P.kron Q).mats p).val) = ((P.mats p.1).val) ⊗ₖ ((Q.mats p.2).val) := rfl

/-! ## Projectivity of the constructions

The expansion stage's measurements are products of a strategy measurement with an ancilla
measurement, coarse-grained by adding the two outcomes, and the arguments downstream need them to
be **projective**. Two closures give that: a product of projective measurements is projective, and
so is any coarse-graining of one (`IsPVM.coarse`). -/

end MIPRE

end


