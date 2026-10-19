-- Prove2me | Definitions.Def_MIPRE_Foundations_POVMMix
-- name    : MIPRE_Foundations_POVMMix
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T00:56:37.653986+00:00
-- url     : https://prove2.me/theorems/0d254b92-7db8-4944-a6a7-fb11396ae4ff
-- title:
--   Definitions of POVMMix: Mixtures and extensions of POVMs, and the agreement triangle Three constructions on bundled POVMs that the padded…
-- statement:
--   The definitions of the module `MIPRE.Foundations.POVMMix` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Mixtures and extensions of POVMs, and the agreement triangle. Three constructions on bundled POVMs that the padded strategy of the Pauli basis test's stage 4 needs, and one inequality. * `POVM.aOp` extends a POVM on `d` by the identity to `d × E`; `POVM.dirac a₀` answers `a₀` with certainty; `POVM.mix w Q` is a convex combination of POVMs with the same outcomes. A strategy that must be a *function of the question* while the analysis controls it *sample by sample* is a mixture over the samples producing the question, and the Born rule's linearity (`bornProb_mix_left`, `bornProb_mix_right`)…
--
--   **Definitions** (7): `MIPRE.POVM.aOp` (A POVM on `d`, extended by the identity to `d × E`.); `MIPRE.POVM.mix` (**A convex combination of POVMs** with the same outcomes, with real weights `w` summing to one.); `MIPRE.POVM.ofPosSemidef` (A POVM from a family of positive semidefinite matrices summing to the identity.); `MIPRE.agreeSum` (The agreement probability of two families of POVMs, one per party, on the same questions, averaged over the question distribution `μ`: the…); `MIPRE.weightA` (The weighted squared norm of Alice's measurement vectors, `∑_x μ_x ∑_a ‖(M^x_a ⊗ I)ψ‖²`.); `MIPRE.weightB` (Bob's version.); `MIPRE.xDev` (The weighted cross-party deviation of two families.).
--
--   **Embedded lemmas** (3): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `aOp_mats`, `mix_mats`, `ofPosSemidef_mats`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.POVMMix` (`MIPRE/Foundations/POVMMix.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 13 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/POVMMix.lean; blueprint lem:qld-global-setup, lem:qld-global-success

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/POVMMix.lean (definition bundle: declarations the uploaded statements rest on);
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
import Definitions.Def_MIPRE_Foundations_StateDistance
import Definitions.Def_MIPRE_Foundations_POVMValue
import Definitions.Def_MIPRE_Foundations_CrossConsistency
import Definitions.Def_MIPRE_Foundations_PVM
import Definitions.Def_MIPRE_Foundations_Commutation
import Definitions.Def_MIPRE_Foundations_Dilation
import Definitions.Def_MIPRE_Foundations_LowDegree_SchwartzZippel
import Definitions.Def_MIPRE_Foundations_Sandwich
import Theorems.Thm_MIPRE_POVM_posSemidef
import Theorems.Thm_MIPRE_POVM_sum_val
import Theorems.Thm_MIPRE_aOp_conjTranspose
import Theorems.Thm_MIPRE_aOp_sum

/-!
# Mixtures and extensions of POVMs, and the agreement triangle

Three constructions on bundled POVMs that the padded strategy of the Pauli basis test's stage 4
needs, and one inequality.

* `POVM.aOp` extends a POVM on `d` by the identity to `d × E`; `POVM.dirac a₀` answers `a₀` with
  certainty; `POVM.mix w Q` is a convex combination of POVMs with the same outcomes. A strategy
  that must be a *function of the question* while the analysis controls it *sample by sample* is
  a mixture over the samples producing the question, and the Born rule's linearity
  (`bornProb_mix_left`, `bornProb_mix_right`) turns a bound on the mixture into the average of the
  per-sample bounds.
* `agreeSum_triangle` is the paper's triangle-like inequality for the consistency relation
  (`fact:triangle-for-simeq`, item 1): if Alice's `A` agrees with Bob's `B`, Alice's `C` agrees
  with Bob's `B`, and Alice's `C` agrees with Bob's `D`, each with probability at least `1 - δ`,
  then Alice's `A` agrees with Bob's `D` with probability at least `1 - 11 δ`. No projectivity is
  assumed: for POVMs the agreement is not a squared distance, and the argument goes through the
  vectors `(R_a ⊗ I)|ψ⟩`, whose weighted squared norms are at most one and, by Cauchy--Schwarz
  against a partner they agree with, at least `1 - 2δ`. The paper pads these vectors to unit
  vectors and gets `9 δ`; the unpadded argument here costs the extra `2 δ` and needs no auxiliary
  space.
-/

noncomputable section

namespace MIPRE

open Finset Matrix Kronecker
open scoped ComplexOrder MatrixOrder

/-! ## Extension by the identity, and the deterministic POVM -/

section Lift

variable {A : Type*} [Fintype A] {d E : Type*} [Fintype d] [DecidableEq d] [Fintype E]
  [DecidableEq E]

/-- A POVM on `d`, extended by the identity to `d × E`. -/
def POVM.aOp (M : POVM A d) : POVM A (d × E) where
  mats a := ⟨MIPRE.aOp (M.mats a).val, by
    rw [selfAdjoint.mem_iff, Matrix.star_eq_conjTranspose, aOp_conjTranspose,
      ← Matrix.star_eq_conjTranspose, selfAdjoint.mem_iff.mp (M.mats a).prop]⟩
  nonneg a :=
    Subtype.coe_le_coe.mp (Matrix.nonneg_iff_posSemidef.mpr
      ((M.posSemidef a).kronecker Matrix.PosSemidef.one))
  normalized := by
    apply Subtype.ext
    rw [AddSubmonoidClass.coe_finsetSum]
    show ∑ a, MIPRE.aOp (M.mats a).val = 1
    rw [← aOp_sum, POVM.sum_val, aOp_one]

@[simp] theorem POVM.aOp_mats (M : POVM A d) (a : A) :
    ((M.aOp (E := E)).mats a).val = MIPRE.aOp (M.mats a).val := rfl

variable [DecidableEq A]

end Lift

/-! ## Mixtures -/

section Mix

variable {A : Type*} [Fintype A] {d : Type*} [Fintype d] [DecidableEq d] {ι : Type*} [Fintype ι]

/-- **A convex combination of POVMs** with the same outcomes, with real weights `w` summing to
one. -/
def POVM.mix (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) (Q : ι → POVM A d) :
    POVM A d where
  mats a := ⟨∑ i, w i • ((Q i).mats a).val, by
    rw [selfAdjoint.mem_iff, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.conjTranspose_smul, star_trivial, ← Matrix.star_eq_conjTranspose,
      selfAdjoint.mem_iff.mp ((Q i).mats a).prop]⟩
  nonneg a :=
    Subtype.coe_le_coe.mp (Matrix.nonneg_iff_posSemidef.mpr
      (Matrix.posSemidef_sum _ fun i _ => ((Q i).posSemidef a).smul (hw i)))
  normalized := by
    apply Subtype.ext
    rw [AddSubmonoidClass.coe_finsetSum]
    show ∑ a, ∑ i, w i • ((Q i).mats a).val = 1
    rw [Finset.sum_comm]
    simp_rw [← Finset.smul_sum, POVM.sum_val]
    rw [← Finset.sum_smul, hw1, one_smul]

@[simp] theorem POVM.mix_mats (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1)
    (Q : ι → POVM A d) (a : A) :
    ((POVM.mix w hw hw1 Q).mats a).val = ∑ i, w i • ((Q i).mats a).val := rfl

variable {dA dB : Type*} [Fintype dA] [Fintype dB]

variable [DecidableEq dA] [DecidableEq dB]

end Mix

/-! ## A POVM from a positive family, and uniform averages -/

section Of

variable {A : Type*} [Fintype A] {d : Type*} [Fintype d] [DecidableEq d]

/-- A POVM from a family of positive semidefinite matrices summing to the identity. -/
def POVM.ofPosSemidef (E : A → Matrix d d ℂ) (hpos : ∀ a, (E a).PosSemidef)
    (hsum : ∑ a, E a = 1) : POVM A d where
  mats a := ⟨E a, by
    rw [selfAdjoint.mem_iff, Matrix.star_eq_conjTranspose]
    exact (hpos a).isHermitian.eq⟩
  nonneg a := Subtype.coe_le_coe.mp (Matrix.nonneg_iff_posSemidef.mpr (hpos a))
  normalized := by
    apply Subtype.ext
    rw [AddSubmonoidClass.coe_finsetSum]
    exact hsum

@[simp] theorem POVM.ofPosSemidef_mats (E : A → Matrix d d ℂ) (hpos : ∀ a, (E a).PosSemidef)
    (hsum : ∑ a, E a = 1) (a : A) : ((POVM.ofPosSemidef E hpos hsum).mats a).val = E a := rfl

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

variable [DecidableEq A]

variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]

end Of

/-! ## Averages and relabelling -/

section AvgMap

variable {A : Type*} [Fintype A] [DecidableEq A] {d : Type*} [Fintype d] [DecidableEq d]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

end AvgMap

/-! ## Acceptance on the support, and the conditional failure -/

section Fail

variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]

variable {X Y A B C : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B] [Fintype C]
  [DecidableEq C] {ψ : dA × dB → ℂ} {x : X} {y : Y}

end Fail

/-! ## The agreement triangle -/

section Triangle

variable {X Λ : Type*} [Fintype X] [Fintype Λ] {dA dB : Type*} [Fintype dA] [DecidableEq dA]
  [Fintype dB] [DecidableEq dB]

/-- The agreement probability of two families of POVMs, one per party, on the same questions,
averaged over the question distribution `μ`: the paper's `p(R, S)`. -/
def agreeSum (μ : X → ℝ) (ψ : dA × dB → ℂ) (M : X → POVM Λ dA) (N : X → POVM Λ dB) : ℝ :=
  ∑ x, μ x * ∑ a, bornProb ψ (((M x).mats a).val) (((N x).mats a).val)

/-- The weighted squared norm of Alice's measurement vectors, `∑_x μ_x ∑_a ‖(M^x_a ⊗ I)ψ‖²`. -/
def weightA (μ : X → ℝ) (ψ : dA × dB → ℂ) (M : X → POVM Λ dA) : ℝ :=
  ∑ x, μ x * ∑ a, stateSqNorm ψ (((M x).mats a).val)

/-- Bob's version. -/
def weightB (μ : X → ℝ) (ψ : dA × dB → ℂ) (N : X → POVM Λ dB) : ℝ :=
  ∑ x, μ x * ∑ a, ‖stateVecB ψ (((N x).mats a).val)‖ ^ 2

/-- The weighted cross-party deviation of two families. -/
def xDev (μ : X → ℝ) (ψ : dA × dB → ℂ) (M : X → POVM Λ dA) (N : X → POVM Λ dB) : ℝ :=
  ∑ x, μ x * ∑ a, xSqNorm ψ (((M x).mats a).val) (((N x).mats a).val)

variable {μ : X → ℝ} {ψ : dA × dB → ℂ}

end Triangle

end MIPRE

end


