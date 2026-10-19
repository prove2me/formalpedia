-- Prove2me | Definitions.Def_MIPRE_Foundations_POVMMix_B
-- name    : MIPRE_Foundations_POVMMix_B
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T01:49:46.624908+00:00
-- url     : https://prove2.me/theorems/e85c924c-44c3-493c-84d8-f9f48101b1f2
-- title:
--   Definitions of POVMMix (addendum): Mixtures and extensions of POVMs, and the agreement triangle Three constructions on bundled POVMs that the padded…
-- statement:
--   The definitions of the module `MIPRE.Foundations.POVMMix` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Mixtures and extensions of POVMs, and the agreement triangle. Three constructions on bundled POVMs that the padded strategy of the Pauli basis test's stage 4 needs, and one inequality. * `POVM.aOp` extends a POVM on `d` by the identity to `d × E`; `POVM.dirac a₀` answers `a₀` with certainty; `POVM.mix w Q` is a convex combination of POVMs with the same outcomes. A strategy that must be a *function of the question* while the analysis controls it *sample by sample* is a mixture over the samples producing the question, and the Born rule's linearity (`bornProb_mix_left`, `bornProb_mix_right`)…
--
--   This bundle **adds** the declarations below to the already published bundle `MIPRE_Foundations_POVMMix` of the same module, which the new statements of this upload need and the earlier bundle left out.
--
--   **Definitions** (3): `MIPRE.POVM.avgOn` (**The uniform average of POVMs over a finset**, defaulting to the deterministic answer `a₀` when the finset is empty.); `MIPRE.POVM.dirac` (The deterministic POVM answering `a₀`.); `MIPRE.unifOn` (The uniform weights on a finset.).
--
--   **Embedded lemmas** (2): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `sum_unifOn`, `unifOn_nonneg`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.POVMMix` (`MIPRE/Foundations/POVMMix.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 25 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/POVMMix.lean; blueprint lem:qld-global-setup

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/POVMMix.lean (delta bundle: declarations the new statements need that the published bundle Def_MIPRE_Foundations_POVMMix does not carry);
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
import Definitions.Def_MIPRE_Foundations_Pasting
import Definitions.Def_MIPRE_Foundations_POVMMix
import Theorems.Thm_MIPRE_POVM_posSemidef
import Theorems.Thm_MIPRE_POVM_sum_val
import Theorems.Thm_MIPRE_aOp_sum
import Theorems.Thm_MIPRE_sum_bornProb_map
import Theorems.Thm_MIPRE_sum_stateSqNorm_le_one
import Theorems.Thm_MIPRE_weightA_ge
import Theorems.Thm_MIPRE_weightB_ge
import Theorems.Thm_MIPRE_xDev_eq

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

variable [DecidableEq A]

/-- The deterministic POVM answering `a₀`. -/
def POVM.dirac (a₀ : A) : POVM A d where
  mats a := ⟨if a = a₀ then 1 else 0, by
    rw [selfAdjoint.mem_iff]
    split_ifs <;> simp⟩
  nonneg a := by
    refine Subtype.coe_le_coe.mp (Matrix.nonneg_iff_posSemidef.mpr ?_)
    show (if a = a₀ then (1 : Matrix d d ℂ) else 0).PosSemidef
    split_ifs
    · exact Matrix.PosSemidef.one
    · exact Matrix.PosSemidef.zero
  normalized := by
    apply Subtype.ext
    rw [AddSubmonoidClass.coe_finsetSum]
    show ∑ a, (if a = a₀ then (1 : Matrix d d ℂ) else 0) = 1
    rw [Finset.sum_ite_eq' univ a₀]
    simp

end Lift

/-! ## Mixtures -/

section Mix

variable {A : Type*} [Fintype A] {d : Type*} [Fintype d] [DecidableEq d] {ι : Type*} [Fintype ι]

variable {dA dB : Type*} [Fintype dA] [Fintype dB]

variable [DecidableEq dA] [DecidableEq dB]

end Mix

/-! ## A POVM from a positive family, and uniform averages -/

section Of

variable {A : Type*} [Fintype A] {d : Type*} [Fintype d] [DecidableEq d]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The uniform weights on a finset. -/
def unifOn (S : Finset ι) : ι → ℝ := fun i => if i ∈ S then (S.card : ℝ)⁻¹ else 0

omit [Fintype ι] in
theorem unifOn_nonneg (S : Finset ι) (i : ι) : 0 ≤ unifOn S i := by
  unfold unifOn
  split_ifs <;> positivity

theorem sum_unifOn (S : Finset ι) (hS : S.Nonempty) : ∑ i, unifOn S i = 1 := by
  unfold unifOn
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
  exact mul_inv_cancel₀ (Nat.cast_ne_zero.mpr (Finset.card_pos.mpr hS).ne')

variable [DecidableEq A]

/-- **The uniform average of POVMs over a finset**, defaulting to the deterministic answer `a₀`
when the finset is empty. -/
def POVM.avgOn (S : Finset ι) (Q : ι → POVM A d) (a₀ : A) : POVM A d :=
  if hS : S.Nonempty then POVM.mix (unifOn S) (unifOn_nonneg S) (sum_unifOn S hS) Q
  else POVM.dirac a₀

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

variable {μ : X → ℝ} {ψ : dA × dB → ℂ}

end Triangle

end MIPRE

end


