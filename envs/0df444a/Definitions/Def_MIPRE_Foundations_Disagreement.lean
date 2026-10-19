-- Prove2me | Definitions.Def_MIPRE_Foundations_Disagreement
-- name    : MIPRE_Foundations_Disagreement
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T00:57:57.499393+00:00
-- url     : https://prove2.me/theorems/685692d7-afda-4aae-9d0e-6ecf03ed39e0
-- title:
--   Definitions of Disagreement: The disagreement of two parties' measurements The probability `dis ψ M N = 1 - ∑_a ⟨ψ| M_a ⊗ N_a |ψ⟩` that Alice's POVM…
-- statement:
--   The definitions of the module `MIPRE.Foundations.Disagreement` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The disagreement of two parties' measurements. The probability `dis ψ M N = 1 - ∑_a ⟨ψ| M_a ⊗ N_a |ψ⟩` that Alice's POVM `M` and Bob's `N`, measured on `ψ`, return different outcomes, and four facts about it that the soundness of answer reduction uses throughout: * it only decreases under a common coarse-graining (`dis_map_le`); * disagreements chain across the two parties, linearly (`sum_dis_triangle`, from `agreeSum_triangle`): Alice's `A` against Bob's `D` through Bob's `B` and Alice's `C`; * the probability of an event under Alice's measurement is at most its probability under Bob's, plus…
--
--   **Definitions** (1): `MIPRE.dis` (**The disagreement** of Alice's POVM `M` and Bob's POVM `N` on the state `ψ`: the probability that their outcomes differ.).
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.Disagreement` (`MIPRE/Foundations/Disagreement.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 14 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Disagreement.lean

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Disagreement.lean (definition bundle: declarations the uploaded statements rest on);
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
import Definitions.Def_MIPRE_Foundations_POVMMix

/-!
# The disagreement of two parties' measurements

The probability `dis ψ M N = 1 - ∑_a ⟨ψ| M_a ⊗ N_a |ψ⟩` that Alice's POVM `M` and Bob's `N`,
measured on `ψ`, return different outcomes, and four facts about it that the soundness of answer
reduction uses throughout:

* it only decreases under a common coarse-graining (`dis_map_le`);
* disagreements chain across the two parties, linearly (`sum_dis_triangle`, from
  `agreeSum_triangle`): Alice's `A` against Bob's `D` through Bob's `B` and Alice's `C`;
* the probability of an event under Alice's measurement is at most its probability under Bob's,
  plus their disagreement (`sum_ite_bornProb_one_le`): no square root is lost, and the two
  measurements need not be projective;
* a subtest whose acceptance forces the agreement of two readings of the answers bounds their
  disagreement by its conditional failure, and a subtest whose acceptance excludes an event bounds
  that event's probability by it (`sum_ite_bornProb_le_condFail`).
-/

noncomputable section

namespace MIPRE

open Finset Matrix
open scoped Kronecker

variable {Λ : Type*} [Fintype Λ] {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB]
  [DecidableEq dB]

/-- **The disagreement** of Alice's POVM `M` and Bob's POVM `N` on the state `ψ`: the probability
that their outcomes differ. -/
def dis (ψ : dA × dB → ℂ) (M : POVM Λ dA) (N : POVM Λ dB) : ℝ :=
  1 - ∑ a, bornProb ψ ((M.mats a).val) ((N.mats a).val)

/-! ## Families on a uniform index -/

section Uniform

variable {X : Type*} [Fintype X] [Nonempty X]

end Uniform

/-! ## Subtests -/

section Subtests

variable {X Y A B C : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B] [Fintype C]
  [DecidableEq C] {G : Game X Y A B} {ψ : dA × dB → ℂ} {MA : X → POVM A dA} {MB : Y → POVM B dB}

end Subtests

end MIPRE

end


