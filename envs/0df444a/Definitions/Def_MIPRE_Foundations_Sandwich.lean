-- Prove2me | Definitions.Def_MIPRE_Foundations_Sandwich
-- name    : MIPRE_Foundations_Sandwich
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T00:55:21.124243+00:00
-- url     : https://prove2.me/theorems/d302f720-59a7-4cce-b5fa-6de100320e8f
-- title:
--   Definitions of Sandwich: The sandwich of two approximately commuting projective measurements Two projective measurements `{X_a}` and `{Z_b}` on…
-- statement:
--   The definitions of the module `MIPRE.Foundations.Sandwich` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The sandwich of two approximately commuting projective measurements. Two projective measurements `{X_a}` and `{Z_b}` on one party that *approximately commute* on a state cannot in general be measured jointly. The **sandwich** `R_{a,b} = Z_b X_a Z_b` always can: it is a POVM --- exactly, by projectivity of `Z` alone --- so its Naimark dilation is a genuine *projective* joint measurement, and the dilation's compression identity carries every Born-rule estimate about `R` to the dilated measurement unchanged. What has to be proved is that the sandwich is approximately self-consistent across the…
--
--   **Definitions** (3): `MIPRE.extVec2` (**The two-sided extension of a state**: one ancilla register in the fixed state `|a0>` adjoined to *each* party.); `MIPRE.sand` (**The sandwich** `R_{a,b} = Z_b X_a Z_b` of two projective measurements.); `MIPRE.sandPOVM` (The sandwich, as a bundled POVM.).
--
--   **Embedded lemmas** (7): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `sandPOVM_mats`, `sand_conjTranspose`, `sand_eq_gram`, `sand_posSemidef`, `sum_prod_id`, `sum_prod_swap`, `sum_sand`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.Sandwich` (`MIPRE/Foundations/Sandwich.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 12 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Sandwich.lean; blueprint lem:qld-combined-points

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Sandwich.lean (definition bundle: declarations the uploaded statements rest on);
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

/-!
# The sandwich of two approximately commuting projective measurements

Two projective measurements `{X_a}` and `{Z_b}` on one party that *approximately commute* on a
state cannot in general be measured jointly. The **sandwich**

`R_{a,b} = Z_b X_a Z_b`

always can: it is a POVM --- exactly, by projectivity of `Z` alone --- so its Naimark dilation is
a genuine *projective* joint measurement, and the dilation's compression identity carries every
Born-rule estimate about `R` to the dilated measurement unchanged.

What has to be proved is that the sandwich is approximately self-consistent across the two
parties, and that is the content of `one_sub_sum_bornProb_sand_le`: a five-link chain from

`sum_{a,b} <psi| R_{a,b} (x) R'_{a,b} |psi>`  to  `1`,

whose links are, in order, the two parties' commutators (each paid for by one Cauchy--Schwarz
against a family of squared norms summing to at most one), the two parties' `X`-consistency
collapsed by `sum_a X'_a = Id`, and the `Z`-consistency. The one thing the chain must *not* do is
bound the `q^2` outcome pairs one at a time: that would cost a factor `q` and the conclusion has
to be `q`-independent. Every link here is therefore an estimate on a single operator product ---
either a sum that telescopes exactly, or one Cauchy--Schwarz over the whole outcome set.

The statement carries an index `iota` with weights, because that is how it is used: the two
measurements come from a question and the bound is an average over questions, and averaging a
square root would otherwise need a second Jensen step.
-/

noncomputable section

namespace MIPRE

open Finset Matrix
open scoped ComplexOrder MatrixOrder Kronecker

set_option linter.unusedSectionVars false

/-! ## Weighted Cauchy--Schwarz -/

/-! ## Sums over a product of the outcome set -/

theorem sum_prod_id {M : Type*} [AddCommMonoid M] {α : Type*} [Fintype α] (f : α × α → M) :
    ∑ p : α × α, f p = ∑ a : α, ∑ b : α, f (a, b) := by
  rw [← Finset.univ_product_univ, Finset.sum_product]

theorem sum_prod_swap {M : Type*} [AddCommMonoid M] {α : Type*} [Fintype α] (f : α × α → M) :
    ∑ p : α × α, f p = ∑ b : α, ∑ a : α, f (a, b) := by
  rw [sum_prod_id]
  exact Finset.sum_comm

/-! ## Quadratic forms: Cauchy--Schwarz and the order -/

section QForm

variable {N : Type*} [Fintype N]

variable [DecidableEq N]

end QForm

/-! ## The two factors -/

section Bipartite

variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]

end Bipartite

/-! ## Sums of mutually orthogonal projections -/

section Proj

variable {N : Type*} [Fintype N] [DecidableEq N]

end Proj

/-! ## Products of the two factors -/

section Bipartite2

variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]

end Bipartite2

/-! ## The sandwich -/

section Sand

variable {A : Type*} [Fintype A] [DecidableEq A]
  {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]

/-- **The sandwich** `R_{a,b} = Z_b X_a Z_b` of two projective measurements. -/
def sand {d : Type*} [Fintype d] [DecidableEq d] (X Z : A → Matrix d d ℂ) (p : A × A) :
    Matrix d d ℂ :=
  Z p.2 * X p.1 * Z p.2

variable {d : Type*} [Fintype d] [DecidableEq d] {X Z : A → Matrix d d ℂ}

/-- The sandwich is the Gram operator of the ordered product, which is where its positivity and
its normalization both come from. -/
theorem sand_eq_gram (hX : IsPVM X) (hZ : IsPVM Z) (p : A × A) :
    sand X Z p = (X p.1 * Z p.2)ᴴ * (X p.1 * Z p.2) := by
  rw [Matrix.conjTranspose_mul, hX.isSelfAdjoint, hZ.isSelfAdjoint, sand]
  calc Z p.2 * X p.1 * Z p.2 = Z p.2 * (X p.1 * X p.1) * Z p.2 := by rw [hX.idem]
    _ = Z p.2 * X p.1 * (X p.1 * Z p.2) := by noncomm_ring

theorem sand_conjTranspose (hX : IsPVM X) (hZ : IsPVM Z) (p : A × A) :
    (sand X Z p)ᴴ = sand X Z p := by
  rw [sand_eq_gram hX hZ, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]

theorem sand_posSemidef (hX : IsPVM X) (hZ : IsPVM Z) (p : A × A) : (sand X Z p).PosSemidef := by
  rw [sand_eq_gram hX hZ]
  exact Matrix.posSemidef_conjTranspose_mul_self _

/-- **The sandwich is a POVM**, exactly: only projectivity of `Z` and completeness of `X` are
used, and no approximate commutation whatsoever. -/
theorem sum_sand (hX : IsPVM X) (hZ : IsPVM Z) : ∑ p : A × A, sand X Z p = 1 := by
  classical
  rw [sum_prod_swap]
  rw [Finset.sum_congr rfl fun b (_ : b ∈ univ) => show
      (∑ a : A, sand X Z (a, b)) = Z b from by
    rw [show (∑ a : A, sand X Z (a, b)) = Z b * (∑ a : A, X a) * Z b from by
        rw [Matrix.mul_sum, Finset.sum_mul]
        rfl,
      hX.sum_eq_one, Matrix.mul_one, hZ.idem]]
  exact hZ.sum_eq_one

/-- The sandwich, as a bundled POVM. -/
def sandPOVM (hX : IsPVM X) (hZ : IsPVM Z) : POVM (A × A) d where
  mats p := ⟨sand X Z p, selfAdjoint.mem_iff.mpr (by
    rw [Matrix.star_eq_conjTranspose]
    exact sand_conjTranspose hX hZ p)⟩
  nonneg p := Subtype.coe_le_coe.mp (Matrix.nonneg_iff_posSemidef.mpr (sand_posSemidef hX hZ p))
  normalized := by
    apply Subtype.ext
    rw [AddSubmonoidClass.coe_finsetSum]
    exact sum_sand hX hZ

@[simp] theorem sandPOVM_mats (hX : IsPVM X) (hZ : IsPVM Z) (p : A × A) :
    (((sandPOVM hX hZ).mats p).val) = sand X Z p := rfl

end Sand

/-! ## The chain

Five links from the agreement of the two parties' sandwiches to one. The two middle links are the
parties' commutators, each paid for by one Cauchy--Schwarz against a family of squared norms
summing to at most one; the third collapses the `X`-outcome sum by completeness; the last is the
`Z`-consistency. -/

section Chain

variable {A : Type*} [Fintype A] [DecidableEq A]
  {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
  {ψ : dA × dB → ℂ} {X Z : A → Matrix dA dA ℂ} {X' Z' : A → Matrix dB dB ℂ}

end Chain

/-! ## The chain, assembled -/

section Assemble

variable {A : Type*} [Fintype A] [DecidableEq A]
  {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]

end Assemble

/-! ## The two-sided extension, and the dilated joint measurement -/

section Ext2

variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]

variable {Anc Bnc : Type*} [Fintype Anc] [DecidableEq Anc] [Fintype Bnc] [DecidableEq Bnc]

/-- **The two-sided extension of a state**: one ancilla register in the fixed state `|a0>`
adjoined to *each* party. This is `def:expanded-state`'s shape with an inert ancilla, and it is
what a *pair* of Naimark dilations --- one per party --- is compressed back by. -/
def extVec2 (ψ : dA × dB → ℂ) (a₀ : Anc) (b₀ : Bnc) : (dA × Anc) × (dB × Bnc) → ℂ :=
  ((ancillaEmbed dA a₀) ⊗ₖ (ancillaEmbed dB b₀)) *ᵥ ψ

end Ext2

/-! ## The dilated joint measurement -/

section Joint

variable {A : Type*} [Fintype A] [DecidableEq A]
  {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]

variable {ψ : dA × dB → ℂ}
  {Q : (A × A) → Matrix (dA × (A × A)) (dA × (A × A)) ℂ}
  {Q' : (A × A) → Matrix (dB × (A × A)) (dB × (A × A)) ℂ}
  {R : (A × A) → Matrix dA dA ℂ} {R' : (A × A) → Matrix dB dB ℂ}

end Joint

/-! ## The theorem -/

section Main

variable {A : Type*} [Fintype A] [DecidableEq A]
  {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]

end Main

/-! ## Coarse-graining -/

section Coarse

variable {A C : Type*} [Fintype A] [DecidableEq A] [Fintype C] [DecidableEq C]
  {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]

end Coarse

/-! ## A deviation as the norm of one vector

`sum_avg_norm_fibre_sq` is a statement about *vectors*; this is the bridge to the cross-party
deviation, and the linearity that lets a fibre sum of vectors be read as the deviation of the
coarse-grained operators. -/

section Vector

variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]

end Vector

end MIPRE

end


