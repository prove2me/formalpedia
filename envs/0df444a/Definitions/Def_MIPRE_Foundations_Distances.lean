-- Prove2me | Definitions.Def_MIPRE_Foundations_Distances
-- name    : MIPRE_Foundations_Distances
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-16T23:08:22.696132+00:00
-- url     : https://prove2.me/theorems/d4db0748-4c51-449c-8cad-a10723ee4986
-- title:
--   Definitions of Distances: Distance measures This file contains the definitions of the blueprint subsection "Distance measures" (Section 2,…
-- statement:
--   The definitions of the module `MIPRE.Foundations.Distances` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Distance measures. This file contains the definitions of the blueprint subsection "Distance measures" (Section 2, "Foundations"): the dimension-normalized Hilbert--Schmidt inner product and squared norm on complex matrices, and the distance between two families of POVMs relative to a question distribution.
--
--   **Definitions** (4): `MIPRE.POVM.map` (Relabel the outcomes of a POVM along `f : A → B` (data processing): the operator of the outcome `b` is the sum of the operators of the…); `MIPRE.ProjectiveMeasurement.toPOVM` (The measurement for the question `x` of a projective measurement family on the matrix algebra `ℂ^{d×d}`, as a POVM (positivity follows from…); `MIPRE.inconsistency` (The inconsistency of two families of POVMs `M` (acting on `ℂ^dA`) and `N` (acting on `ℂ^dB`) with the same question and outcome alphabets,…); `MIPRE.uniform` (The uniform distribution on a finite type, as a real-valued weight function.).
--
--   **Embedded lemmas** (1): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `map_mats`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.Distances` (`MIPRE/Foundations/Distances.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 1 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Distances.lean; blueprint def:expanded-state, def:inconsistency

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Distances.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.ENat.Lattice
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Definitions.Def_MIPRE_Foundations_Games

/-!
# Distance measures

This file contains the definitions of the blueprint subsection "Distance measures"
(Section 2, "Foundations"): the dimension-normalized Hilbert--Schmidt inner product and
squared norm on complex matrices, and the distance between two families of POVMs
relative to a question distribution.

## Main definitions

- `MIPRE.hsInner`: the dimension-normalized Hilbert--Schmidt inner product
  `⟨A, B⟩_hs = τ(Aᴴ B)`, where `τ = Tr/d` is the dimension-normalized trace
  (blueprint `def:hs-norm`).
- `MIPRE.hsNormSq`: the squared dimension-normalized Hilbert--Schmidt norm
  `‖A‖²_hs = τ(Aᴴ A)` (blueprint `def:hs-norm`).
- `MIPRE.povmDistance`: the squared distance `𝔼_{x ∼ μ} ∑ₐ ‖M^x_a - N^x_a‖²_hs`
  between two families of POVMs (blueprint `def:distance`).
- `MIPRE.IsPOVMClose`: the δ-closeness relation `M ≈_δ N` of the blueprint.

## Implementation notes

- As elsewhere in the foundations, question distributions are bare real-valued
  functions: `povmDistance` and `IsPOVMClose` take any `μ : X → ℝ`, and results about
  them will assume nonnegativity and normalization as needed.
- `⟨A, A⟩_hs` is a nonnegative real for every `A`, but proving so requires a positivity
  argument; `hsNormSq` takes the real part `.re` so that the definition carries no
  proof obligations. Nonnegativity is recorded separately in `hsNormSq_nonneg`.
- The blueprint writes the POVM distance as `𝔼_{x ∼ μ} ∑ₐ τ((M^x_a - N^x_a)²)`; since
  differences of POVM elements are Hermitian, this agrees with the definition here (see
  `hsNormSq_of_isHermitian`).
-/

namespace MIPRE

open ComplexOrder Matrix

/-! ## The normalized Hilbert--Schmidt inner product -/

variable {n : Type*} [Fintype n]

/-! ## POVM distance -/

variable {X A d : Type*} [Fintype X] [Fintype A] [Fintype d] [DecidableEq d]

/-! ## Constructions on POVMs -/

open scoped MatrixOrder in
/-- Relabel the outcomes of a POVM along `f : A → B` (data processing): the operator of
the outcome `b` is the sum of the operators of the outcomes `a` with `f a = b`. -/
noncomputable def POVM.map {B : Type*} [Fintype B] [DecidableEq B] (f : A → B)
    (M : POVM A d) : POVM B d where
  mats b := ∑ a ∈ Finset.univ.filter (fun a => f a = b), M.mats a
  nonneg b := by
    have h : (0 : Matrix d d ℂ) ≤ ∑ a ∈ Finset.univ.filter (fun a => f a = b), (M.mats a).val :=
      Finset.sum_nonneg fun a _ => Subtype.coe_le_coe.mpr (M.nonneg a)
    rw [← AddSubmonoidClass.coe_finsetSum] at h
    exact Subtype.coe_le_coe.mp h
  normalized := (Finset.sum_fiberwise Finset.univ f M.mats).trans M.normalized

@[simp] theorem POVM.map_mats {B : Type*} [Fintype B] [DecidableEq B] (f : A → B) (M : POVM A d)
    (b : B) : (((M.map f).mats b).val)
      = ∑ a ∈ Finset.univ.filter fun a => f a = b, ((M.mats a).val) :=
  AddSubmonoidClass.coe_finsetSum _ _

open scoped MatrixOrder in
/-- The measurement for the question `x` of a projective measurement family on the matrix
algebra `ℂ^{d×d}`, as a POVM (positivity follows from projectivity). -/
def ProjectiveMeasurement.toPOVM (P : ProjectiveMeasurement X A (Matrix d d ℂ)) (x : X) :
    POVM A d where
  mats a := ⟨P.M x a, selfAdjoint.mem_iff.mpr (P.selfAdjoint x a)⟩
  nonneg a := by
    have h := Matrix.posSemidef_conjTranspose_mul_self (P.M x a)
    rw [← Matrix.star_eq_conjTranspose, P.selfAdjoint x a, P.projective x a] at h
    exact Subtype.coe_le_coe.mp h.nonneg
  normalized := by
    apply Subtype.ext
    rw [AddSubmonoidClass.coe_finsetSum]
    exact P.normalized x

/-- The uniform distribution on a finite type, as a real-valued weight function. -/
noncomputable def uniform (X : Type*) [Fintype X] : X → ℝ := fun _ => (Fintype.card X : ℝ)⁻¹

/-! ## Inconsistency of two measurement families on a bipartite state -/

open Kronecker in
/-- The inconsistency of two families of POVMs `M` (acting on `ℂ^dA`) and `N` (acting on
`ℂ^dB`) with the same question and outcome alphabets, relative to a question distribution
`μ` and a bipartite state `ψ ∈ ℂ^dA ⊗ ℂ^dB = ℂ^(dA × dB)`: the probability that measuring
`M^x` on the first factor and `N^x` on the second factor yields different outcomes,
`𝔼_{x ∼ μ} ∑_{a ≠ b} ⟨ψ| M^x_a ⊗ N^x_b |ψ⟩`
(the consistency relation of JNVWY21qld, Definition 4.8, in its two-space form). The
tensor product is realized by the Kronecker product, as in `TensorProductStrategy.value`;
the probability is a nonnegative real, and we take the real part so that the definition
carries no proof obligation. -/
noncomputable def inconsistency {dA dB : Type*} [Fintype dA] [DecidableEq dA]
    [Fintype dB] [DecidableEq dB] [DecidableEq A]
    (μ : X → ℝ) (ψ : dA × dB → ℂ) (M : X → POVM A dA) (N : X → POVM A dB) : ℝ :=
  ∑ x, μ x * ∑ a, ∑ b, if a = b then 0 else
    (star ψ ⬝ᵥ ((((M x).mats a).val ⊗ₖ ((N x).mats b).val) *ᵥ ψ)).re

end MIPRE


