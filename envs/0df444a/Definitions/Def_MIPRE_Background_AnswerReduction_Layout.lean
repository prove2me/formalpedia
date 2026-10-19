-- Prove2me | Definitions.Def_MIPRE_Background_AnswerReduction_Layout
-- name    : MIPRE_Background_AnswerReduction_Layout
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T05:30:34.784423+00:00
-- url     : https://prove2.me/theorems/768386f6-502a-45c6-a066-fea64225700e
-- title:
--   Definitions of Layout: The layout of the PCP coordinates Piece AR-3d of `planning/answer-reduction.md`: how a program reads a vector of…
-- statement:
--   The definitions of the module `MIPRE.Background.AnswerReduction.Layout` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The layout of the PCP coordinates. Piece AR-3d of `planning/answer-reduction.md`: how a program reads a vector of `V^pcp`. * The coordinates are numbered in three runs (`coordIndex`): the concatenated point register `V_{6,pt}` (`pt6`, `m'` coordinates), the concatenated direction register `V_{6,dir}` (`dir6`), and the six seeds. A vector of `V^pcp` is thus the three lists `ptOf6`, `dirOf6`, `seedsOf`. * Each copy of the test is a contiguous run of `V_{6,pt}` and of `V_{6,dir}` with its own seed (`regsAt`): copy `i ≤ 5` at offset `i·m` and length `m` (`regs_eq`), copy `6` at offset `0` and…
--
--   **Definitions** (9): `MIPRE.AnswerReduction.Pcp.bitIndex` (The numbering of the bits: coordinate by coordinate, `k` bits each.); `MIPRE.AnswerReduction.Pcp.coordIndex` (The numbering of the coordinates: `V_{6,pt}`, then `V_{6,dir}`, then the seeds.); `MIPRE.AnswerReduction.Pcp.dirOf6` (The concatenated direction register of a vector.); `MIPRE.AnswerReduction.Pcp.flatBits` (The Shoup bits of a vector of `V^pcp`, in the numbering.); `MIPRE.AnswerReduction.Pcp.layout` (The three runs of the coordinates.); `MIPRE.AnswerReduction.Pcp.pcpDim` (The number of coordinates of `V^pcp`, in the three runs.); `MIPRE.AnswerReduction.Pcp.ptOf6` (The concatenated point register of a vector.); `MIPRE.AnswerReduction.Pcp.regsAt` (The registers of a copy at offset `o` and length `sz` of the concatenated registers, with the seed `c`.); `MIPRE.AnswerReduction.Pcp.seedsOf` (The six seeds of a vector.).
--
--   **Embedded lemmas** (12): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `coordIndex_symm_castAdd`, `coordIndex_symm_natAdd_castAdd`, `coordIndex_symm_natAdd_natAdd`, `dir6_aux`, `dir6_block`, `dir6_ne_coord`, `layout_coord`, `layout_dir6`, `layout_pt6`, `pt6_aux`, ….
--
--   **Formalization Note** The bundle is the module `MIPRE.Background.AnswerReduction.Layout` (`MIPRE/Background/AnswerReduction/Layout.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 99 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/AnswerReduction/Layout.lean; blueprint def:ar-typed-game

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/AnswerReduction/Layout.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Image
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Basic
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Rotate
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.FieldTheory.Finite.Trace
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.KummerExtension
import Mathlib.FieldTheory.Minpoly.Finite
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Matrix.Circulant
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Pi
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.Polynomial.Content
import Mathlib.RingTheory.Polynomial.Cyclotomic.Factorization
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Background_LIDT_Game
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Canonical
import Definitions.Def_MIPRE_Background_LIDT_CLGame
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Background_LIDT_Presentation
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_SAT_Circuit
import Definitions.Def_MIPRE_Foundations_SAT_Cnf
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_CL_Closure
import Definitions.Def_MIPRE_Foundations_CL_Closure_B
import Definitions.Def_MIPRE_Foundations_CL_Sampler
import Definitions.Def_MIPRE_Foundations_Verifier
import Definitions.Def_MIPRE_Foundations_SAT_Succinct
import Definitions.Def_MIPRE_Foundations_SAT_Decoupled
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Fold
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_SAT_Pcp
import Definitions.Def_MIPRE_Background_AnswerReduction_PcpPresentation
import Definitions.Def_MIPRE_Foundations_CL_Embedding
import Definitions.Def_MIPRE_Foundations_CL_Product
import Definitions.Def_MIPRE_Foundations_CL_Downsize
import Definitions.Def_MIPRE_Foundations_CL_TypedSampler
import Definitions.Def_MIPRE_Foundations_CL_ProductSampler
import Definitions.Def_MIPRE_Background_LIDT_PresentationQueries
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryRepresentation
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryPolynomial
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryConstants
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryPower
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryQuotient
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryNormalize
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryDivision
import Definitions.Def_MIPRE_Foundations_Cost_Binary
import Definitions.Def_MIPRE_Foundations_SAT_Formula
import Definitions.Def_MIPRE_Foundations_SAT_FmlLib
import Definitions.Def_MIPRE_Foundations_SAT_Flatten
import Definitions.Def_MIPRE_Foundations_Cost_Reader
import Definitions.Def_MIPRE_Foundations_SAT_FmlProg
import Definitions.Def_MIPRE_Foundations_SAT_ArrayProg
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryLinear
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryElimination
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryBasisProg
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryEchelon
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryBasis
import Definitions.Def_MIPRE_Foundations_LowDegree_BinarySolve
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryMatrixSolve
import Definitions.Def_MIPRE_Foundations_Cost_Iterates
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryCirculantProg
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryKernel
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryGroupAlgebra
import Definitions.Def_MIPRE_Foundations_LowDegree_FiniteReducedComponents
import Definitions.Def_MIPRE_Foundations_LowDegree_IdempotentSplit
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryComponents
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryComponentsProg
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryQuotientFrobenius
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryQuotientComponents
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryQuotientFactors
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryGCD
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryFactorization
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryCyclotomicSeed
import Definitions.Def_MIPRE_Foundations_LowDegree_BinarySubstitution
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryNonresidueLoop
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryNonresidueCorrectness
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryQuotientOrbit
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryTraceBits
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryOrbitPolynomial
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryOrbitDescent
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryQuotientPolynomial
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryQuotientTranslation
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryCoprimeDegree
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryComposedSumPolynomial
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryComposedSumProg
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryOddPrimeProgram
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryPrimePowerTrace
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryArtinSchreier
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryArtinSchreierProg
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryArtinSchreierTower
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryArtinSchreierLoop
import Definitions.Def_MIPRE_Foundations_LowDegree_UnaryDegreeArithmetic
import Definitions.Def_MIPRE_Foundations_LowDegree_UnaryPrimality
import Definitions.Def_MIPRE_Foundations_LowDegree_UnaryPrimePower
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryDegreeFactors
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryDegreeDecomposition
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryPrimePowerDispatch
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryIrreducibleAssembly
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryIrreducibleConstructor
import Definitions.Def_MIPRE_Foundations_LowDegree_Shoup
import Definitions.Def_MIPRE_Foundations_LowDegree_ShoupCoefficients
import Definitions.Def_MIPRE_Foundations_SAT_QuotientField
import Definitions.Def_MIPRE_Foundations_SAT_FieldTrace
import Definitions.Def_MIPRE_Foundations_SAT_FieldCoordinates
import Theorems.Thm_MIPRE_AnswerReduction_Pcp_pt6_block

/-!
# The layout of the PCP coordinates

Piece AR-3d of `planning/answer-reduction.md`: how a program reads a vector of `V^pcp`.

* The coordinates are numbered in three runs (`coordIndex`): the concatenated point register
  `V_{6,pt}` (`pt6`, `m'` coordinates), the concatenated direction register `V_{6,dir}` (`dir6`),
  and the six seeds. A vector of `V^pcp` is thus the three lists `ptOf6`, `dirOf6`, `seedsOf`.
* Each copy of the test is a contiguous run of `V_{6,pt}` and of `V_{6,dir}` with its own seed
  (`regsAt`): copy `i ≤ 5` at offset `i·m` and length `m` (`regs_eq`), copy `6` at offset `0` and
  length `m'` (`regs6_eq`).
* The bits of the downsized vector, numbered by `bitIndex`, are the field elements' Shoup bits in
  that order (`toBits_pcp`), so a program reads them by cutting `k`-bit blocks.
-/

noncomputable section

namespace MIPRE.AnswerReduction.Pcp

open Finset MIPRE.LIDT MIPRE.LIDT.CL SAT MIPRE.CL Cost

variable (P : PcpParams)

/-! ## The concatenated registers -/

theorem dir6_block (i : Fin 5) (j : Fin P.m) :
    dir6 P ⟨i * P.m + j, by
      have h1 : (i : ℕ) * P.m ≤ 4 * P.m := Nat.mul_le_mul_right _ (Nat.lt_succ_iff.mp i.isLt)
      have h2 : (j : ℕ) < P.m := j.isLt
      simp only [PcpParams.m']
      omega⟩ = .dir i j := by
  have hj : (j : ℕ) < P.m := j.isLt
  have hi : (i : ℕ) < 5 := i.isLt
  have hlt : (i : ℕ) * P.m + j < 5 * P.m := by nlinarith
  have hm : 0 < P.m := by omega
  simp only [dir6, dif_pos hlt]
  congr 1
  · apply Fin.ext
    simp only
    rw [show (i : ℕ) * P.m + j = j + P.m * i by ring, Nat.add_mul_div_left _ _ hm,
      Nat.div_eq_of_lt hj, zero_add]
  · apply Fin.ext
    simp only
    rw [show (i : ℕ) * P.m + j = j + P.m * i by ring, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt hj]

theorem pt6_aux (j : Fin (5 + P.s)) :
    pt6 P ⟨5 * P.m + j, by have := j.isLt; simp only [PcpParams.m']; omega⟩ = .auxPt j := by
  simp only [pt6, show ¬ (5 * P.m + (j : ℕ) < 5 * P.m) by omega, dif_neg, not_false_eq_true]
  congr 1
  exact Fin.ext (by simp)

theorem dir6_aux (j : Fin (5 + P.s)) :
    dir6 P ⟨5 * P.m + j, by have := j.isLt; simp only [PcpParams.m']; omega⟩ = .auxDir j := by
  simp only [dir6, show ¬ (5 * P.m + (j : ℕ) < 5 * P.m) by omega, dif_neg, not_false_eq_true]
  congr 1
  exact Fin.ext (by simp)

theorem pt6_ne_coord (r : Fin P.m') (c : Fin 6) : pt6 P r ≠ .coord c := by
  unfold pt6; split_ifs <;> simp

theorem dir6_ne_coord (r : Fin P.m') (c : Fin 6) : dir6 P r ≠ .coord c := by
  unfold dir6; split_ifs <;> simp

/-! ## A copy of the test as a run of the concatenated registers -/

/-- The registers of a copy at offset `o` and length `sz` of the concatenated registers, with
the seed `c`. -/
def regsAt (o sz : ℕ) (c : Fin 6) (h : o + sz ≤ P.m') : Regs (Coord P) sz where
  pt j := pt6 P ⟨o + j, by omega⟩
  dir j := dir6 P ⟨o + j, by omega⟩
  coord := .coord c
  pt_injective a b hab := by
    have := pt6_injective P hab
    exact Fin.ext (by simpa using this)
  dir_injective a b hab := by
    have := dir6_injective P hab
    exact Fin.ext (by simpa using this)
  pt_ne_dir _ _ hab := (regs6 P).pt_ne_dir _ _ hab
  pt_ne_coord _ := pt6_ne_coord P _ c
  dir_ne_coord _ := dir6_ne_coord P _ c

theorem regs_le (i : Fin 5) : (i : ℕ) * P.m + P.m ≤ P.m' := by
  have := i.isLt
  have : (i : ℕ) * P.m + P.m ≤ 5 * P.m := by nlinarith
  simp only [PcpParams.m']
  omega

/-! ## The three runs -/

variable {F : Type*}

/-- The concatenated point register of a vector. -/
def ptOf6 (x : Coord P → F) : Fin P.m' → F := fun r => x (pt6 P r)

/-- The concatenated direction register of a vector. -/
def dirOf6 (x : Coord P → F) : Fin P.m' → F := fun r => x (dir6 P r)

/-- The six seeds of a vector. -/
def seedsOf (x : Coord P → F) : Fin 6 → F := fun c => x (.coord c)

/-- The three runs of the coordinates. -/
def layout : Coord P ≃ Fin P.m' ⊕ Fin P.m' ⊕ Fin 6 where
  toFun
    | .pt i j => .inl ⟨i * P.m + j, by have := regs_le P i; have := j.isLt; omega⟩
    | .dir i j => .inr (.inl ⟨i * P.m + j, by have := regs_le P i; have := j.isLt; omega⟩)
    | .coord c => .inr (.inr c)
    | .auxPt j => .inl ⟨5 * P.m + j, by have := j.isLt; simp only [PcpParams.m']; omega⟩
    | .auxDir j => .inr (.inl ⟨5 * P.m + j, by have := j.isLt; simp only [PcpParams.m']; omega⟩)
  invFun
    | .inl r => pt6 P r
    | .inr (.inl r) => dir6 P r
    | .inr (.inr c) => .coord c
  left_inv c := by
    cases c with
    | pt i j => exact pt6_block P i j
    | dir i j => exact dir6_block P i j
    | coord c => rfl
    | auxPt j => exact pt6_aux P j
    | auxDir j => exact dir6_aux P j
  right_inv c := by
    rcases c with r | r | c
    · simp only [pt6]
      split_ifs with h
      · simp only [Sum.inl.injEq]
        exact Fin.ext (by simp only; rw [Nat.mul_comm]; exact Nat.div_add_mod _ _)
      · simp only [Sum.inl.injEq]
        exact Fin.ext (by simp only; omega)
    · simp only [dir6]
      split_ifs with h
      · simp only [Sum.inr.injEq, Sum.inl.injEq]
        exact Fin.ext (by simp only; rw [Nat.mul_comm]; exact Nat.div_add_mod _ _)
      · simp only [Sum.inr.injEq, Sum.inl.injEq]
        exact Fin.ext (by simp only; omega)
    · rfl

/-- The number of coordinates of `V^pcp`, in the three runs. -/
abbrev pcpDim : ℕ := P.m' + (P.m' + 6)

/-- The numbering of the coordinates: `V_{6,pt}`, then `V_{6,dir}`, then the seeds. -/
def coordIndex : Coord P ≃ Fin (pcpDim P) :=
  (layout P).trans ((Equiv.sumCongr (Equiv.refl _) finSumFinEquiv).trans finSumFinEquiv)

theorem layout_pt6 (r : Fin P.m') : layout P (pt6 P r) = .inl r :=
  (layout P).apply_symm_apply (.inl r)

theorem layout_dir6 (r : Fin P.m') : layout P (dir6 P r) = .inr (.inl r) :=
  (layout P).apply_symm_apply (.inr (.inl r))

theorem layout_coord (c : Fin 6) : layout P (.coord c) = .inr (.inr c) := rfl

@[simp] theorem coordIndex_symm_castAdd (r : Fin P.m') :
    (coordIndex P).symm (Fin.castAdd (P.m' + 6) r) = pt6 P r := by
  rw [Equiv.symm_apply_eq]
  simp [coordIndex, layout_pt6]

@[simp] theorem coordIndex_symm_natAdd_castAdd (r : Fin P.m') :
    (coordIndex P).symm (Fin.natAdd P.m' (Fin.castAdd 6 r)) = dir6 P r := by
  rw [Equiv.symm_apply_eq]
  simp [coordIndex, layout_dir6]

@[simp] theorem coordIndex_symm_natAdd_natAdd (c : Fin 6) :
    (coordIndex P).symm (Fin.natAdd P.m' (Fin.natAdd P.m' c)) = .coord c := by
  rw [Equiv.symm_apply_eq]
  simp [coordIndex, layout_coord]

/-! ## The bits of a downsized vector -/

variable {k : ℕ} (hk : 1 ≤ k)

/-- The numbering of the bits: coordinate by coordinate, `k` bits each. -/
def bitIndex (k : ℕ) : Coord P × Fin k ≃ Fin (pcpDim P * k) :=
  ((coordIndex P).prodCongr (Equiv.refl _)).trans finProdFinEquiv

/-- The Shoup bits of a vector of `V^pcp`, in the numbering. -/
def flatBits (v : Coord P → (shoupBinField k hk).carrier) : BitStr :=
  ((shoupBinField k hk).vecBits fun r => v ((coordIndex P).symm r)).flatten

end MIPRE.AnswerReduction.Pcp

end


