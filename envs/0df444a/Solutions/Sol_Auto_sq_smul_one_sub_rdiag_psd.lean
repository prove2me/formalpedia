-- Prove2me | solution 1 for Auto.sq_smul_one_sub_rdiag_psd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:39:06.255619+00:00
-- url     : https://prove2.me/submissions/b6cd0035-bbe3-4376-893b-e91dc1507bb2

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_rdiag_posSemidef

set_option autoImplicit true
@[expose] public section
public section
public section
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder ENNReal NNReal
open Matrix MeasureTheory Filter Topology
public section
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder ENNReal NNReal
open Matrix MeasureTheory Filter Topology Real
public section
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder ENNReal NNReal
open Matrix MeasureTheory Filter Topology Real
public section
open scoped ENNReal NNReal
open MeasureTheory Filter Topology Real
public section
open Auto
open MeasureTheory Filter Topology Matrix Real
open scoped ENNReal NNReal MatrixOrder Matrix.Norms.L2Operator ComplexOrder
noncomputable section
namespace Auto
theorem _root_.solution {ι : Type*} [Fintype ι] [DecidableEq ι]
    {f : ι → ℝ} {d : ℝ} (hf : ∀ i, |f i| ≤ d) :
    ((d ^ 2 : ℝ) • (1 : Matrix ι ι ℂ) - rdiag f * rdiag f).PosSemidef := by
  have e : (d ^ 2 : ℝ) • (1 : Matrix ι ι ℂ) - rdiag f * rdiag f =
      rdiag fun i => d ^ 2 - f i ^ 2 := by
    ext i j
    by_cases hij : i = j
    · subst hij; simp [rdiag]; ring
    · simp [rdiag, hij]
  rw [e]
  refine rdiag_posSemidef fun i => ?_
  have := hf i
  nlinarith [abs_nonneg (f i), sq_abs (f i)]
end Auto
