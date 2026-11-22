-- Prove2me | solution 1 for Auto.HeatData.baseTrace_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:36:43.521201+00:00
-- url     : https://prove2.me/submissions/9eee20ae-37ca-4017-8f45-7aa7c974d961

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_trace_cyclic_diag
public import Theorems.Thm_Auto_dexp_sum
public import Theorems.Thm_Auto_HeatData_Dfun_mul_w

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
open Auto
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
open Auto.HeatData
variable (Hd : HeatData ι)
namespace Auto.HeatData
theorem _root_.solution (hh : 0 ≤ Hd.h) {m : ℕ} (hm : m = 3 ∨ m = 4) {s : ℝ} (hs : 0 < s)
    (p : Fin 3 → ℝ) :
    Hd.baseTrace m p s = ((Hd.h ^ 3 * √s ^ m : ℝ) : ℂ) * ∑ i, ∑ j, ∑ k, Hd.A 0 i j * Hd.A 1 j k
      * Hd.A 2 k i * ((gaussianD (dexp m 0) (21 / 20 * s) (Hd.u i - p 0) * gaussianD (dexp m 1)
      (21 / 20 * s) (Hd.u j - p 1) * gaussianD (dexp m 2) (21 / 20 * s) (Hd.u k - p 2) : ℝ) : ℂ) :=
          by
  have e1 : (0 : Fin 3) + 1 = 1 := rfl
  have e2 : (1 : Fin 3) + 1 = 2 := rfl
  have e3 : (2 : Fin 3) + 1 = 0 := rfl
  rw [baseTrace, Dmat, Dmat, Dmat, W, W, W, e1, e2, e3, trace_cyclic_diag, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Hd.Dfun_mul_w hh _ hs, Hd.Dfun_mul_w hh _ hs, Hd.Dfun_mul_w hh _ hs]
  have hsum := dexp_sum hm
  have hpow : √s ^ dexp m 0 * √s ^ dexp m 1 * √s ^ dexp m 2 = √s ^ m := by
    rw [← pow_add, ← pow_add]; congr 1; omega
  have : (Hd.h * (√s ^ dexp m 0 * gaussianD (dexp m 0) (21 / 20 * s) (Hd.u i - p 0)) *
      (Hd.h * (√s ^ dexp m 1 * gaussianD (dexp m 1) (21 / 20 * s) (Hd.u j - p 1))) *
      (Hd.h * (√s ^ dexp m 2 * gaussianD (dexp m 2) (21 / 20 * s) (Hd.u k - p 2)))) =
      Hd.h ^ 3 * √s ^ m * (gaussianD (dexp m 0) (21 / 20 * s) (Hd.u i - p 0) *
        gaussianD (dexp m 1) (21 / 20 * s) (Hd.u j - p 1) *
        gaussianD (dexp m 2) (21 / 20 * s) (Hd.u k - p 2)) := by
    rw [← hpow]; ring
  rw [this]
  push_cast; ring
end Auto.HeatData
