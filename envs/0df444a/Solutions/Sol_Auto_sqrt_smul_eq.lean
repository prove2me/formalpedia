-- Prove2me | solution 1 for Auto.sqrt_smul_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:06:43.109791+00:00
-- url     : https://prove2.me/submissions/699c843f-0687-4afb-91bb-71ff4a71fc76

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT

set_option autoImplicit true
@[expose] public section
public section
public section
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder ENNReal NNReal
open Matrix MeasureTheory Filter Topology
open Auto
noncomputable section
variable {n : Type*} [Fintype n] [DecidableEq n]
omit [DecidableEq n]
namespace Auto
theorem _root_.solution {n : Type*} [Fintype n] {Q : Matrix n n ℂ} (hQ : Q.PosSemidef) {a : ℝ}
    (ha : 0 ≤ a) :
    open scoped Classical in CFC.sqrt ((a : ℂ) • Q) = ((√a : ℝ) : ℂ) • CFC.sqrt Q := by
  classical
  have hs : (CFC.sqrt Q).PosSemidef := (CFC.sqrt_nonneg Q).posSemidef
  have hnn : 0 ≤ ((√a : ℝ) : ℂ) • CFC.sqrt Q := (hs.smul (by exact_mod_cast Real.sqrt_nonneg a : (0
      : ℂ) ≤ ((√a : ℝ) : ℂ))).nonneg
  refine CFC.sqrt_unique ?_ hnn
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, CFC.sqrt_mul_sqrt_self Q hQ.nonneg,
    ← Complex.ofReal_mul, Real.mul_self_sqrt ha]
end Auto
