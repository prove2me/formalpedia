-- Prove2me | solution 1 for Auto.hsSq_sqrt_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:24:35.793738+00:00
-- url     : https://prove2.me/submissions/2192ba1e-1c02-4d82-a18c-9518c2a9eb23

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
public section
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder ENNReal NNReal
open Matrix MeasureTheory Filter Topology Real
open Auto
noncomputable section
variable {κ : Type*} [Fintype κ] [DecidableEq κ]
omit [DecidableEq κ]
namespace Auto
theorem _root_.solution {κ : Type*} [Fintype κ] {P : Matrix κ κ ℂ} (hP : 0 ≤ P) :
    open scoped Classical in hsSq (CFC.sqrt P) = P.trace.re := by
  classical
  rw [← hsRe_self, hsRe, (CFC.sqrt_nonneg P).posSemidef.isHermitian.eq,
    CFC.sqrt_mul_sqrt_self P hP]
end Auto
