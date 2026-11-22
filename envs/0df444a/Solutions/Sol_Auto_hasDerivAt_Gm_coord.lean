-- Prove2me | solution 1 for Auto.hasDerivAt_Gm_coord
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:28:01.453421+00:00
-- url     : https://prove2.me/submissions/d88efb0a-8b99-4389-abdb-bdb3377b1c2c

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_HeatData_hasDerivAt_update_coord

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
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace Auto
theorem _root_.solution (β : ℝ) (m : ℕ) (s : ℝ) (i : Fin 3) (p : Fin 3 → ℝ) :
    HasDerivAt (fun x => Gm β m s (Function.update p i x)) (Gm β (m + 1) s p) (p i) := by
  have hin : HasDerivAt (fun x => Function.update p i x 0 + Function.update p i x 1 +
      Function.update p i x 2) 1 (p i) := by
    have := ((HeatData.hasDerivAt_update_coord p i 0 (p i)).add (HeatData.hasDerivAt_update_coord p
        i 1 (p i))).add (HeatData.hasDerivAt_update_coord p i
          2 (p i))
    convert this using 1 <;> try rfl
    have : i = 0 ∨ i = 1 ∨ i = 2 := by fin_cases i <;> simp
    rcases this with rfl | rfl | rfl <;> simp
  have hval : Function.update p i (p i) 0 + Function.update p i (p i) 1 +
      Function.update p i (p i) 2 = p 0 + p 1 + p 2 := by simp
  have hg := hasDerivAt_gaussianD m (β * s) (p 0 + p 1 + p 2)
  rw [← hval] at hg
  have := hg.comp (p i) hin
  rw [hval, mul_one] at this
  exact this
end Auto
