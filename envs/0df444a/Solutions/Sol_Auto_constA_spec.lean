-- Prove2me | solution 1 for Auto.constA_spec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:37:42.698864+00:00
-- url     : https://prove2.me/submissions/48149569-015f-4872-ac1e-36a91fc76890

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_dexp_cases

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
namespace Auto
theorem _root_.solution :
    0 ≤ constA ∧ ∀ (m : ℕ) (v : Fin 3) (s : ℝ), 0 < s → ∀ d, |acoef (dexp m v) s d| ≤ constA *
      √s := by
  have h1 := Classical.choose_spec (acoef_bound 1 le_rfl)
  have h2 := Classical.choose_spec (acoef_bound 2 (by norm_num))
  refine ⟨add_nonneg h1.1 h2.1, fun m v s hs d => ?_⟩
  have hs' := Real.sqrt_nonneg s
  rcases dexp_cases m v with h | h <;> rw [h] <;> unfold constA
  · nlinarith [h1.2 s hs d, mul_nonneg h2.1 hs']
  · nlinarith [h2.2 s hs d, mul_nonneg h1.1 hs']
end Auto
