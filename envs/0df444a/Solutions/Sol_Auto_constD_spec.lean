-- Prove2me | solution 1 for Auto.constD_spec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T18:55:29.320463+00:00
-- url     : https://prove2.me/submissions/67eba99a-72fe-4063-883f-da0a973ea5e6

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
    0 ≤ constD ∧ ∀ (m : ℕ) (v : Fin 3) (s : ℝ), 0 < s → ∀ x, |Dfun (dexp m v) s x| ≤ constD := by
  have h1 := Classical.choose_spec (Dfun_bound 1)
  have h2 := Classical.choose_spec (Dfun_bound 2)
  refine ⟨add_nonneg h1.1 h2.1, fun m v s hs x => ?_⟩
  rcases dexp_cases m v with h | h <;> rw [h] <;> unfold constD
  · linarith [h1.2 s hs x, h2.1]
  · linarith [h2.2 s hs x, h1.1]
end Auto
