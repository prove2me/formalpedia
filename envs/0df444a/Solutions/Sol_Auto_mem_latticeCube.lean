-- Prove2me | solution 1 for Auto.mem_latticeCube
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:03:30.057105+00:00
-- url     : https://prove2.me/submissions/33932416-83e1-44d2-90dc-98fd1365ca54

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal NNReal symmDiff
noncomputable section
variable {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
namespace Auto
theorem _root_.solution {N : ℕ} (hN : 0 < N) {k : Fin d → ℤ} {x : Fin d → ℝ} :
    x ∈ latticeCube N k ↔ ∀ i, ⌊(N : ℝ) * x i⌋ = k i := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  simp only [latticeCube, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Ico, Int.floor_eq_iff]
  refine forall_congr' fun i => ?_
  rw [div_le_iff₀ hN', lt_div_iff₀ hN']
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
end Auto
