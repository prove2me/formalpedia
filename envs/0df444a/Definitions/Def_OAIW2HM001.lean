-- Prove2me | Definitions.Def_OAIW2HM001
-- name    : OAIW2HM001
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-25T05:39:15.769341+00:00
-- url     : https://prove2.me/theorems/b8978b5a-fc96-49ef-81f8-be4f81b7a769
-- title:
--   Definitions bundle OAIW2HM001 of the split of OpenAI, Spontaneous magnetization in the quantum Heisenberg ferromagnet
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Heisenberg.spontaneous_magnetization`, carved from OpenAI's openai/math development (OpenAI, *Spontaneous magnetization in the quantum Heisenberg ferromagnet*, OpenAI Math Release, September 24, 2026, result family 271, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 19 declarations of OpenAI's Lean: 11 definitions, 1 inductive type or structure and 7 theorems. The definitions and types are `OAI.Heisenberg.Serial.split`, `OAI.Heisenberg.sandwichFunctional`, `OAI.HeisenbergStrip.BoundaryCauchy`, `OAI.SpinEvolution.LocalDecomposition`, `OAI.completedSurfaceDecEq`, `OAI.exposureDecEq`, `OAI.kernelDecEq`, `OAI.matrixSurfaceDecEq`, `OAI.meshCPDecEq`, `OAI.meshDecEq`, `OAI.regDecEq`, `OAI.surfaceDecEq`.
--
--   **Sources.** They come from these modules of lean/OAI/MathematicalPhysics, in whole or in part: `Heisenberg_AveragedEnergy`, `Heisenberg_BoundedStrip`, `Heisenberg_CompletedSurface`, `Heisenberg_CyclicEnergy`, `Heisenberg_ExponentialEvolution`, `Heisenberg_LayerEnergy`, `Heisenberg_MeshCutProduct`, `Heisenberg_MeshMatrixSurface`, `Heisenberg_MeshPin`, `Heisenberg_MeshSurface`, `Heisenberg_RegularPin`, `Heisenberg_StateCompactness`, `Heisenberg_ThermodynamicDynamics`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundle `OAIW2HM002`; the statement `OAI.Heisenberg.Surface.mesh_matrix_surface`; the proofs of `OAI.Heisenberg.Bootstrap.periodic_return_estimate`, `OAI.Heisenberg.Flow.indexed_prefix_leakage` and `OAI.Heisenberg.Surface.mesh_matrix_surface`.
-- source:
--   OpenAI, Spontaneous magnetization in the quantum Heisenberg ferromagnet, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 271; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Spontaneous-magnetization-in-the-quantum-Heisenberg-ferromagnet-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/MathematicalPhysics at commit adc7f12

import Mathlib

section
-- module Solutions.OAIW2_Heis.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
/-- Mathlib's newer `TensorProduct.inductionOn` (no `zero` case: it is the `tmul` case at
`0 ⊗ₜ 0`); ours has only `TensorProduct.induction_on`, which asks for one. Not named
`TensorProduct.inductionOn`: inside `namespace OAI` that would make `open TensorProduct` open
`OAI.TensorProduct` instead of Mathlib's. -/
@[elab_as_elim]
theorem tensorInductionOn {R M N : Type*} [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N] {motive : TensorProduct R M N → Prop} (z : TensorProduct R M N)
    (tmul : ∀ x y, motive (TensorProduct.tmul R x y))
    (add : ∀ x y, motive x → motive y → motive (x + y)) : motive z :=
  TensorProduct.induction_on z (by simpa using tmul 0 0) tmul add
/-- Mathlib's newer case names for `FreeGroup.induction_on` (`one`, where ours says `C1`). -/
@[elab_as_elim]
theorem freeGroupInductionOn {α : Type*} {C : FreeGroup α → Prop} (z : FreeGroup α) (one : C 1)
    (of : ∀ x, C (FreeGroup.of x)) (inv_of : ∀ x, C (FreeGroup.of x) → C (FreeGroup.of x)⁻¹)
    (mul : ∀ x y, C x → C y → C (x * y)) : C z :=
  FreeGroup.induction_on z one of inv_of mul
end OAICompat434

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_ExponentialEvolution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexConjugate ENNReal Classical
open scoped ComplexConjugate BigOperators

namespace SpinEvolution

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

structure LocalDecomposition (D : E →L[ℂ] E) (Local : ℕ → E → Prop) (C : ℝ) : Prop where
  nonneg : 0 ≤ C
  split : ∀ k A, Local k A → ∃ (r : ℕ) (g : Fin r → E),
    D A = ∑ i, g i ∧ (∀ i, Local (k+1) (g i)) ∧
      ∑ i, ‖g i‖ ≤ C * (k+1) * ‖A‖

end SpinEvolution

end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_ThermodynamicDynamics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexConjugate ENNReal Classical
open scoped ComplexConjugate BigOperators

namespace Heisenberg

theorem clm_topologicalRing {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] :
    IsTopologicalRing (E →L[ℂ] E) := inferInstance

end Heisenberg

open Filter Topology Metric
open scoped NNReal

open scoped NNReal
end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_StateCompactness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexConjugate ENNReal Classical
open scoped ComplexConjugate BigOperators
open Filter Topology Metric
open scoped NNReal
open scoped NNReal

namespace Heisenberg

open scoped ComplexOrder

open scoped InnerProductSpace

theorem positive_norm_le_four_one {E : Type*} [CStarAlgebra E] [PartialOrder E]
    [StarOrderedRing E] (φ : E →L[ℂ] ℂ)
    (hpos : ∀ B, 0 ≤ φ (star B * B)) : ‖φ‖ ≤ 4 * ‖φ 1‖ := by
  have hp : ∀ A : E, 0 ≤ A → 0 ≤ φ A := by
    intro A hA
    obtain ⟨B, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA
    exact hpos B
  let f : E →ₚ[ℂ] ℂ :=
    { φ.toLinearMap with
      monotone' := by
        intro A B h
        change φ A ≤ φ B
        have h' := hp (B - A) (sub_nonneg.mpr h)
        simpa only [map_sub, sub_nonneg] using h' }
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro A
  obtain ⟨x, hx, hnorm, hA⟩ := CStarAlgebra.exists_sum_four_nonneg A
  conv_lhs => rw [hA, map_sum]
  calc
    ‖∑ i : Fin 4, φ (Complex.I ^ (i : ℕ) • x i)‖ ≤
        ∑ i : Fin 4, ‖φ (Complex.I ^ (i : ℕ) • x i)‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin 4, ‖φ 1‖ * ‖A‖ := by
      apply Finset.sum_le_sum
      intro i _
      rw [map_smul, norm_smul, norm_pow, Complex.norm_I, one_pow, one_mul]
      exact (PositiveLinearMap.norm_apply_le_of_nonneg f (x i) (hx i)).trans
        (mul_le_mul_of_nonneg_left (hnorm i) (norm_nonneg _))
    _ = (4 * ‖φ 1‖) * ‖A‖ := by simp; ring

def sandwichFunctional {E : Type*} [CStarAlgebra E] (φ : E →L[ℂ] ℂ) (B : E) :
    E →L[ℂ] ℂ := φ.comp (ContinuousLinearMap.mulLeftRight ℂ E (star B) B)

@[simp] theorem sandwichFunctional_apply {E : Type*} [CStarAlgebra E]
    (φ : E →L[ℂ] ℂ) (B A : E) : sandwichFunctional φ B A = φ (star B * A * B) := rfl

theorem sandwichFunctional_positive {E : Type*} [CStarAlgebra E]
    (φ : E →L[ℂ] ℂ) (hpos : ∀ B, 0 ≤ φ (star B * B)) (B A : E) :
    0 ≤ sandwichFunctional φ B (star A*A) := by
  simpa only [sandwichFunctional_apply, star_mul, mul_assoc] using hpos (A*B)

theorem sandwich_one_pos {E : Type*} [CStarAlgebra E] [PartialOrder E]
    [StarOrderedRing E] (φ : E →L[ℂ] ℂ) (hn : φ 1 = 1)
    (hpos : ∀ B, 0 ≤ φ (star B * B)) {B : E} (hB : IsUnit B) :
    0 < (sandwichFunctional φ B 1).re := by
  have hp := hpos B
  simp only [sandwichFunctional_apply, mul_one]
  apply lt_of_le_of_ne hp.1
  intro hz
  have hzero : φ (star B * B) = 0 := by
    apply Complex.ext
    · exact hz.symm
    · exact hp.2.symm
  have hnorm := positive_norm_le_four_one (sandwichFunctional φ B)
    (sandwichFunctional_positive φ hpos B)
  have hzfun : sandwichFunctional φ B = 0 := by
    apply norm_eq_zero.mp
    apply le_antisymm _ (norm_nonneg _)
    simpa only [sandwichFunctional_apply, mul_one, hzero, norm_zero, mul_zero] using hnorm
  obtain ⟨u, rfl⟩ := hB
  have hh := congrArg (fun f : E →L[ℂ] ℂ => f (star (↑u⁻¹ : E) * (↑u⁻¹ : E))) hzfun
  simp only [sandwichFunctional_apply, zero_apply] at hh
  have hc : star (↑u : E) * (star (↑u⁻¹ : E) * (↑u⁻¹ : E)) * ↑u = 1 := by
    calc
      _ = star ((↑u⁻¹ : E) * ↑u) * ((↑u⁻¹ : E) * ↑u) := by rw [star_mul]; simp only [mul_assoc]
      _ = 1 := by simp
  rw [hc, hn] at hh
  exact one_ne_zero hh

end Heisenberg
end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_BoundedStrip
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexConjugate ENNReal Classical
open scoped ComplexConjugate BigOperators
open Filter Topology Metric
open scoped NNReal
open scoped NNReal

open scoped ComplexConjugate Topology

open Set Filter Complex
open scoped Topology

namespace HeisenbergStrip

def BoundaryCauchy (β : ℝ) (F : ℕ → ℂ → ℂ) : Prop :=
  ∀ R : ℝ, 0 < R → ∀ ε : ℝ, 0 < ε →
    ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N, ∀ z : ℂ,
      (z.im = 0 ∨ z.im = β) → |z.re| ≤ R → ‖F m z - F n z‖ < ε

end HeisenbergStrip
end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_LayerEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Classical
open Matrix
open scoped Classical
open Matrix
open scoped Classical
open Matrix
open scoped Classical
open scoped BigOperators Classical
open scoped Classical
open scoped Classical
open Filter
open scoped Classical
open scoped Classical

@[reducible] local instance exposureDecEq (α : Type*) : DecidableEq α := Classical.decEq α

open Filter Topology
open scoped RealInnerProductSpace Classical
end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_CyclicEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators Classical RealInnerProductSpace

open Filter Topology
open scoped RealInnerProductSpace Classical

open scoped Classical
open Filter
namespace Heisenberg.Serial

section
open Matrix
variable {V B : Type*} [Fintype V] [DecidableEq V] [Fintype B]

def split (n : ℕ) : (Fin (n+1) → B) ≃ B × (Fin n → B) where
  toFun c := (c 0,fun i => c i.succ)
  invFun c := Fin.cons c.1 c.2
  left_inv c := by funext i; exact Fin.cases rfl (fun _ => rfl) i
  right_inv c := by rfl

end

open Matrix

end Heisenberg.Serial

end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_AveragedEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Classical
open Matrix
noncomputable section
open scoped Classical
open Matrix
noncomputable section
open scoped Classical
open Matrix
noncomputable section
open scoped Classical
noncomputable section
open scoped BigOperators Classical
noncomputable section
open scoped Classical
noncomputable section
open scoped Classical
open Filter
noncomputable section
open scoped Classical
noncomputable section
open scoped Classical
attribute [local instance] exposureDecEq
attribute [-instance] exposureDecEq

end
end
end
end
end
end
end
end
end

noncomputable section
open Filter Topology
open scoped RealInnerProductSpace Classical

@[reducible] local instance kernelDecEq (α : Type*) : DecidableEq α := Classical.decEq α

end
end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_RegularPin
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped Classical BigOperators
attribute [-instance] instDecidableEqFin
@[reducible] local instance regDecEq (α : Type*) : DecidableEq α := Classical.decEq α
end
end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_MeshPin
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped Classical BigOperators Fin.NatCast
open Filter Topology
attribute [-instance] instDecidableEqFin
@[reducible] local instance meshDecEq (α : Type*) : DecidableEq α := Classical.decEq α
end
end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_MeshSurface
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped Classical BigOperators Fin.NatCast
open Filter Topology
attribute [-instance] instDecidableEqFin instDecidableEqProd
@[reducible] local instance surfaceDecEq (α : Type*) : DecidableEq α := Classical.decEq α
end
end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_MeshCutProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Classical BigOperators Fin.NatCast
attribute [-instance] instDecidableEqFin instDecidableEqProd
@[reducible] local instance meshCPDecEq (α : Type*) : DecidableEq α := Classical.decEq α
end
end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_MeshMatrixSurface
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Classical BigOperators Fin.NatCast
open Filter Topology
attribute [-instance] instDecidableEqFin instDecidableEqProd
@[reducible] local instance matrixSurfaceDecEq (α : Type*) : DecidableEq α := Classical.decEq α
end
end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_CompletedSurface
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Classical BigOperators Fin.NatCast Matrix Matrix.Norms.Operator
open Filter Topology
attribute [-instance] instDecidableEqFin instDecidableEqProd
@[reducible] local instance completedSurfaceDecEq (α : Type*) : DecidableEq α := Classical.decEq α
end
end

end OAI
end


