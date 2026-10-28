-- Prove2me | Definitions.Def_OAIQ033D012
-- name    : OAIQ033D012
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T01:52:36.149486+00:00
-- url     : https://prove2.me/theorems/1b429f2b-6ef2-4641-b9ee-39343ff6591c
-- title:
--   Definitions bundle OAIQ033D012 of the split of OpenAI, Entanglement without distillable secret key in local dimension ten (result family 272)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.DimensionTen.main_pair`, carved from OpenAI's openai/math development (OpenAI, *Entanglement without distillable secret key in local dimension ten (result family 272)*, OpenAI Math Release, September 27, 2026, result family 272, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 69 declarations of OpenAI's Lean: 6 definitions and 63 theorems. The definitions and types are `OAI.DimensionTen.Border.H`, `OAI.DimensionTen.Border.NB`, `OAI.DimensionTen.Border.cofactorKernel`, `OAI.DimensionTen.Border.minor`, `OAI.DimensionTen.Border.quadraticIndex`, `OAI.DimensionTen.Border.rowChoices`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis/Quantum/DimensionTen, in whole or in part: [`Quantum_DimensionTen_Annihilator`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Quantum/DimensionTen/Quantum/DimensionTen/Annihilator.lean), [`Quantum_DimensionTen_BorderData`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Quantum/DimensionTen/Quantum/DimensionTen/BorderData.lean), [`Quantum_DimensionTen_BorderField`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Quantum/DimensionTen/Quantum/DimensionTen/BorderField.lean), [`Quantum_DimensionTen_Cofactors`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Quantum/DimensionTen/Quantum/DimensionTen/Cofactors.lean), [`Quantum_DimensionTen_MinorData`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Quantum/DimensionTen/Quantum/DimensionTen/MinorData.lean), [`Quantum_DimensionTen_NormalizedMatrices`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Quantum/DimensionTen/Quantum/DimensionTen/NormalizedMatrices.lean), [`Quantum_DimensionTen_QuadraticBounds`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Quantum/DimensionTen/Quantum/DimensionTen/QuadraticBounds.lean).
--
--   **Imports.** It imports the bundles `OAIQ033D000`, `OAIQ033D002` and `OAIQ033D003` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ033D014`; the statements `OAI.DimensionTen.Border.minors_eq`, `OAI.DimensionTen.Border.minors_row_0`, `OAI.DimensionTen.Border.minors_row_11`, `OAI.DimensionTen.Border.minors_row_12`, `OAI.DimensionTen.Border.minors_row_13`, `OAI.DimensionTen.Border.minors_row_14`, `OAI.DimensionTen.Border.minors_row_2`, `OAI.DimensionTen.Border.minors_row_4` and `OAI.DimensionTen.Border.minors_row_7`; the proofs of `OAI.DimensionTen.Border.minors_eq`, `OAI.DimensionTen.Border.minors_row_0`, `OAI.DimensionTen.Border.minors_row_11`, `OAI.DimensionTen.Border.minors_row_12`, `OAI.DimensionTen.Border.minors_row_13`, `OAI.DimensionTen.Border.minors_row_14`, `OAI.DimensionTen.Border.minors_row_2`, `OAI.DimensionTen.Border.minors_row_4` and `OAI.DimensionTen.Border.minors_row_7`.
-- source:
--   OpenAI, Entanglement without distillable secret key in local dimension ten (result family 272), OpenAI Math Release, September 27, 2026, https://github.com/openai/math (result family 272; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Entanglement-with-zero-distillable-secret-key-in-local-dimension-ten-September-27-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis/Quantum/DimensionTen at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ033D000
import Definitions.Def_OAIQ033D002
import Definitions.Def_OAIQ033D003

section
-- module Solutions.OAIQ033_DT.Quantum_DimensionTen_BorderData
attribute [-instance] _root_.OAI.DimensionTen.Mod41.instFactPrimeOfNatNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Matrix
namespace DimensionTen.Border
def H : Matrix (Fin 15) (Fin 15) ℤ := PencilAlgebra.H

lemma commute_01_row0 : ∀ k : Fin 20, (B0 * B1) 0 k = (B1 * B0) 0 k := by decide +kernel
lemma commute_01_row1 : ∀ k : Fin 20, (B0 * B1) 1 k = (B1 * B0) 1 k := by decide +kernel
lemma commute_01_row2 : ∀ k : Fin 20, (B0 * B1) 2 k = (B1 * B0) 2 k := by decide +kernel
lemma commute_01_row3 : ∀ k : Fin 20, (B0 * B1) 3 k = (B1 * B0) 3 k := by decide +kernel
lemma commute_01_row4 : ∀ k : Fin 20, (B0 * B1) 4 k = (B1 * B0) 4 k := by decide +kernel
lemma commute_01_row5 : ∀ k : Fin 20, (B0 * B1) 5 k = (B1 * B0) 5 k := by decide +kernel
lemma commute_01_row6 : ∀ k : Fin 20, (B0 * B1) 6 k = (B1 * B0) 6 k := by decide +kernel
lemma commute_01_row7 : ∀ k : Fin 20, (B0 * B1) 7 k = (B1 * B0) 7 k := by decide +kernel
lemma commute_01_row8 : ∀ k : Fin 20, (B0 * B1) 8 k = (B1 * B0) 8 k := by decide +kernel
lemma commute_01_row9 : ∀ k : Fin 20, (B0 * B1) 9 k = (B1 * B0) 9 k := by decide +kernel
lemma commute_01_row10 : ∀ k : Fin 20, (B0 * B1) 10 k = (B1 * B0) 10 k := by decide +kernel
lemma commute_01_row11 : ∀ k : Fin 20, (B0 * B1) 11 k = (B1 * B0) 11 k := by decide +kernel
lemma commute_01_row12 : ∀ k : Fin 20, (B0 * B1) 12 k = (B1 * B0) 12 k := by decide +kernel
lemma commute_01_row13 : ∀ k : Fin 20, (B0 * B1) 13 k = (B1 * B0) 13 k := by decide +kernel
lemma commute_01_row14 : ∀ k : Fin 20, (B0 * B1) 14 k = (B1 * B0) 14 k := by decide +kernel
lemma commute_01_row15 : ∀ k : Fin 20, (B0 * B1) 15 k = (B1 * B0) 15 k := by decide +kernel
lemma commute_01_row16 : ∀ k : Fin 20, (B0 * B1) 16 k = (B1 * B0) 16 k := by decide +kernel
lemma commute_01_row17 : ∀ k : Fin 20, (B0 * B1) 17 k = (B1 * B0) 17 k := by decide +kernel
lemma commute_01_row18 : ∀ k : Fin 20, (B0 * B1) 18 k = (B1 * B0) 18 k := by decide +kernel
lemma commute_01_row19 : ∀ k : Fin 20, (B0 * B1) 19 k = (B1 * B0) 19 k := by decide +kernel
lemma commute_01 : B0 * B1 = B1 * B0 := by
  ext i j
  fin_cases i
  · exact commute_01_row0 j
  · exact commute_01_row1 j
  · exact commute_01_row2 j
  · exact commute_01_row3 j
  · exact commute_01_row4 j
  · exact commute_01_row5 j
  · exact commute_01_row6 j
  · exact commute_01_row7 j
  · exact commute_01_row8 j
  · exact commute_01_row9 j
  · exact commute_01_row10 j
  · exact commute_01_row11 j
  · exact commute_01_row12 j
  · exact commute_01_row13 j
  · exact commute_01_row14 j
  · exact commute_01_row15 j
  · exact commute_01_row16 j
  · exact commute_01_row17 j
  · exact commute_01_row18 j
  · exact commute_01_row19 j

lemma commute_02_row2 : ∀ k : Fin 20, (B0 * B2) 2 k = (B2 * B0) 2 k := by decide +kernel
lemma commute_02_row3 : ∀ k : Fin 20, (B0 * B2) 3 k = (B2 * B0) 3 k := by decide +kernel
lemma commute_02_row4 : ∀ k : Fin 20, (B0 * B2) 4 k = (B2 * B0) 4 k := by decide +kernel
lemma commute_02_row5 : ∀ k : Fin 20, (B0 * B2) 5 k = (B2 * B0) 5 k := by decide +kernel
lemma commute_02_row6 : ∀ k : Fin 20, (B0 * B2) 6 k = (B2 * B0) 6 k := by decide +kernel
lemma commute_02_row7 : ∀ k : Fin 20, (B0 * B2) 7 k = (B2 * B0) 7 k := by decide +kernel
lemma commute_02_row8 : ∀ k : Fin 20, (B0 * B2) 8 k = (B2 * B0) 8 k := by decide +kernel
lemma commute_02_row9 : ∀ k : Fin 20, (B0 * B2) 9 k = (B2 * B0) 9 k := by decide +kernel
lemma commute_02_row11 : ∀ k : Fin 20, (B0 * B2) 11 k = (B2 * B0) 11 k := by decide +kernel
lemma commute_02_row12 : ∀ k : Fin 20, (B0 * B2) 12 k = (B2 * B0) 12 k := by decide +kernel
lemma commute_02_row13 : ∀ k : Fin 20, (B0 * B2) 13 k = (B2 * B0) 13 k := by decide +kernel
lemma commute_02_row14 : ∀ k : Fin 20, (B0 * B2) 14 k = (B2 * B0) 14 k := by decide +kernel
lemma commute_02_row15 : ∀ k : Fin 20, (B0 * B2) 15 k = (B2 * B0) 15 k := by decide +kernel
lemma commute_02_row16 : ∀ k : Fin 20, (B0 * B2) 16 k = (B2 * B0) 16 k := by decide +kernel
lemma commute_02_row17 : ∀ k : Fin 20, (B0 * B2) 17 k = (B2 * B0) 17 k := by decide +kernel
lemma commute_02_row18 : ∀ k : Fin 20, (B0 * B2) 18 k = (B2 * B0) 18 k := by decide +kernel
lemma commute_02_row19 : ∀ k : Fin 20, (B0 * B2) 19 k = (B2 * B0) 19 k := by decide +kernel

lemma commute_12_row0 : ∀ k : Fin 20, (B1 * B2) 0 k = (B2 * B1) 0 k := by decide +kernel
lemma commute_12_row1 : ∀ k : Fin 20, (B1 * B2) 1 k = (B2 * B1) 1 k := by decide +kernel

end DimensionTen.Border

end
end

end OAI
end

section
-- module Solutions.OAIQ033_DT.Quantum_DimensionTen_Annihilator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Matrix Polynomial
namespace DimensionTen.Border

lemma propagate_zero {T B : Matrix (Fin 20) (Fin 20) ℤ} {u v : Fin 20 → ℤ}
    (hc : Commute T B) (hu : T *ᵥ u = 0) (hb : B *ᵥ u = d • v) : T *ᵥ v = 0 := by
  have hd : d ≠ 0 := by norm_num [d, PencilAlgebra.denominator]
  have h : d • (T *ᵥ v) = 0 := by
    rw [← Matrix.mulVec_smul, ← hb, Matrix.mulVec_mulVec, hc.eq,
      ← Matrix.mulVec_mulVec, hu, Matrix.mulVec_zero]
  exact (smul_eq_zero.mp h).resolve_left hd

lemma shift_2 : B1 *ᵥ (Pi.single 0 1 : Fin 20 → ℤ) = d • Pi.single 2 1 := by decide +kernel
lemma shift_3 : B0 *ᵥ (Pi.single 0 1 : Fin 20 → ℤ) = d • Pi.single 3 1 := by decide +kernel
lemma shift_4 : B2 *ᵥ (Pi.single 1 1 : Fin 20 → ℤ) = d • Pi.single 4 1 := by decide +kernel
lemma shift_5 : B1 *ᵥ (Pi.single 1 1 : Fin 20 → ℤ) = d • Pi.single 5 1 := by decide +kernel
lemma shift_6 : B1 *ᵥ (Pi.single 2 1 : Fin 20 → ℤ) = d • Pi.single 6 1 := by decide +kernel
lemma shift_7 : B0 *ᵥ (Pi.single 1 1 : Fin 20 → ℤ) = d • Pi.single 7 1 := by decide +kernel
lemma shift_8 : B0 *ᵥ (Pi.single 2 1 : Fin 20 → ℤ) = d • Pi.single 8 1 := by decide +kernel
lemma shift_9 : B0 *ᵥ (Pi.single 3 1 : Fin 20 → ℤ) = d • Pi.single 9 1 := by decide +kernel
lemma shift_10 : B2 *ᵥ (Pi.single 4 1 : Fin 20 → ℤ) = d • Pi.single 10 1 := by decide +kernel
lemma shift_11 : B1 *ᵥ (Pi.single 4 1 : Fin 20 → ℤ) = d • Pi.single 11 1 := by decide +kernel
lemma shift_12 : B1 *ᵥ (Pi.single 5 1 : Fin 20 → ℤ) = d • Pi.single 12 1 := by decide +kernel
lemma shift_13 : B1 *ᵥ (Pi.single 6 1 : Fin 20 → ℤ) = d • Pi.single 13 1 := by decide +kernel
lemma shift_14 : B0 *ᵥ (Pi.single 4 1 : Fin 20 → ℤ) = d • Pi.single 14 1 := by decide +kernel
lemma shift_15 : B0 *ᵥ (Pi.single 5 1 : Fin 20 → ℤ) = d • Pi.single 15 1 := by decide +kernel
lemma shift_16 : B0 *ᵥ (Pi.single 6 1 : Fin 20 → ℤ) = d • Pi.single 16 1 := by decide +kernel
lemma shift_17 : B0 *ᵥ (Pi.single 7 1 : Fin 20 → ℤ) = d • Pi.single 17 1 := by decide +kernel
lemma shift_18 : B0 *ᵥ (Pi.single 8 1 : Fin 20 → ℤ) = d • Pi.single 18 1 := by decide +kernel
lemma shift_19 : B0 *ᵥ (Pi.single 9 1 : Fin 20 → ℤ) = d • Pi.single 19 1 := by decide +kernel

end DimensionTen.Border

end
end

end OAI
end

section
-- module Solutions.OAIQ033_DT.Quantum_DimensionTen_NormalizedMatrices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Matrix Polynomial
namespace DimensionTen.Border

def NB (i : Fin 3) : Matrix (Fin 20) (Fin 20) ℚ :=
  ((d : ℚ)⁻¹) • ((![B0, B1, B2] i).map (Int.castRingHom ℚ))

lemma dQ_ne_zero : (d : ℚ) ≠ 0 := by norm_num [d, PencilAlgebra.denominator]

end DimensionTen.Border

end
end

end OAI
end

section
-- module Solutions.OAIQ033_DT.Quantum_DimensionTen_BorderField
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Matrix Polynomial
namespace DimensionTen.Border

lemma eQ_ne : eQ 0 ≠ 0 := by
  intro h
  have hh := congrFun h 0
  simp [eQ] at hh

lemma QB_eq : B0.map (Int.castRingHom ℚ) = (d : ℚ) • NB 0 := by
  change _ = (d : ℚ) • ((d : ℚ)⁻¹ • B0.map (Int.castRingHom ℚ))
  rw [smul_smul, mul_inv_cancel₀ dQ_ne_zero, one_smul]

end DimensionTen.Border

end
end

end OAI
end

section
-- module Solutions.OAIQ033_DT.Quantum_DimensionTen_MinorData
attribute [-instance] _root_.OAI.DimensionTen.Mod41.instFactPrimeOfNatNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Matrix
namespace DimensionTen.Border

def rowChoices : Fin 15 → Fin 4 → Fin 6 := PencilAlgebra.rows

def minor {R : Type*} [CommRing R] (x : Fin 4 → R) (i : Fin 15) : R :=
  ((pencilR x).submatrix (rowChoices i) id).det

end DimensionTen.Border

end
end

end OAI
end

section
-- module Solutions.OAIQ033_DT.Quantum_DimensionTen_Cofactors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Matrix
namespace DimensionTen.Border

def cofactorKernel {R : Type*} [CommRing R] (x : Fin 4 → R) : Fin 4 → R :=
  fun j => ((pencilR x).submatrix (rowChoices 0) id).adjugate j 3

end DimensionTen.Border

end
end

end OAI
end

section
-- module Solutions.OAIQ033_DT.Quantum_DimensionTen_QuadraticBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Matrix
namespace DimensionTen.Border

def quadraticIndex (i : Fin 10) : QuadraticIndex :=
  ⟨quadraticPairs i, by fin_cases i <;> decide⟩

lemma quadraticIndex_bijective : Function.Bijective quadraticIndex := by decide

end DimensionTen.Border

end
end

end OAI
end


