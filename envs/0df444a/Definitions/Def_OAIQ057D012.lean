-- Prove2me | Definitions.Def_OAIQ057D012
-- name    : OAIQ057D012
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T21:13:49.265989+00:00
-- url     : https://prove2.me/theorems/20d5d07f-2d8a-4313-92d1-6aaf7c793119
-- title:
--   Definitions bundle OAIQ057D012 of the split of OpenAI, Entanglement without distillable secret key in local dimension ten (result family 272)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.DimensionTen.exists_channel_fin21`, carved from OpenAI's openai/math development (OpenAI, *Entanglement without distillable secret key in local dimension ten (result family 272)*, OpenAI Math Release, September 27, 2026, result family 272, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 3 declarations of OpenAI's Lean: 3 theorems.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, lean/OAI/InformationTheory, in whole or in part: [`Quantum_DimensionTen_TensorSymmetry`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Quantum/DimensionTen/TensorSymmetry.lean).
--
--   **Imports.** It imports the bundle `OAIQ057D009` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ057D013`.
-- source:
--   OpenAI, Entanglement without distillable secret key in local dimension ten (result family 272), OpenAI Math Release, September 27, 2026, https://github.com/openai/math (result family 272; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Entanglement-with-zero-distillable-secret-key-in-local-dimension-ten-September-27-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis, lean/OAI/InformationTheory at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ057D009

section
-- module Solutions.OAIQ057_CH.Quantum_DimensionTen_TensorSymmetry
attribute [-instance] _root_.OAI.DimensionTen.Mod41.instFactPrimeOfNatNat_solutions _root_.OAI.ZeroKey.matrixMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Matrix Kronecker ComplexOrder
open Matrix
namespace DimensionTen

lemma tensorMap_output_transpose {a b c d : ℕ} (F : Mat a → Mat b) (G : Mat c → Mat d)
    (hF : ∀ A, (F A)ᵀ = F A) (hG : ∀ A, (G A)ᵀ = G A)
    (X : Matrix (Fin a × Fin c) (Fin a × Fin c) ℂ) :
    (tensorMap F G X)ᵀ = tensorMap F G X := by
  simp only [tensorMap, Matrix.kronecker, Matrix.transpose_sum, kronecker_transpose, hG]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  erw [hF]

lemma tensorMap_input_transpose {a b c d : ℕ} (F : Mat a → Mat b) (G : Mat c → Mat d)
    (hF : ∀ A, F Aᵀ = F A) (hG : ∀ A, G Aᵀ = G A)
    (X : Matrix (Fin a × Fin c) (Fin a × Fin c) ℂ) :
    tensorMap F G Xᵀ = tensorMap F G X := by
  unfold tensorMap
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  have hb : (fun a b => Xᵀ (a, j) (b, i)) =
      (Matrix.of (fun a b => X (a, i) (b, j)))ᵀ := rfl
  rw [hb, hF]
  have hg : G (Matrix.single j i 1) = G (Matrix.single i j 1) := by
    have ht : (Matrix.single i j (1 : ℂ))ᵀ = Matrix.single j i 1 := by
      simp only [Matrix.transpose_single]
    rw [← ht, hG]
  rw [hg]
  rfl

lemma hsAdjoint_output_transpose {a b : ℕ} (F : Mat a → Mat b)
    (h : ∀ A, F Aᵀ = F A) (Y : Mat b) :
    (hsAdjoint F Y)ᵀ = hsAdjoint F Y := by
  ext i j
  change (∑ u, ∑ v, star (F (Matrix.single j i 1) u v) * Y u v) = _
  have he : F (Matrix.single j i 1) = F (Matrix.single i j 1) := by
    rw [← Matrix.transpose_single, h]
  rw [he]
  rfl

end DimensionTen

end
end

end OAI
end


