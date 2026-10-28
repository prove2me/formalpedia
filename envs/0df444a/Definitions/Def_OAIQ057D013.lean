-- Prove2me | Definitions.Def_OAIQ057D013
-- name    : OAIQ057D013
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T21:25:43.911918+00:00
-- url     : https://prove2.me/theorems/128c8f03-350e-47c7-b48a-e59a08af2d96
-- title:
--   Definitions bundle OAIQ057D013 of the split of OpenAI, Entanglement without distillable secret key in local dimension ten (result family 272)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.DimensionTen.exists_channel_fin21`, carved from OpenAI's openai/math development (OpenAI, *Entanglement without distillable secret key in local dimension ten (result family 272)*, OpenAI Math Release, September 27, 2026, result family 272, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 14 declarations of OpenAI's Lean: 4 definitions and 10 theorems. The definitions and types are `OAI.DimensionTen.PublishedChoi21`, `OAI.DimensionTen.channel`, `OAI.DimensionTen.channel21`, `OAI.DimensionTen.phiTwoLinear`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, lean/OAI/InformationTheory, in whole or in part: [`DimensionTen_ChoiTransfer`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/InformationTheory/DimensionTen/ChoiTransfer.lean), [`Quantum_DimensionTen_Channel`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Quantum/DimensionTen/Channel.lean), [`Quantum_DimensionTen_ExteriorMaps`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Quantum/DimensionTen/ExteriorMaps.lean), [`Quantum_DimensionTen_Kraus`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Quantum/DimensionTen/Kraus.lean), [`Quantum_DimensionTen_PencilKraus`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Quantum/DimensionTen/PencilKraus.lean).
--
--   **Imports.** It imports the published bundle `Def_DimensionTenChannel`; the bundles `OAIQ057D011` and `OAIQ057D012` of this split.
--
--   **Imported by** (directly, in this split): the statements `OAI_DimensionTen_linear_composite_not_separable`, `OAI.DimensionTen.linear_composite_not_separable_s2`, `OAI_DimensionTen_main_channel_conditional` and `OAI.DimensionTen.main_channel_conditional_s2`; the proofs of `OAI_DimensionTen_compositeChoi_veronese`, `OAI.DimensionTen.compositeChoi_veronese_s2`, `OAI.DimensionTen.exists_channel_fin21`, `OAI_DimensionTen_linear_composite_not_separable`, `OAI.DimensionTen.linear_composite_not_separable_s2`, `OAI_DimensionTen_main_channel_conditional` and `OAI.DimensionTen.main_channel_conditional_s2`.
-- source:
--   OpenAI, Entanglement without distillable secret key in local dimension ten (result family 272), OpenAI Math Release, September 27, 2026, https://github.com/openai/math (result family 272; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Entanglement-with-zero-distillable-secret-key-in-local-dimension-ten-September-27-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis, lean/OAI/InformationTheory at commit adc7f12

import Mathlib
import Definitions.Def_DimensionTenChannel
import Definitions.Def_OAIQ057D011
import Definitions.Def_OAIQ057D012

section
-- module Solutions.OAIQ057_CH.Quantum_DimensionTen_Kraus
attribute [-instance] _root_.OAI.DimensionTen.Mod41.instFactPrimeOfNatNat_solutions _root_.OAI.ZeroKey.matrixMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Matrix ComplexOrder Kronecker
open Matrix
namespace DimensionTen

lemma krausMap_adjoint {r : Type*} [Fintype r] {a b : ℕ}
    (Q : r → Matrix (Fin b) (Fin a) ℂ) :
    hsAdjoint (krausMap Q) = krausMap (fun k => (Q k)ᴴ) := by
  funext A
  ext i j
  change (∑ u, ∑ v, star (krausMap Q (Matrix.single i j 1) u v) * A u v) = _
  simp only [krausMap_single]
  simp only [krausMap_entry,
    star_sum, star_mul', star_star, Matrix.conjTranspose_apply,
    Finset.sum_mul]
  conv_lhs => rw [Finset.sum_comm]; arg 2; ext v; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u hu
  apply Finset.sum_congr rfl
  intro v hv
  ring

end DimensionTen

end
end

end OAI
end

section
-- module Solutions.OAIQ057_CH.Quantum_DimensionTen_PencilKraus
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

lemma pencilMap_input_transpose (A : Mat 4) : pencilMap Aᵀ = pencilMap A := by
  simp only [pencilMap, Matrix.transpose_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [blocks_transpose_mul_comm j i]

end DimensionTen

end
end

end OAI
end

section
-- module Solutions.OAIQ057_CH.Quantum_DimensionTen_ExteriorMaps
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

lemma exteriorMap_output_transpose (A : Mat 10) : (exteriorMap A)ᵀ = exteriorMap A := by
  unfold exteriorMap
  rw [real_compression_transpose _ exteriorIsometry_real]
  rw [tensorMap_output_transpose _ _ pencilMap_output_transpose pencilMap_output_transpose]

lemma exteriorMap_input_transpose (A : Mat 10) : exteriorMap Aᵀ = exteriorMap A := by
  unfold exteriorMap
  rw [← real_embedding_transpose _ symmetricIsometry_real]
  rw [tensorMap_input_transpose _ _ pencilMap_input_transpose pencilMap_input_transpose]

lemma complementaryMap_kraus : complementaryMap = krausMap complementaryKraus := by
  funext A
  unfold complementaryMap
  rw [exteriorMap_output_transpose, exteriorMap_kraus, krausMap_postconjugate]
  rfl

lemma complementaryMap_input_transpose (A : Mat 10) : complementaryMap Aᵀ = complementaryMap A := by
  simp only [complementaryMap, exteriorMap_input_transpose]

lemma phiTwo_kraus : phiTwo = krausMap phiTwoKraus := by
  funext A
  unfold phiTwo
  rw [complementaryMap_kraus, krausMap_adjoint]
  have h := krausMap_preconjugate (fun k => (complementaryKraus k)ᴴ) firstSixᴴ A
  unfold phiTwoKraus
  simpa only [Matrix.conjTranspose_conjTranspose] using h

lemma phiTwo_output_transpose (A : Mat 10) : (phiTwo A)ᵀ = phiTwo A :=
  hsAdjoint_output_transpose _ complementaryMap_input_transpose _

lemma phiTwo_ppt : PPT phiTwo := by
  refine ⟨?_, ?_, ?_⟩
  · rw [phiTwo_kraus]; exact krausMap_linear _
  · rw [phiTwo_kraus]; exact krausMap_cp _
  · simp only [phiTwo_output_transpose]
    rw [phiTwo_kraus]; exact krausMap_cp _

end DimensionTen

end
end

end OAI
end

section
-- module Solutions.OAIQ057_CH.DimensionTen_ChoiTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Transpose-adjoint transfer for the explicit dimension-ten maps. -/

noncomputable section
open Matrix MeasureTheory Filter
open scoped ComplexOrder Kronecker ENNReal

namespace DimensionTen
universe u

def phiTwoLinear : Mat 10 →ₗ[ℂ] Mat 10 := asLinearMap phiTwo phiTwo_ppt.1

end DimensionTen

end

end OAI
end

section
-- module Solutions.OAIQ057_CH.Quantum_DimensionTen_Channel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A trace-preserving PPT channel with an entangled square, from the dimension-ten pair. -/

noncomputable section

open scoped BigOperators Matrix Kronecker ComplexOrder MatrixOrder
open Matrix

namespace DimensionTen

@[simp] lemma phiTwoLinear_apply (A : Mat 10) : phiTwoLinear A = phiTwo A := rfl

def channel : ChannelCompletion.Map (ChannelCompletion.Space 10)
    (ChannelCompletion.Space 10) :=
  ChannelCompletion.theta 10 phiOneLinear phiTwoLinear

def channel21 : ChannelCompletion.Map (Fin 21) (Fin 21) :=
  ChannelCompletion.rename ExplicitPencil.orderedCoordinates.symm channel

def PublishedChoi21 : Prop :=
  ChannelCompletion.EntanglementBreaking (channel.comp channel) →
    ChannelCompletion.Separable (ChannelCompletion.choi (channel.comp channel))

end DimensionTen

end

end OAI
end


