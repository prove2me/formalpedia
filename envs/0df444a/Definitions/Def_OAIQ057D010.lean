-- Prove2me | Definitions.Def_OAIQ057D010
-- name    : OAIQ057D010
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T20:47:29.534091+00:00
-- url     : https://prove2.me/theorems/babe8d45-c76e-42e4-87b4-5760f5a0495a
-- title:
--   Definitions bundle OAIQ057D010 of the split of OpenAI, Entanglement without distillable secret key in local dimension ten (result family 272)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.DimensionTen.exists_channel_fin21`, carved from OpenAI's openai/math development (OpenAI, *Entanglement without distillable secret key in local dimension ten (result family 272)*, OpenAI Math Release, September 27, 2026, result family 272, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 16 declarations of OpenAI's Lean: 9 definitions and 7 theorems. The definitions and types are `OAI.DimensionTen.choi`, `OAI.DimensionTen.compound`, `OAI.DimensionTen.quadraticEval`, `OAI.DimensionTen.separable`, `OAI.DimensionTen.symmetricEquiv`, `OAI.DimensionTen.symmetricIndex`, `OAI.DimensionTen.veronese`, `OAI.DimensionTen.veroneseCoeffs`, `OAI.ExplicitPencil.orderedCoordinates`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, lean/OAI/InformationTheory, in whole or in part: [`Quantum_DimensionTen_CompoundTrace`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Quantum/DimensionTen/CompoundTrace.lean), [`Quantum_DimensionTen_PencilModel`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Quantum/DimensionTen/PencilModel.lean), [`Quantum_DimensionTen_TensorKraus`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Quantum/DimensionTen/TensorKraus.lean), [`Quantum_DimensionTen_TensorSymmetry`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Quantum/DimensionTen/TensorSymmetry.lean), [`Quantum_DimensionTen_Veronese`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Quantum/DimensionTen/Veronese.lean), [`Quantum_PPTSquare_OrderedChannel`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Quantum/PPTSquare/OrderedChannel.lean).
--
--   **Imports.** It imports the bundles `OAIQ057D000`, `OAIQ057D003` and `OAIQ057D006` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ057D011`.
-- source:
--   OpenAI, Entanglement without distillable secret key in local dimension ten (result family 272), OpenAI Math Release, September 27, 2026, https://github.com/openai/math (result family 272; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Entanglement-with-zero-distillable-secret-key-in-local-dimension-ten-September-27-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis, lean/OAI/InformationTheory at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ057D000
import Definitions.Def_OAIQ057D003
import Definitions.Def_OAIQ057D006

section
-- module Solutions.OAIQ057_CH.Quantum_DimensionTen_PencilModel
attribute [-instance] _root_.OAI.DimensionTen.Mod41.instFactPrimeOfNatNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Matrix ComplexOrder
open Matrix Complex

namespace DimensionTen

def quadraticEval (q : QuadraticIndex → ℂ) (x : Fin 4 → ℂ) : ℂ :=
  ∑ ij : QuadraticIndex, q ij * x ij.val.1 * x ij.val.2




def separable {a b : ℕ} (X : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) : Prop :=
  ∃ r : ℕ, ∃ A : Fin r → Mat a, ∃ B : Fin r → Mat b,
    (∀ i, (A i).PosSemidef ∧ (B i).PosSemidef) ∧
    X = ∑ i, Matrix.kronecker (A i) (B i)

def choi {a b : ℕ} (F : Mat a → Mat b) :
    Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ :=
  fun u v => F (Matrix.single u.1 v.1 1) u.2 v.2


theorem blocksZ_transpose_mul_comm (i j : Fin 4) :
    (blocksZ i)ᵀ * blocksZ j = (blocksZ j)ᵀ * blocksZ i := by
  decide +revert


end DimensionTen

end
end

end OAI
end

section
-- module Solutions.OAIQ057_CH.Quantum_DimensionTen_TensorSymmetry
attribute [-instance] _root_.OAI.DimensionTen.Mod41.instFactPrimeOfNatNat_solutions
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

lemma symmetricIsometry_real : symmetricIsometryᴴ = symmetricIsometryᵀ := by
  ext i j
  simp [symmetricIsometry, Matrix.conjTranspose_apply, apply_ite star]

lemma exteriorIsometry_real : exteriorIsometryᴴ = exteriorIsometryᵀ := by
  ext i j
  simp [exteriorIsometry, Matrix.conjTranspose_apply]

end DimensionTen

end
end

end OAI
end

section
-- module Solutions.OAIQ057_CH.Quantum_DimensionTen_Veronese
attribute [-instance] _root_.OAI.DimensionTen.Mod41.instFactPrimeOfNatNat_solutions
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

def veronese (x : Fin 4 → ℂ) (i : Fin 10) : ℂ :=
  let p := (symmetricPairs i).1
  let q := (symmetricPairs i).2
  (if p = q then 1 else (Real.sqrt 2 : ℂ)) * x p * x q

def symmetricIndex (i : Fin 10) : QuadraticIndex :=
  ⟨symmetricPairs i, by fin_cases i <;> decide⟩

lemma symmetricIndex_bijective : Function.Bijective symmetricIndex := by decide

def symmetricEquiv : Fin 10 ≃ QuadraticIndex :=
  Equiv.ofBijective symmetricIndex symmetricIndex_bijective

def veroneseCoeffs (u : Fin 10 → ℂ) (ij : QuadraticIndex) : ℂ :=
  star (u (symmetricEquiv.symm ij)) *
    (if ij.val.1 = ij.val.2 then 1 else (Real.sqrt 2 : ℂ))

end DimensionTen

end
end

end OAI
end

section
-- module Solutions.OAIQ057_CH.Quantum_DimensionTen_CompoundTrace
attribute [-instance] _root_.OAI.DimensionTen.Mod41.instFactPrimeOfNatNat_solutions
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

def compound (B : Mat 4) : Mat 6 := fun i j =>
  B (exteriorPairs i).1 (exteriorPairs j).1 * B (exteriorPairs i).2 (exteriorPairs j).2 -
  B (exteriorPairs i).1 (exteriorPairs j).2 * B (exteriorPairs i).2 (exteriorPairs j).1

end DimensionTen

end
end

end OAI
end

section
-- module Solutions.OAIQ057_CH.Quantum_DimensionTen_TensorKraus
attribute [-instance] _root_.OAI.DimensionTen.Mod41.instFactPrimeOfNatNat_solutions
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

lemma krausMap_conjugate {r a b c d : Type*} [Fintype r] [Fintype a] [Fintype b]
    [Fintype c] (Q : r → Matrix b a ℂ) (U : Matrix a c ℂ) (V : Matrix d b ℂ)
    (A : Matrix c c ℂ) :
    V * krausMap Q (U * A * Uᴴ) * Vᴴ =
      krausMap (fun k => V * Q k * U) A := by
  simp only [krausMap, Matrix.mul_sum, Matrix.sum_mul, Matrix.conjTranspose_mul]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [Matrix.mul_assoc]

lemma krausMap_postconjugate {r a b c : Type*} [Fintype r] [Fintype a] [Fintype b]
    (Q : r → Matrix b a ℂ) (V : Matrix c b ℂ) (A : Matrix a a ℂ) :
    V * krausMap Q A * Vᴴ = krausMap (fun k => V * Q k) A := by
  simp only [krausMap, Matrix.mul_sum, Matrix.sum_mul, Matrix.conjTranspose_mul]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [Matrix.mul_assoc]

lemma krausMap_preconjugate {r a b c : Type*} [Fintype r] [Fintype a] [Fintype c]
    (Q : r → Matrix b a ℂ) (U : Matrix a c ℂ) (A : Matrix c c ℂ) :
    krausMap Q (U * A * Uᴴ) = krausMap (fun k => Q k * U) A := by
  simp only [krausMap, Matrix.conjTranspose_mul]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [Matrix.mul_assoc]

end DimensionTen

end
end

end OAI
end

section
-- module Solutions.OAIQ057_CH.Quantum_PPTSquare_OrderedChannel
attribute [-instance] _root_.OAI.DimensionTen.Mod41.instFactPrimeOfNatNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
open Matrix
namespace ExplicitPencil
open ChannelCompletion

def orderedCoordinates : Space 10 ≃ Fin 21 :=
  (Equiv.sumCongr (finSumFinEquiv : (Fin 10 ⊕ Fin 10) ≃ Fin 20)
    (Equiv.ofUnique Unit (Fin 1))).trans finSumFinEquiv
end ExplicitPencil

end

end OAI
end


