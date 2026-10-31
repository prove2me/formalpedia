-- Prove2me | Definitions.Def_OAIQ019N044
-- name    : OAIQ019N044
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T07:28:36.559148+00:00
-- url     : https://prove2.me/theorems/c6ee63db-15b1-4c05-8aba-970b7b2b4b66
-- title:
--   Definitions bundle OAIQ019N044 of the split of OpenAI, An explicit obstruction to nuclear norm-ultrapower embeddings (result family 292)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.NuclearUltrapower.main_no_embedding`, carved from OpenAI's openai/math development (OpenAI, *An explicit obstruction to nuclear norm-ultrapower embeddings (result family 292)*, OpenAI Math Release, September 23, 2026, result family 292, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 45 declarations of OpenAI's Lean: 35 definitions, 1 instance and 9 theorems. The definitions and types are `OAI.NuclearUltrapower.Elementary.augmentation`, `OAI.NuclearUltrapower.Elementary.augmentationRep`, `OAI.NuclearUltrapower.Elementary.augmentationVector`, `OAI.NuclearUltrapower.Elementary.elementaryTransvection`, `OAI.NuclearUltrapower.Elementary.integralInclusion`, `OAI.NuclearUltrapower.Elementary.kazhdanSet`, `OAI.NuclearUltrapower.Elementary.linearInclusion`, `OAI.NuclearUltrapower.Elementary.thetaCosetEquiv`, `OAI.NuclearUltrapower.Elementary.transvectionHom`, `OAI.NuclearUltrapower.SOS.ElementarySpectral.deltaOp`, `OAI.NuclearUltrapower.SOS.ElementarySpectral.gramOp`, `OAI.NuclearUltrapower.SOS.ElementarySpectral.residualInE`, `OAI.NuclearUltrapower.SOS.ElementarySpectral.value`, `OAI.NuclearUltrapower.SOS.ElementarySpectral.vectorStabilizer`, `OAI.NuclearUltrapower.SOS.GoodWord`, `OAI.NuclearUltrapower.SOS.basisWords`, `OAI.NuclearUltrapower.SOS.eGenSet`, `OAI.NuclearUltrapower.SOS.eInterpret`, `OAI.NuclearUltrapower.SOS.generator0`, `OAI.NuclearUltrapower.SOS.generator1`, `OAI.NuclearUltrapower.SOS.generator10`, `OAI.NuclearUltrapower.SOS.generator11`, `OAI.NuclearUltrapower.SOS.generator2`, `OAI.NuclearUltrapower.SOS.generator3`, `OAI.NuclearUltrapower.SOS.generator4`, `OAI.NuclearUltrapower.SOS.generator5`, `OAI.NuclearUltrapower.SOS.generator6`, `OAI.NuclearUltrapower.SOS.generator7`, `OAI.NuclearUltrapower.SOS.generator8`, `OAI.NuclearUltrapower.SOS.generator9`, `OAI.NuclearUltrapower.SOS.gramPolyRow`, `OAI.NuclearUltrapower.SOS.gramValue`, `OAI.NuclearUltrapower.SOS.matrixWord`, `OAI.NuclearUltrapower.SOS.residualRows`, `OAI.NuclearUltrapower.SOS.rootPairs`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`NuclearUltrapower_IntegerMatrices`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/NuclearUltrapower/IntegerMatrices.lean), [`NuclearUltrapower_IntegralCertificate`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/NuclearUltrapower/IntegralCertificate.lean), [`NuclearUltrapower_Kazhdan`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/NuclearUltrapower/Kazhdan.lean), [`NuclearUltrapower_SOSGap`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/NuclearUltrapower/SOSGap.lean), [`NuclearUltrapower_SOSResidual`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/NuclearUltrapower/SOSResidual.lean).
--
--   **Imports.** It imports the published bundle `Def_NuclearUltrapower`; the bundles `OAIQ019N049` and `OAIQ019N043` of this split.
--
--   **Imported by** (directly, in this split): the statements `OAI.NuclearUltrapower.Elementary.kazhdanSet_generates`, `OAI.NuclearUltrapower.SOS.ElementarySpectral.deltaOp_certificate`, `OAI.NuclearUltrapower.SOS.ElementarySpectral.deltaOp_gap`, `OAI.NuclearUltrapower.SOS.ElementarySpectral.deltaOp_nonneg`, `OAI.NuclearUltrapower.SOS.ElementarySpectral.deltaOp_sq_gap`, `OAI.NuclearUltrapower.SOS.ElementarySpectral.delta_energy`, `OAI.NuclearUltrapower.SOS.ElementarySpectral.delta_eq_half_laplacian`, `OAI.NuclearUltrapower.SOS.ElementarySpectral.delta_value`, `OAI.NuclearUltrapower.SOS.ElementarySpectral.exists_fixed_nearby`, `OAI.NuclearUltrapower.SOS.ElementarySpectral.genList_nodup`, `OAI.NuclearUltrapower.SOS.ElementarySpectral.gramOp_nonneg`, `OAI.NuclearUltrapower.SOS.ElementarySpectral.residualInE_aug`, `OAI.NuclearUltrapower.SOS.ElementarySpectral.residualInE_l1`, `OAI.NuclearUltrapower.SOS.ElementarySpectral.residualInE_operator`, `OAI.NuclearUltrapower.SOS.ElementarySpectral.residualInE_support`, `OAI.NuclearUltrapower.SOS.ElementarySpectral.residual_value_native`, `OAI.NuclearUltrapower.SOS.ElementarySpectral.sum_gen_star`, `OAI.NuclearUltrapower.SOS.ElementarySpectral.value_inv`, `OAI.NuclearUltrapower.SOS.ElementarySpectral.value_mul`, `OAI.NuclearUltrapower.SOS.basis_good`, `OAI.NuclearUltrapower.SOS.delta_good`, `OAI.NuclearUltrapower.SOS.eWord`, `OAI.NuclearUltrapower.SOS.eval_gram_rows`, `OAI.NuclearUltrapower.SOS.gramPolyRow_good`, `OAI.NuclearUltrapower.SOS.residualRows_good`, `OAI.NuclearUltrapower.SOS.residual_eval` and `OAI.NuclearUltrapower.SOS.residual_value_generic`; the proofs of `OAI.NuclearUltrapower.Elementary.kazhdanSet_generates`, `OAI.NuclearUltrapower.SOS.ElementarySpectral.deltaOp_certificate`, `OAI.NuclearUltrapower.SOS.ElementarySpectral.deltaOp_gap`, `OAI.NuclearUltrapower.SOS.ElementarySpectral.deltaOp_nonneg`, `OAI.NuclearUltrapower.SOS.ElementarySpectral.deltaOp_sq_gap`, `OAI.NuclearUltrapower.SOS.ElementarySpectral.delta_energy`, `OAI.NuclearUltrapower.SOS.ElementarySpectral.delta_eq_half_laplacian`, `OAI.NuclearUltrapower.SOS.ElementarySpectral.delta_value`, `OAI.NuclearUltrapower.SOS.ElementarySpectral.exists_fixed_nearby`, `OAI.NuclearUltrapower.SOS.ElementarySpectral.genList_nodup`, `OAI.NuclearUltrapower.SOS.ElementarySpectral.gramOp_nonneg`, `OAI.NuclearUltrapower.SOS.ElementarySpectral.residualInE_aug`, `OAI.NuclearUltrapower.SOS.ElementarySpectral.residualInE_l1`, `OAI.NuclearUltrapower.SOS.ElementarySpectral.residualInE_operator`, `OAI.NuclearUltrapower.SOS.ElementarySpectral.residualInE_support`, `OAI.NuclearUltrapower.SOS.ElementarySpectral.residual_value_native`, `OAI.NuclearUltrapower.SOS.ElementarySpectral.sum_gen_star`, `OAI.NuclearUltrapower.SOS.ElementarySpectral.value_inv`, `OAI.NuclearUltrapower.SOS.ElementarySpectral.value_mul`, `OAI.NuclearUltrapower.SOS.basis_good`, `OAI.NuclearUltrapower.SOS.delta_good`, `OAI.NuclearUltrapower.SOS.eWord`, `OAI.NuclearUltrapower.SOS.eval_gram_rows`, `OAI.NuclearUltrapower.SOS.gramPolyRow_good`, `OAI.NuclearUltrapower.SOS.residualRows_good`, `OAI.NuclearUltrapower.SOS.residual_eval`, `OAI.NuclearUltrapower.SOS.residual_value_generic` and `OAI.NuclearUltrapower.main_statement`.
-- source:
--   OpenAI, An explicit obstruction to nuclear norm-ultrapower embeddings (result family 292), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 292; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/NuclearUltrapower.lean; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit adc7f12

import Mathlib
import Definitions.Def_NuclearUltrapower
import Definitions.Def_OAIQ019N049
import Definitions.Def_OAIQ019N043

section
-- module Solutions.OAIQ019_Nuc.NuclearUltrapower_SOSResidual
attribute [-instance] _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instInvolutiveStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instSeminormedRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarAddMonoidMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.UniversalCompletion.completionInvolutiveStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionNormedAlgebra _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStarRing _root_.OAI.NuclearUltrapower.lp_finiteDimensional _root_.OAI.NuclearUltrapower.strongDualInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace NuclearUltrapower.SOS
def residualRows : List (Poly Mat3) := [residualRow0, residualRow1, residualRow2, residualRow3, residualRow4, residualRow5, residualRow6, residualRow7, residualRow8, residualRow9, residualRow10, residualRow11, residualRow12, residualRow13, residualRow14, residualRow15, residualRow16, residualRow17, residualRow18, residualRow19, residualRow20, residualRow21, residualRow22, residualRow23, residualRow24, residualRow25, residualRow26, residualRow27, residualRow28, residualRow29, residualRow30, residualRow31, residualRow32, residualRow33, residualRow34, residualRow35, residualRow36, residualRow37, residualRow38, residualRow39, residualRow40, residualRow41, residualRow42, residualRow43, residualRow44, residualRow45, residualRow46, residualRow47, residualRow48, residualRow49, residualRow50, residualRow51, residualRow52, residualRow53, residualRow54, residualRow55, residualRow56, residualRow57, residualRow58, residualRow59, residualRow60, residualRow61, residualRow62, residualRow63, residualRow64, residualRow65, residualRow66, residualRow67, residualRow68, residualRow69, residualRow70, residualRow71, residualRow72, residualRow73, residualRow74, residualRow75, residualRow76, residualRow77, residualRow78, residualRow79, residualRow80, residualRow81, residualRow82, residualRow83, residualRow84, residualRow85, residualRow86, residualRow87, residualRow88, residualRow89, residualRow90, residualRow91, residualRow92, residualRow93, residualRow94, residualRow95, residualRow96, residualRow97, residualRow98, residualRow99, residualRow100, residualRow101, residualRow102, residualRow103, residualRow104, residualRow105, residualRow106, residualRow107, residualRow108, residualRow109, residualRow110, residualRow111, residualRow112, residualRow113, residualRow114, residualRow115, residualRow116, residualRow117, residualRow118, residualRow119, residualRow120, residualRow121, residualRow122]
end NuclearUltrapower.SOS
end

end OAI
end

section
-- module Solutions.OAIQ019_Nuc.NuclearUltrapower_IntegerMatrices
attribute [-instance] _root_.OAI.NuclearUltrapower.CuntzWords.instDecidableEqWord _root_.OAI.NuclearUltrapower.CuntzWords.instFintypeWord _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instInvolutiveStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instSeminormedRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarAddMonoidMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.UniversalCompletion.completionInvolutiveStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionNormedAlgebra _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStarRing _root_.OAI.NuclearUltrapower.lp_finiteDimensional _root_.OAI.NuclearUltrapower.strongDualInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace NuclearUltrapower.SOS

def GoodWord (n : ℕ) (m : Mat3) : Prop :=
  (toMatrix m).det = 1 ∧ ∃ w : List SL, w.prod = interpret m ∧ w.length ≤ n ∧
    ∀ s ∈ w, s ∈ genSet

def matrixWord : List Mat3 → Mat3
  | [] => matOne
  | a::as => matMul a (matrixWord as)

def generator0 : Mat3 := [1, -1, 0, 0, 1, 0, 0, 0, 1]
def generator1 : Mat3 := [1, 1, 0, 0, 1, 0, 0, 0, 1]
def generator2 : Mat3 := [1, 0, -1, 0, 1, 0, 0, 0, 1]
def generator3 : Mat3 := [1, 0, 1, 0, 1, 0, 0, 0, 1]
def generator4 : Mat3 := [1, 0, 0, -1, 1, 0, 0, 0, 1]
def generator5 : Mat3 := [1, 0, 0, 1, 1, 0, 0, 0, 1]
def generator6 : Mat3 := [1, 0, 0, 0, 1, -1, 0, 0, 1]
def generator7 : Mat3 := [1, 0, 0, 0, 1, 1, 0, 0, 1]
def generator8 : Mat3 := [1, 0, 0, 0, 1, 0, -1, 0, 1]
def generator9 : Mat3 := [1, 0, 0, 0, 1, 0, 1, 0, 1]
def generator10 : Mat3 := [1, 0, 0, 0, 1, 0, 0, -1, 1]
def generator11 : Mat3 := [1, 0, 0, 0, 1, 0, 0, 1, 1]
def basisWords : List (List Mat3) := [[generator0, generator5], [generator2, generator9], [generator3, generator8], [generator1, generator4], [generator0, generator0], [generator0, generator2], [generator2, generator11], [generator0, generator7], [generator4, generator0], [generator6, generator0], [generator0, generator8], [generator8, generator0], [generator0, generator10], [generator0], [generator0, generator11], [generator9, generator0], [generator0, generator9], [generator7, generator0], [generator5, generator0], [generator0, generator6], [generator3, generator10], [generator0, generator3], [generator2, generator2], [generator2, generator4], [generator4, generator2], [generator2, generator6], [generator8, generator2], [generator10, generator2], [generator2], [generator11, generator2], [generator9, generator2], [generator2, generator7], [generator5, generator2], [generator2, generator5], [generator4, generator4], [generator4, generator6], [generator6, generator9], [generator4, generator8], [generator11, generator4], [generator4, generator10], [generator4], [generator4, generator11], [generator10, generator4], [generator4, generator9], [generator7, generator8], [generator4, generator7], [generator6, generator11], [generator7, generator10], [generator6, generator6], [generator8, generator6], [generator10, generator6], [generator6], [generator11, generator6], [generator9, generator6], [generator8, generator8], [generator8, generator10], [generator8], [generator8, generator11], [generator10, generator10], [generator10], [], [generator11], [generator11, generator11], [generator9, generator10], [generator9], [generator9, generator11], [generator9, generator9], [generator8, generator7], [generator10, generator7], [generator7], [generator11, generator7], [generator9, generator7], [generator7, generator7], [generator6, generator10], [generator7, generator11], [generator6, generator8], [generator5, generator6], [generator10, generator5], [generator5, generator8], [generator5, generator10], [generator5], [generator5, generator11], [generator5, generator9], [generator11, generator5], [generator5, generator7], [generator7, generator9], [generator5, generator5], [generator4, generator3], [generator3, generator4], [generator3, generator6], [generator8, generator3], [generator10, generator3], [generator3], [generator11, generator3], [generator9, generator3], [generator3, generator7], [generator3, generator5], [generator5, generator3], [generator3, generator3], [generator1, generator6], [generator2, generator10], [generator1, generator2], [generator4, generator1], [generator6, generator1], [generator8, generator1], [generator1, generator8], [generator1, generator10], [generator1], [generator1, generator11], [generator1, generator9], [generator9, generator1], [generator7, generator1], [generator5, generator1], [generator1, generator3], [generator3, generator11], [generator1, generator7], [generator1, generator1], [generator0, generator4], [generator2, generator8], [generator3, generator9], [generator1, generator5]]

end NuclearUltrapower.SOS
end
end

section

noncomputable section
namespace NuclearUltrapower.SOS

def eInterpret (m : Mat3) : E := by
  classical
  exact if h : interpret m ∈ elementary then ⟨interpret m, h⟩ else 1

def eGenSet : Finset E := (generators.map eInterpret).toFinset

end NuclearUltrapower.SOS
end
end

end OAI
end

section
-- module Solutions.OAIQ019_Nuc.NuclearUltrapower_SOSGap
attribute [-instance] _root_.OAI.NuclearUltrapower.CuntzWords.instDecidableEqWord _root_.OAI.NuclearUltrapower.CuntzWords.instFintypeWord _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instInvolutiveStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instSeminormedRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarAddMonoidMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.UniversalCompletion.completionInvolutiveStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionNormedAlgebra _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStarRing _root_.OAI.NuclearUltrapower.VariableUltra.instNormedRingAlgebra _root_.OAI.NuclearUltrapower.lp_finiteDimensional _root_.OAI.NuclearUltrapower.strongDualInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped ComplexOrder InnerProductSpace
namespace NuclearUltrapower.SOS.ElementarySpectral

section Algebra
variable {A : Type*} [CStarAlgebra A]

def value (ρ : E →* unitary A) (m : Mat3) : A := ρ (eInterpret m)

end Algebra

end NuclearUltrapower.SOS.ElementarySpectral
end
end

end OAI
end

section
-- module Solutions.OAIQ019_Nuc.NuclearUltrapower_IntegralCertificate
attribute [-instance] _root_.OAI.NuclearUltrapower.CuntzPolynomial.instInvolutiveStarPoly _root_.OAI.NuclearUltrapower.CuntzPolynomial.instInvolutiveStarWord _root_.OAI.NuclearUltrapower.CuntzPolynomial.instStarPoly _root_.OAI.NuclearUltrapower.CuntzPolynomial.instStarWord _root_.OAI.NuclearUltrapower.CuntzWords.instDecidableEqWord _root_.OAI.NuclearUltrapower.CuntzWords.instFintypeWord _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instInvolutiveStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instSeminormedRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarAddMonoidMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.UniversalCompletion.completionInvolutiveStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionNormedAlgebra _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStarRing _root_.OAI.NuclearUltrapower.VariableUltra.instCStarAlgebraAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instStarAlgebra _root_.OAI.NuclearUltrapower.instStarNormUltrapower _root_.OAI.NuclearUltrapower.lp_finiteDimensional _root_.OAI.NuclearUltrapower.strongDualInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace NuclearUltrapower.SOS
open NuclearUltrapower.SL3Certificate

def gramPolyRow (a : Mat3) (r : List ℤ) : Poly Mat3 :=
  (basis.zip r).map (fun q => (matMul (matInv a) q.1, -10*q.2))

def rootPairs : List (Mat3 × List ℤ) := basis.zip columns

section Operator
variable {A : Type*} [Ring A] [StarRing A]

def gramValue (f : Mat3 → A) : A :=
  (rootPairs.map (fun p =>
    (rootPairs.map (fun q => dot p.2 q.2 • (star (f p.1) * f q.1))).sum)).sum

end Operator
end NuclearUltrapower.SOS
end

section

noncomputable section
open scoped InnerProductSpace ComplexOrder
namespace NuclearUltrapower.SOS.ElementarySpectral

section Hilbert
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def deltaOp (ρ : E →* (H ≃ₗᵢ[ℂ] H)) : H →L[ℂ] H :=
  eval (value (A := H →L[ℂ] H) (unitaryRep ρ)) delta

def residualInE : List (E × ℤ) := residual.map (fun p => (eInterpret p.1, p.2))

def gramOp (ρ : E →* (H ≃ₗᵢ[ℂ] H)) : H →L[ℂ] H :=
  (10 : ℤ) • gramValue (value (A := H →L[ℂ] H) (unitaryRep ρ))

end Hilbert
end NuclearUltrapower.SOS.ElementarySpectral
end
end

end OAI
end

section
-- module Solutions.OAIQ019_Nuc.NuclearUltrapower_Kazhdan
attribute [-instance] _root_.OAI.NuclearUltrapower.CuntzModel.instNontrivialSubtypePreLpIndexComplexMemAddSubgroupSpace _root_.OAI.NuclearUltrapower.CuntzPolynomial.instSeminormedRingPoly _root_.OAI.NuclearUltrapower.CuntzWords.instDecidableEqWord _root_.OAI.NuclearUltrapower.CuntzWords.instFintypeWord _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instInvolutiveStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instSeminormedRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarAddMonoidMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.UniversalCompletion.completionInvolutiveStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionNormedAlgebra _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStarRing _root_.OAI.NuclearUltrapower.VariableUltra.instCompleteSpaceAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instNontrivialAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instNormedAddCommGroupAlgebra _root_.OAI.NuclearUltrapower.induced_nontrivial _root_.OAI.NuclearUltrapower.instCountableDyadic _root_.OAI.NuclearUltrapower.instCountableG _root_.OAI.NuclearUltrapower.instCountableSL3Z _root_.OAI.NuclearUltrapower.instCountableVector3 _root_.OAI.NuclearUltrapower.lp_finiteDimensional _root_.OAI.NuclearUltrapower.tensorHilbertNontrivial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped InnerProductSpace
namespace NuclearUltrapower.SOS.ElementarySpectral
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def vectorStabilizer (ρ : E →* (H ≃ₗᵢ[ℂ] H)) (x : H) : Subgroup E where
  carrier := {g | ρ g x = x}
  one_mem' := by simp
  mul_mem' ha hb := by
    change ρ _ x = x at ha hb ⊢
    simpa only [map_mul, LinearIsometryEquiv.coe_mul, Function.comp_apply, hb] using ha
  inv_mem' {g} hg := by
    change ρ g⁻¹ x = x
    apply (ρ g).injective
    change (ρ g * ρ g⁻¹) x = ρ g x
    rw [← map_mul, mul_inv_cancel, map_one]
    exact hg.symm

end NuclearUltrapower.SOS.ElementarySpectral
end
end

section

noncomputable section
open scoped InnerProductSpace
namespace NuclearUltrapower.Elementary

/-- The inclusion is literally integer coordinate inclusion into Z[1/2]. -/
def integralInclusion : IntegralGroup →* G where
  toFun g := ⟨Multiplicative.ofAdd (fun i => (g.left.toAdd i : Dyadic)), (g.right, 1)⟩
  map_one' := by ext <;> simp
  map_mul' g h := by
    apply SemidirectProduct.ext
    · apply Multiplicative.toAdd.injective
      funext i
      change ((g.left.toAdd i + (Matrix.SpecialLinearGroup.toLin' g.right) h.left.toAdd i : ℤ) : Dyadic) =
        (g.left.toAdd i : Dyadic) + (dilationAction (g.right, 1)) (fun j => (h.left.toAdd j : Dyadic)) i
      simp [dilationAction, matrixAction, Matrix.SpecialLinearGroup.toLin'_apply,
        Matrix.mulVec, dotProduct, LinearEquiv.smulOfUnit]
    · rfl

theorem mem_theta_range_iff (g : IntegralGroup) :
    g ∈ integralTheta.range ↔ residue g = 0 := by
  constructor
  · rintro ⟨h, rfl⟩
    exact residue_theta h
  · intro hg
    have hd (i : Fin 3) : (2 : ℤ) ∣ g.left.toAdd i := by
      have hi := congrFun hg i
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hi
    refine ⟨⟨Multiplicative.ofAdd (fun i => g.left.toAdd i / 2), g.right⟩, ?_⟩
    apply SemidirectProduct.ext
    · apply Multiplicative.toAdd.injective
      funext i
      change 2 * (g.left.toAdd i / 2) = g.left.toAdd i
      exact Int.mul_ediv_cancel' (hd i)
    · rfl

theorem leftRel_theta_iff (g h : IntegralGroup) :
    QuotientGroup.leftRel integralTheta.range g h ↔ residue g = residue h := by
  rw [QuotientGroup.leftRel_apply, mem_theta_range_iff]
  have he : residue (g⁻¹) + residueMatrix (g⁻¹).right (residue g) = 0 := by
    rw [← residue_mul, inv_mul_cancel, residue_one]
  rw [residue_mul]
  constructor
  · intro hz
    have hi := add_left_cancel (hz.trans he.symm)
    exact (residueMatrix (g⁻¹).right).injective hi |>.symm
  · intro hgh
    rwa [← hgh]

/-- The eight left cosets are precisely the three translation residues. -/
def thetaCosetEquiv : (IntegralGroup ⧸ integralTheta.range) ≃ Residue3 where
  toFun := Quotient.lift residue (fun g h hgh => (leftRel_theta_iff g h).mp hgh)
  invFun a := Quotient.mk'' (integralTranslation (fun i => (a i).val))
  left_inv q := by
    induction q using Quotient.inductionOn with | h g =>
      apply Quotient.sound
      apply (leftRel_theta_iff _ _).mpr
      ext i
      simp [residue, integralTranslation]
  right_inv a := by
    ext i
    simp [residue, integralTranslation]

def augmentation : Submodule ℂ ResidueHilbert := LinearMap.ker ({
  toFun f := ∑ x, f x
  map_add' f h := Finset.sum_add_distrib
  map_smul' c f := by simp [Finset.mul_sum] } : ResidueHilbert →ₗ[ℂ] ℂ)

@[simp] theorem mem_augmentation (f : ResidueHilbert) :
    f ∈ augmentation ↔ ∑ x, f x = 0 := Iff.rfl

theorem augmentation_invariant (g : IntegralGroup) (f : ResidueHilbert)
    (hf : f ∈ augmentation) : residueUnitary g f ∈ augmentation := by
  rw [mem_augmentation] at *
  simpa only [residueUnitary_apply, Equiv.sum_comp] using hf

def augmentationVector : ResidueHilbert :=
  PiLp.single 2 (0 : Residue3) 1 - PiLp.single 2 (1 : Residue3) 1

theorem augmentationVector_mem : augmentationVector ∈ augmentation := by
  simp [augmentationVector, PiLp.sub_apply, PiLp.single_apply, Finset.sum_sub_distrib]

theorem augmentationVector_ne_zero : augmentationVector ≠ 0 := by
  intro h
  have he := congrArg (fun f : ResidueHilbert => f 0) h
  have hz : (0 : Residue3) ≠ 1 := by
    intro hz
    have h0 := congrFun hz 0
    exact zero_ne_one h0
  simp [augmentationVector, hz] at he

instance augmentation_nontrivial : Nontrivial augmentation := by
  apply Submodule.nontrivial_iff_ne_bot.mpr
  intro h
  have hmem := augmentationVector_mem
  rw [h] at hmem
  exact augmentationVector_ne_zero hmem

def augmentationRep : FiniteUnitaryRep IntegralGroup :=
  (FiniteUnitaryRep.mk ResidueHilbert residueUnitary).restrict augmentation augmentation_invariant

end NuclearUltrapower.Elementary
end
end

section

noncomputable section
namespace NuclearUltrapower.Elementary
open SOS

theorem transvection_one_mem : ∀ (i j : Fin 3) (h : i ≠ j),
    Matrix.SpecialLinearGroup.transvection h (1 : ℤ) ∈ SOS.genSet := by
  decide +kernel

def transvectionHom {i j : Fin 3} (h : i ≠ j) : Multiplicative ℤ →* SL3Z where
  toFun z := Matrix.SpecialLinearGroup.transvection h z.toAdd
  map_one' := by simp
  map_mul' a b := Matrix.SpecialLinearGroup.transvection_add h a.toAdd b.toAdd

theorem transvection_mem {i j : Fin 3} (h : i ≠ j) (k : ℤ) :
    Matrix.SpecialLinearGroup.transvection h k ∈ SOS.elementary := by
  have he : Matrix.SpecialLinearGroup.transvection h k =
      (Matrix.SpecialLinearGroup.transvection h (1:ℤ)) ^ k := by
    have hz := (transvectionHom h).map_zpow (Multiplicative.ofAdd (1:ℤ)) k
    simpa only [transvectionHom, MonoidHom.coe_mk, OneHom.coe_mk,
      toAdd_zpow, toAdd_ofAdd, zsmul_eq_mul,
      mul_one, Int.cast_id] using hz
  rw [he]
  exact SOS.elementary.zpow_mem (Subgroup.subset_closure (transvection_one_mem i j h)) k

def elementaryTransvection {i j : Fin 3} (h : i ≠ j) (k : ℤ) : SOS.E :=
  ⟨Matrix.SpecialLinearGroup.transvection h k, transvection_mem h k⟩

def linearInclusion : SOS.E →* IntegralGroup := SemidirectProduct.inr

end NuclearUltrapower.Elementary
end
end

section

noncomputable section
namespace NuclearUltrapower.Displacement
variable {Γ H : Type*} [Group Γ] [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] (ρ : Γ →* (H ≃ₗᵢ[ℂ] H))

@[simp] theorem inv (g : Γ) (x : H) : dist ρ g⁻¹ x = dist ρ g x := by
  unfold dist
  rw [← (ρ g).norm_map (ρ g⁻¹ x-x), map_sub]
  have he : ρ g (ρ g⁻¹ x) = x := by
    change (ρ g * ρ g⁻¹) x = x
    rw [← map_mul, mul_inv_cancel, map_one]
    rfl
  rw [he, norm_sub_rev]

end NuclearUltrapower.Displacement
end
end

section

noncomputable section
open scoped InnerProductSpace
namespace NuclearUltrapower.Elementary
open SOS SOSEnergy
open Displacement (dist)

/-- An explicit finite set in the honest integral elementary subgroup. -/
def kazhdanSet : Finset IntegralGroup :=
  eGenSet.image linearInclusion ∪ Finset.univ.image (fun i => integralTranslation (basisVector i))

end NuclearUltrapower.Elementary
end
end

end OAI
end


