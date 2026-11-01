-- Prove2me | Definitions.Def_OAIQ050L006
-- name    : OAIQ050L006
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T09:07:46.214754+00:00
-- url     : https://prove2.me/theorems/545f9424-2ff9-4507-9499-252559c89e0b
-- title:
--   Definitions bundle OAIQ050L006 of the split of OpenAI, A Fock-space inequality and the Laughlin spectral gap
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Laughlin.planar_gap`, carved from OpenAI's openai/math development (OpenAI, *A Fock-space inequality and the Laughlin spectral gap*, OpenAI Math Release, September 24, 2026, result family 269, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 48 declarations of OpenAI's Lean: 44 definitions and 4 theorems. The definitions and types are `OAI.Laughlin.Fock.boundedAnnihilate`, `OAI.Laughlin.Fock.complexOuter`, `OAI.Laughlin.Fock.contractionForm`, `OAI.Laughlin.Fock.copyQuadraticMatrix`, `OAI.Laughlin.Fock.create`, `OAI.Laughlin.Fock.delta`, `OAI.Laughlin.Fock.diagonalUnit`, `OAI.Laughlin.Fock.entrySum`, `OAI.Laughlin.Fock.firstOddPairLabel`, `OAI.Laughlin.Fock.fourDimensionRatio`, `OAI.Laughlin.Fock.localDiagonals`, `OAI.Laughlin.Fock.localMetricError`, `OAI.Laughlin.Fock.matrixMetricError`, `OAI.Laughlin.Fock.mode`, `OAI.Laughlin.Fock.occupationInner`, `OAI.Laughlin.Rotation.SourceSU2`, `OAI.Laughlin.Rotation.subsetTensorBits`, `OAI.Laughlin.Rotation.symmetricTensorInclusion`, `OAI.Laughlin.Rotation.symmetricTensorInclusionReal`, `OAI.Laughlin.Rotation.tensorBits`, `OAI.Laughlin.Rotation.tensorMatrix`, `OAI.Laughlin.Rotation.tensorSubsetEquiv`, `OAI.Laughlin.Rotation.tensorWeight`, `OAI.Laughlin.Spin.CoupledIndex`, `OAI.Laughlin.Spin.LocalFourIndex`, `OAI.Laughlin.Spin.OddPairLabel`, `OAI.Laughlin.Spin.coupledSelector`, `OAI.Laughlin.Spin.coupledWeight`, `OAI.Laughlin.Spin.couplingPolynomial`, `OAI.Laughlin.Spin.couplingPolynomialCoefficient`, `OAI.Laughlin.Spin.fourBodyLimitCoefficient`, `OAI.Laughlin.Spin.fourErrorLimitEntry`, `OAI.Laughlin.Spin.fourErrorLimitRow`, `OAI.Laughlin.Spin.highestNorm`, `OAI.Laughlin.Spin.highestRaw`, `OAI.Laughlin.Spin.highestUnit`, `OAI.Laughlin.Spin.monomialNormFactor`, `OAI.Laughlin.Spin.pairInclusion`, `OAI.Laughlin.Spin.sourceAlpha`, `OAI.Laughlin.Spin.sqrtFactorial` and 4 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `Laughlin_Asymptotics_LocalDiagonalLimit`, `Laughlin_Asymptotics_LocalMetricLimit`, `Laughlin_Fock_Adjoint`, `Laughlin_Fock_Creation`, `Laughlin_Fock_HaarQuadratic`, `Laughlin_Fock_RankOneHaar`, `Laughlin_FourBody_CoefficientLimit`, `Laughlin_FourBody_CopyAlgebra`, `Laughlin_FourBody_ErrorLimit`, `Laughlin_FourBody_MiddleLimit`, `Laughlin_FourBody_TransferConjugation`, `Laughlin_FourBody_Ungroup`, `Laughlin_Model`, `Laughlin_Operators_CAR`, `Laughlin_Operators_CopyQuadraticMatrix`, `Laughlin_Operators_MatrixMetricError`, `Laughlin_Operators_NormalOrder`, `Laughlin_Pair_Conjugation`, `Laughlin_Pair_CoupledBasis`, `Laughlin_Pair_LadderIntertwining`, `Laughlin_Polynomial_OscillatorPolynomial`, `Laughlin_Polynomial_SymmetricTensorCoordinates`, `Laughlin_Polynomial_SymmetricTensorRange`, `Laughlin_Spin_Basis`, `Laughlin_Spin_DescendantNorm`, `Laughlin_Spin_Highest2`, `Laughlin_Spin_HighestSpace`, `Laughlin_Spin_Sl2DescendantNorm`, `Laughlin_Spin_TensorAction`, `Laughlin_ThreeBody_SpinProjectors`.
--
--   **Imports.** It imports the published bundle `Def_LaughlinPlanar`.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ050L010`, `OAIQ050L011`, `OAIQ050L012`, `OAIQ050L013`, `OAIQ050L014` and `OAIQ050L015`; the statements `OAI_Laughlin_Fock_annihilate_create_inner`, `OAI.Laughlin.Fock.annihilate_create_inner_s50`, `OAI_Laughlin_Fock_create_create_inner`, `OAI.Laughlin.Fock.create_create_inner_s50`, `OAI_Laughlin_Fock_limitPairEnd_four_create`, `OAI.Laughlin.Fock.limitPairEnd_four_create_s50`, `OAI_Laughlin_Fock_occupationInner_scalar_wedge_zero`, `OAI.Laughlin.Fock.occupationInner_scalar_wedge_zero_s50`, `OAI_Laughlin_Fock_pairEnd_create_create`, `OAI.Laughlin.Fock.pairEnd_create_create_s50`, `OAI_Laughlin_Fock_pairEnd_three_create`, `OAI.Laughlin.Fock.pairEnd_three_create_s50`, `OAI_Laughlin_Fock_row_normal_square`, `OAI.Laughlin.Fock.row_normal_square_s50`, `OAI_Laughlin_Fock_vectorCreate_adjoint`, `OAI.Laughlin.Fock.vectorCreate_adjoint_s50`, `OAI_Laughlin_Fock_weightedFourEnd_readout`, `OAI.Laughlin.Fock.weightedFourEnd_readout_s50`, `OAI_Laughlin_Spin_oscillatorArray_polynomial`, `OAI.Laughlin.Spin.oscillatorArray_polynomial_s50`, `OAI_Laughlin_Spin_source_fourBody_factorial_coefficient`, `OAI.Laughlin.Spin.source_fourBody_factorial_coefficient_s50`, `OAI_Laughlin_Spin_source_highest_coupling_tendsto`, `OAI.Laughlin.Spin.source_highest_coupling_tendsto_s50`, `OAI_Laughlin_pairCoefficient_unit_norm` and `OAI.Laughlin.pairCoefficient_unit_norm_s50`; the proofs of `OAI_Laughlin_Fock_finiteFourMiddle_tendsto`, `OAI_Laughlin_Fock_fockInclusion_normSq`, `OAI.Laughlin.Fock.fockInclusion_normSq_s50`, `OAI_Laughlin_Fock_limitPairEnd_four_create`, `OAI.Laughlin.Fock.limitPairEnd_four_create_s50`, `OAI_Laughlin_Fock_occupationInner_scalar_wedge_zero`, `OAI.Laughlin.Fock.occupationInner_scalar_wedge_zero_s50`, `OAI_Laughlin_Fock_pairEnd_create_create`, `OAI.Laughlin.Fock.pairEnd_create_create_s50`, `OAI_Laughlin_Fock_pairEnd_three_create`, `OAI.Laughlin.Fock.pairEnd_three_create_s50`, `OAI_Laughlin_Fock_physicalLimitError_eq`, `OAI_Laughlin_Spin_oscillatorArray_polynomial`, `OAI.Laughlin.Spin.oscillatorArray_polynomial_s50`, `OAI_Laughlin_Spin_source_fourBody_factorial_coefficient`, `OAI.Laughlin.Spin.source_fourBody_factorial_coefficient_s50`, `OAI_Laughlin_pairCoefficient_unit_norm` and `OAI.Laughlin.pairCoefficient_unit_norm_s50`.
-- source:
--   OpenAI, A Fock-space inequality and the Laughlin spectral gap, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 269; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit adc7f12

import Mathlib
import Definitions.Def_LaughlinPlanar

section
-- module Solutions.OAIQ050_Laughlin.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Operators_CAR
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock

noncomputable def mode {Q : ℕ} (i : Fin (Q+1)) : Orbital Q := Pi.single i 1

noncomputable def create {Q : ℕ} (i : Fin (Q+1)) : Module.End ℂ (Space Q) where
  toFun x := ExteriorAlgebra.ι ℂ (mode i) * x
  map_add' x y := mul_add _ x y
  map_smul' c x := by simp

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Model
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin
open scoped BigOperators

noncomputable def pairCoefficient (Q p : ℕ) (x y : Fin (Q+1)) : ℝ :=
  if x.val + y.val = p+1 then
    ((x.val : ℝ) - (y.val : ℝ)) *
      Real.sqrt (((Q.descFactorial x.val : ℝ) * (Q.descFactorial y.val : ℝ) *
        (p.factorial : ℝ)) /
        ((Q : ℝ) * ((2*Q-2).descFactorial p : ℝ) *
          (x.val.factorial : ℝ) * (y.val.factorial : ℝ))) / Real.sqrt 2
  else 0

end Laughlin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Pair_Conjugation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin

noncomputable def modeFactor (Q x : ℕ) : ℝ :=
  Real.sqrt ((Q.descFactorial x : ℝ) / (Q : ℝ)^x)

noncomputable def pairFactor (Q p : ℕ) : ℝ :=
  Real.sqrt (((2 : ℝ)*Q)^p / ((2*Q-2).descFactorial p : ℝ))

end Laughlin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Asymptotics_LocalDiagonalLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators Topology
open Filter

noncomputable def localDiagonals (L Q : ℕ) (A : Finset (Fin (L+1))) : ℝ :=
  ∏ i ∈ A, modeFactor Q i.val

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Asymptotics_LocalMetricLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators Topology
open Filter

noncomputable def localMetricError (L Q : ℕ) : ℝ :=
  ‖fun A : Finset (Fin (L+1)) => ((localDiagonals L Q A)⁻¹)^2 - 1‖

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Fock_Creation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators

theorem occupation_singleton (Q : ℕ) (i : Fin (Q+1)) :
    occupationBasis Q {i} = ExteriorAlgebra.ι ℂ (mode i) := by
  let A : Set.powersetCard (Fin (Q+1)) 1 := ⟨{i},Finset.card_singleton i⟩
  have hi : Set.powersetCard.ofFinEmbEquiv.symm A 0 = i := by
    have hm := (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem A
      (Set.powersetCard.ofFinEmbEquiv.symm A 0)).mp ⟨0,rfl⟩
    exact Finset.mem_singleton.mp hm
  change (Pi.basisFun ℂ (Fin (Q+1))).ExteriorAlgebra A.val = _
  rw [ExteriorAlgebra.basis_apply_powersetCard]
  simp only [ExteriorAlgebra.ιMulti_family, ExteriorAlgebra.ιMulti_succ_apply,
    ExteriorAlgebra.ιMulti_zero_apply, mul_one, Function.comp_apply, hi]
  simp [Pi.basisFun_apply, mode]

theorem create_unoccupied_sign (Q : ℕ) (i : Fin (Q+1))
    (A : Finset (Fin (Q+1))) (hi : i ∉ A) :
    ∃ ε : ℂ, (ε = 1 ∨ ε = -1) ∧
      create i (occupationBasis Q A) = ε • occupationBasis Q (insert i A) := by
  let S : Set.powersetCard (Fin (Q+1)) 1 := ⟨{i},Finset.card_singleton i⟩
  let T : Set.powersetCard (Fin (Q+1)) A.card := ⟨A,rfl⟩
  have hd : Disjoint S.val T.val := by simpa [S,T] using hi
  have h := ExteriorAlgebra.basis_mul_of_disjoint (Pi.basisFun ℂ (Fin (Q+1))) S T hd
  rcases Int.units_eq_one_or (Set.powersetCard.permOfDisjoint hd).sign with hs | hs
  · refine ⟨1,Or.inl rfl,?_⟩
    simpa [hs,S,T,occupationBasis,Set.powersetCard.disjUnion,
      ← occupation_singleton Q i, create] using h
  · refine ⟨-1,Or.inr rfl,?_⟩
    simpa [hs,S,T,occupationBasis,Set.powersetCard.disjUnion,
      ← occupation_singleton Q i, create] using h

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Fock_Adjoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators

noncomputable def occupationInner (Q : ℕ) (x y : Space Q) : ℂ :=
  ∑ A : Finset (Fin (Q+1)), star ((occupationBasis Q).repr x A) * (occupationBasis Q).repr y A

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Spin_TensorAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Rotation
open scoped BigOperators Matrix

noncomputable def tensorMatrix (N : ℕ) (A : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (Fin N → Fin 2) (Fin N → Fin 2) ℂ := fun a b => ∏ i, A (a i) (b i)

theorem tensorMatrix_mul (N : ℕ) (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    tensorMatrix N (A*B) = tensorMatrix N A * tensorMatrix N B := by
  ext a c
  simp only [tensorMatrix,Matrix.mul_apply,← Finset.prod_mul_distrib]
  exact Fintype.prod_sum (fun i b => A (a i) b*B b (c i))

abbrev SourceSU2 := Matrix.specialUnitaryGroup (Fin 2) ℂ

end Laughlin.Rotation

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Polynomial_SymmetricTensorCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Rotation
open scoped BigOperators Matrix

noncomputable def tensorBits (Q : ℕ) (a : Fin Q → Fin 2) : Finset (Fin Q) :=
  Finset.univ.filter (fun i => a i=1)
noncomputable def subsetTensorBits (Q : ℕ) (s : Finset (Fin Q)) : Fin Q → Fin 2 :=
  fun i => if i ∈ s then 1 else 0

noncomputable def tensorSubsetEquiv (Q : ℕ) : (Fin Q → Fin 2) ≃ Finset (Fin Q) where
  toFun := tensorBits Q
  invFun := subsetTensorBits Q
  left_inv a := by
    funext i
    simp only [subsetTensorBits,tensorBits,Finset.mem_filter,Finset.mem_univ,true_and]
    have hi : a i=0 ∨ a i=1 := by omega
    rcases hi with hi | hi <;> simp [hi]
  right_inv s := by
    ext i
    simp [tensorBits,subsetTensorBits]

noncomputable def tensorWeight (Q : ℕ) (a : Fin Q → Fin 2) : ℕ := (tensorBits Q a).card

noncomputable def symmetricTensorInclusionReal (Q : ℕ) :
    Matrix (Fin Q → Fin 2) (Fin (Q+1)) ℝ :=
  fun a p => if tensorWeight Q a=p.val then (Real.sqrt (Q.choose p.val : ℝ))⁻¹ else 0

end Laughlin.Rotation

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Polynomial_SymmetricTensorRange
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Rotation
open scoped BigOperators Matrix

noncomputable def symmetricTensorInclusion (Q : ℕ) : Matrix (Fin Q → Fin 2) (Fin (Q+1)) ℂ :=
  (symmetricTensorInclusionReal Q).map Complex.ofReal

end Laughlin.Rotation

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Fock_HaarQuadratic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open Rotation MeasureTheory
open scoped BigOperators Matrix

noncomputable def contractionForm {I : Type*} [Fintype I] (Q : ℕ)
    (minus : I → Module.End ℂ (Space Q)) (M : Matrix I I ℂ) (x : Space Q) : ℂ :=
  ∑ i, ∑ j, M i j * occupationInner Q (minus i x) (minus j x)

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Operators_NormalOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock

noncomputable def delta {Q : ℕ} (i j : Fin (Q+1)) : ℂ := if i = j then 1 else 0

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Spin_Highest2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators

noncomputable def highestRaw (A B z p : ℕ) : ℝ :=
  if p ≤ z then (-1 : ℝ)^p * (z.choose p : ℝ) /
    Real.sqrt ((A.choose p : ℝ)*(B.choose (z-p) : ℝ)) else 0

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Pair_LadderIntertwining
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix

noncomputable def pairInclusion (Q : ℕ) :
    Matrix (Fin (Q+1) × Fin (Q+1)) (Fin ((2*Q-2)+1)) ℝ :=
  fun i p => pairCoefficient Q p.val i.1 i.2

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Spin_HighestSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators

noncomputable def highestNorm (A B z : ℕ) : ℝ :=
  Real.sqrt (∑ p ∈ Finset.range (z+1), (highestRaw A B z p)^2)

noncomputable def highestUnit (A B z p : ℕ) : ℝ :=
  highestRaw A B z p / highestNorm A B z

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Fock_RankOneHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open Rotation MeasureTheory
open scoped BigOperators Matrix

noncomputable def complexOuter {I : Type*} (v w : I → ℂ) : Matrix I I ℂ :=
  fun i j => v i * star (w j)

noncomputable def diagonalUnit {J : Type*} [DecidableEq J] (p : J) : Matrix J J ℂ :=
  fun i j => if i=p ∧ j=p then 1 else 0

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Spin_Sl2DescendantNorm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix

variable {I : Type*} [Fintype I] [DecidableEq I]

noncomputable def vectorNormSq (v : I → ℝ) : ℝ := ∑ i, (v i)^2

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Polynomial_OscillatorPolynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators
open Polynomial

noncomputable def sqrtFactorial (n : ℕ) : ℝ := Real.sqrt (n.factorial : ℝ)
noncomputable def monomialNormFactor (T p : ℕ) : ℝ := sqrtFactorial p * sqrtFactorial (T-p)

noncomputable def couplingPolynomial (u v : ℝ) (z n : ℕ) : Polynomial ℝ :=
  (C u * X-C v)^z * (C v * X+C u)^n

noncomputable def couplingPolynomialCoefficient (u v : ℝ) (z n p : ℕ) : ℝ :=
  (couplingPolynomial u v z n).coeff p * monomialNormFactor (z+n) p /
    (sqrtFactorial z * sqrtFactorial n)

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Spin_DescendantNorm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix

def coupledWeight (Q z : ℕ) : ℕ := 3*Q-2-2*z

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FourBody_CoefficientLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped Topology
open Filter

noncomputable def fourBodyLimitCoefficient (r D T p j k : ℕ) : ℝ :=
  if r ≤ j+k then Real.sqrt 2 *
    couplingPolynomialCoefficient (Real.sqrt (1/2)) (Real.sqrt (1/2)) r (j+k-r) j *
    couplingPolynomialCoefficient (Real.sqrt (1/2)) (Real.sqrt (1/2)) (D-r) (T-D) p else 0

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FourBody_TransferConjugation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Topology
open Filter

abbrev LocalFourIndex (D : ℕ) :=
  {b : Fin (D+1) × Fin (D+1) × Fin (D+1) // b.1.val+b.2.1.val+b.2.2.val=D ∧ b.2.1 < b.2.2}

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FourBody_ErrorLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped Topology
open Filter

noncomputable def sourceAlpha (t : ℕ) (e : ℕ × ℕ × ℤ) : ℝ :=
  (e.2.2 : ℝ)/(10^7) * Real.sqrt ((2 : ℝ)^((e.1 : ℤ)-t) *
    ((t.factorial : ℝ)*((e.1+e.2.1-t).factorial : ℝ) /
      ((e.1.factorial : ℝ)*(e.2.1.factorial : ℝ))))

noncomputable def fourErrorLimitEntry (D r s t : ℕ) (e f : ℕ × ℕ × ℤ) : ℝ :=
  let i := e.1+e.2.1-t
  let k := f.1+f.2.1-t
  let T := e.1+e.2.1+k
  if D ≤ T then sourceAlpha t e * sourceAlpha t f *
    fourBodyLimitCoefficient r D T e.1 e.2.1 k * fourBodyLimitCoefficient s D T f.1 f.2.1 i else 0

noncomputable def fourErrorLimitRow (D r s : ℕ) (row : ℕ × ℤ × List (ℕ × ℕ × ℤ)) : ℝ :=
  (row.2.2.map (fun e => (row.2.2.map (fun f => fourErrorLimitEntry D r s row.1 e f)).sum)).sum

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FourBody_MiddleLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators Matrix Topology
open Filter Spin

noncomputable def fourDimensionRatio (Q D : ℕ) : ℝ :=
  (4*(Q : ℝ)-1-2*(D : ℝ))/(2*(Q : ℝ)-1)

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Operators_CopyQuadraticMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators Matrix
open Matrix

noncomputable def copyQuadraticMatrix {I J : Type*} [Fintype I]
    (C : I → I → ℝ) (β : I → J → ℝ) : J → J → ℝ :=
  fun a b => ∑ i, ∑ j, C i j * β i a * β j b

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Operators_MatrixMetricError
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators Topology
open Filter

noncomputable def entrySum {I : Type*} [Fintype I] (R : I → I → ℝ) : ℝ := ∑ i, ∑ j, |R i j|

noncomputable def matrixMetricError {I : Type*} [Fintype I] (L Q : ℕ) (R S : I → I → ℝ) : ℝ :=
  entrySum (fun i j => R i j-S i j) + localMetricError L Q * entrySum R

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Spin_Basis
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix

abbrev CoupledIndex (Q : ℕ) := Σ z : Fin (Q+1), Fin (coupledWeight Q z.val+1)

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Pair_CoupledBasis
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix

abbrev OddPairLabel (Q : ℕ) := Fin ((Q+1)/2)

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FourBody_CopyAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open Spin
open scoped BigOperators Matrix

def firstOddPairLabel (D : ℕ) (hD : 1 ≤ D) : OddPairLabel D := ⟨0,by omega⟩

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_ThreeBody_SpinProjectors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix

noncomputable def coupledSelector (Q : ℕ) (z : Fin (Q+1)) :
    Matrix (CoupledIndex Q) (CoupledIndex Q) ℝ :=
  Matrix.diagonal (fun s => if s.1=z then 1 else 0)

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FourBody_Ungroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open Spin
open scoped BigOperators Matrix

noncomputable def boundedAnnihilate (Q n : ℕ) : Module.End ℂ (Space Q) :=
  if h : n ≤ Q then annihilate ⟨n,by omega⟩ else 0

end Laughlin.Fock

end OAI
end


