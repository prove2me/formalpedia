-- Prove2me | Definitions.Def_OAIQ039C034
-- name    : OAIQ039C034
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T06:19:59.14902+00:00
-- url     : https://prove2.me/theorems/90ab868a-ab9a-4b49-924c-9a48c87ebab4
-- title:
--   Definitions bundle OAIQ039C034 of the split of OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 21 declarations of OpenAI's Lean: 5 definitions and 16 theorems. The definitions and types are `OAI.Kadison.FiniteCompression.averageIsometry`, `OAI.Kadison.FiniteTest.character`, `OAI.Kadison.Kaplansky.offDiagonal`, `OAI.Kadison.OperatorAmplification.diagonalVonNeumann`, `OAI.Kadison.OperatorAmplification.fullMatrixAlgebra`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis/Commutator, in whole or in part: `Commutator_DecomposableOperator`, `Commutator_DiagonalVonNeumann`, `Commutator_FiniteHankel`, `Commutator_FiniteTestPatching`, `Commutator_KaplanskyFull`, `Commutator_MatrixAlgebraDensity`, `Commutator_OperatorAmplification`.
--
--   **Imports.** It imports the bundles `OAIQ039C021`, `OAIQ039C022`, `OAIQ039C023` and `OAIQ039C024` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ039C043`, `OAIQ039C044`, `OAIQ039C045`, `OAIQ039C046`, `OAIQ039C047`, `OAIQ039C050` and `OAIQ039C051`; the proofs of `OAI.Kadison.CyclicSpatial.exists_cyclic_intertwiner` and `OAI.Kadison.LocalQuantization.exists_small_projection`.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis/Commutator at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ039C021
import Definitions.Def_OAIQ039C022
import Definitions.Def_OAIQ039C023
import Definitions.Def_OAIQ039C024

section
-- module Solutions.OAIQ039_CM.Commutator_DecomposableOperator
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open MeasureTheory Filter

open scoped Topology ComplexOrder InnerProductSpace

namespace Kadison.Decomposable

variable {Ω H : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

lemma operator_norm_le (T : Ω → H →L[ℂ] H)
    (hm : ∀ ξ : H,AEStronglyMeasurable (fun a => T a ξ) μ)
    {b d : ℝ} (hb : ∀ᵐ a ∂μ,‖T a‖≤b) (hd0 : 0≤d) (hd : ∀ᵐ a ∂μ,‖T a‖≤d) :
    ‖operator μ T hm hb‖≤d :=
  ContinuousLinearMap.opNorm_le_bound _ hd0 (act_norm_le μ T hm hb hd)

end Kadison.Decomposable

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_OperatorAmplification
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators InnerProductSpace

namespace Kadison.OperatorAmplification

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (ι : Type*) [Fintype ι] [DecidableEq ι]

omit [CompleteSpace H] in
lemma reconstruct (T : SumSpace (H:=H) ι →L[ℂ] SumSpace (H:=H) ι) :
    CyclicColumns.matrixAction (entry ι T)=T := by
  ext x i
  simpa only [CyclicColumns.matrixAction_apply] using (apply_eq_sum_entries ι T x i).symm

end Kadison.OperatorAmplification

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_DiagonalVonNeumann
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators InnerProductSpace

namespace Kadison.OperatorAmplification

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (ι : Type*) [Fintype ι] [DecidableEq ι]

lemma matrixUnit_commutes (i j : ι) (T : H →L[ℂ] H) :
    matrixUnit ι (H:=H) i j*diagonal (H:=H) ι T=
      diagonal (H:=H) ι T*matrixUnit ι i j := by
  ext x k
  simp [mul_apply_eq_comp,diagonal_single]

lemma diagonal_of_matrixUnits (i₀ : ι) (T : SumSpace (H:=H) ι →L[ℂ] SumSpace (H:=H) ι)
    (hT : ∀ i j, matrixUnit ι i j*T=T*matrixUnit ι i j) :
    T=diagonal (H:=H) ι (entry ι T i₀ i₀) := by
  have hs : ∀ j x, T (single ι j x)=single ι j (entry ι T i₀ i₀ x) := by
    intro j x
    have he := congrArg (fun R : SumSpace (H:=H) ι →L[ℂ] SumSpace (H:=H) ι => R (single ι i₀ x)) (hT j i₀)
    simpa [mul_apply_eq_comp,entry_apply] using he.symm
  ext x j
  conv_lhs => rw [←sum_single ι x]
  simp only [map_sum,hs]
  simp

def diagonalVonNeumann (i₀ : ι) (M : VonNeumannAlgebra H) : VonNeumannAlgebra (SumSpace (H:=H) ι) where
  toStarSubalgebra := M.toStarSubalgebra.map (diagonal (H:=H) ι)
  centralizer_centralizer' := by
    ext T
    constructor
    · intro hT
      have hU : ∀ i j, matrixUnit ι i j*T=T*matrixUnit ι i j := by
        intro i j
        apply hT
        rintro R ⟨a,ha,rfl⟩
        exact (matrixUnit_commutes ι i j a).symm
      let a := entry ι T i₀ i₀
      have he : T=diagonal (H:=H) ι a := diagonal_of_matrixUnits ι i₀ T hU
      have ha : a∈M := by
        rw [←SetLike.mem_coe,←M.centralizer_centralizer]
        intro b hb
        apply entry_commutes ι T b
        apply hT
        rintro R ⟨d,hd,rfl⟩
        have hh : d*b=b*d := hb d hd
        change diagonal (H:=H) ι d * diagonal (H:=H) ι b =
          diagonal (H:=H) ι b * diagonal (H:=H) ι d
        exact (map_mul (diagonal (H:=H) ι) d b).symm.trans
          ((congrArg (diagonal (H:=H) ι) hh).trans (map_mul (diagonal (H:=H) ι) b d))
      exact ⟨a,ha,he.symm⟩
    · rintro ⟨a,ha,rfl⟩
      apply diagonal_bicommutant ι M.toStarSubalgebra
      change a ∈ Set.centralizer (Set.centralizer (M : Set (H →L[ℂ] H)))
      rw [M.centralizer_centralizer]
      exact ha

@[simp] lemma mem_diagonalVonNeumann (i₀ : ι) (M : VonNeumannAlgebra H)
    (T : SumSpace (H:=H) ι →L[ℂ] SumSpace (H:=H) ι) :
    T∈diagonalVonNeumann ι i₀ M ↔ ∃ a∈M,diagonal (H:=H) ι a=T := Iff.rfl

end Kadison.OperatorAmplification

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FiniteHankel
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace

open ContinuousLinearMap

namespace Kadison.FiniteCompression

open scoped BigOperators InnerProductSpace

open ContinuousLinearMap

variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

variable {I : Type*} [Fintype I] [DecidableEq I]

omit [CompleteSpace H] [CompleteSpace K] [DecidableEq I] in
lemma average_inner (c : ℝ) (U : I → K →ₗᵢ[ℂ] H)
    (horth : ∀ i j, i ≠ j → ∀ x y : K, inner ℂ (U i x) (U j y) = 0)
    (hscale : c^2 * Fintype.card I = 1) (x y : K) :
    inner ℂ (average c (fun i => (U i).toContinuousLinearMap) x)
      (average c (fun i => (U i).toContinuousLinearMap) y) = inner ℂ x y := by
  simp only [average_apply, inner_smul_left, inner_smul_right,
    Complex.conj_ofReal, LinearIsometry.coe_toContinuousLinearMap]
  rw [inner_sum_diagonal (fun i => U i x) (fun i => U i y)
    (fun i j hij => horth i j hij x y)]
  simp only [LinearIsometry.inner_map_map, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hs : (c : ℂ)^2 * (Fintype.card I : ℂ) = 1 := by exact_mod_cast hscale
  calc
    _ = ((c : ℂ)^2 * (Fintype.card I : ℂ)) * inner ℂ x y := by ring
    _ = _ := by rw [hs, one_mul]

def averageIsometry (c : ℝ) (U : I → K →ₗᵢ[ℂ] H)
    (horth : ∀ i j, i ≠ j → ∀ x y : K, inner ℂ (U i x) (U j y) = 0)
    (hscale : c^2 * Fintype.card I = 1) : K →ₗᵢ[ℂ] H where
  toLinearMap := (average c (fun i => (U i).toContinuousLinearMap)).toLinearMap
  norm_map' x := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [norm_sq_eq_re_inner (𝕜 := ℂ), norm_sq_eq_re_inner (𝕜 := ℂ)]
    exact congrArg Complex.re (average_inner c U horth hscale x x)

end Kadison.FiniteCompression

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FiniteTestPatching
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators InnerProductSpace

namespace Kadison.FiniteTest

section Signs

variable {I : Type*} [DecidableEq I]

def character (s : Finset I) (σ : I → Bool) : ℝ := ∏ i ∈ s, sign (σ i)

omit [DecidableEq I] in
@[simp] lemma character_empty (σ : I → Bool) : character ∅ σ = 1 := by simp [character]

end Signs

end Kadison.FiniteTest

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_MatrixAlgebraDensity
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators InnerProductSpace

namespace Kadison.OperatorAmplification

open CyclicColumns CyclicSpatial

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (ι : Type*) [Fintype ι]

attribute [local instance] OAI.Kadison.OperatorAmplification.matrixAlgebraDensityDecidableEq
variable (S : StarSubalgebra ℂ (H →L[ℂ] H)) [IsClosed (S : Set (H →L[ℂ] H))]

attribute [local instance] OAI.Kadison.OperatorAmplification.instPartialOrderSubtypeContinuousLinearMapComplexIdMemStarSubalgebra_solutions
attribute [local instance] OAI.Kadison.OperatorAmplification.instStarOrderedRingSubtypeContinuousLinearMapComplexIdMemStarSubalgebra_solutions
def fullMatrixAlgebra : StarSubalgebra ℂ (SumSpace (H:=H) ι →L[ℂ] SumSpace (H:=H) ι) :=
  letI : DecidableEq ι := matrixAlgebraDensityDecidableEq ι
  (matrixRepresentation (ι:=ι) S.subtype).range

lemma entry_represented (X : CStarMatrix ι ι S) (i j : ι) :
    entry ι (matrixRepresentation S.subtype X) i j=(X i j:H →L[ℂ] H) := by
  ext x
  simp [entry_apply,represented_matrix_apply,single_apply,apply_ite]

lemma mem_fullMatrixAlgebra_iff (T : SumSpace (H:=H) ι →L[ℂ] SumSpace (H:=H) ι) :
    T∈fullMatrixAlgebra ι S ↔ ∀ i j, entry ι T i j∈S := by
  constructor
  · rintro ⟨X,rfl⟩ i j
    change entry ι (matrixRepresentation S.subtype X) i j ∈ S
    rw [entry_represented]
    exact (X i j).property
  · intro h
    let X : CStarMatrix ι ι S := CStarMatrix.ofMatrix (fun i j => ⟨entry ι T i j,h i j⟩)
    refine ⟨X,?_⟩
    change CyclicColumns.matrixAction (entry ι T)=T
    exact reconstruct ι T

lemma diagonal_mem_fullMatrixAlgebra {a : H →L[ℂ] H} (ha : a∈S) :
    diagonal (H:=H) ι a∈fullMatrixAlgebra ι S := by
  rw [mem_fullMatrixAlgebra_iff]
  intro i j
  have he : entry ι (diagonal (H:=H) ι a) i j=if i=j then a else 0 := by
    ext x
    by_cases hij : i=j <;> simp [entry_apply,diagonal_apply,single_apply,hij]
  rw [he]
  split_ifs <;> simp_all

end Kadison.OperatorAmplification

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_KaplanskyFull
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators InnerProductSpace

namespace Kadison.Kaplansky

open OperatorAmplification

attribute [local instance] OAI.Kadison.Kaplansky.instDecidableEqFinOfNatNat_solutions
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def offDiagonal (a : H →L[ℂ] H) : SumSpace (H:=H) (Fin 2) →L[ℂ] SumSpace (H:=H) (Fin 2) :=
  matrixUnit (Fin 2) 0 1*diagonal (H:=H) (Fin 2) a+
    matrixUnit (Fin 2) 1 0*diagonal (H:=H) (Fin 2) (star a)

@[simp] lemma offDiagonal_zero (a : H →L[ℂ] H) (x : SumSpace (H:=H) (Fin 2)) :
    offDiagonal a x 0=a (x 1) := by
  simp [offDiagonal,mul_apply_eq_comp,matrixUnit_apply,single_apply]

@[simp] lemma offDiagonal_one (a : H →L[ℂ] H) (x : SumSpace (H:=H) (Fin 2)) :
    offDiagonal a x 1=star a (x 0) := by
  simp [offDiagonal,mul_apply_eq_comp,matrixUnit_apply,single_apply]

lemma offDiagonal_norm_le {a : H →L[ℂ] H} (ha : ‖a‖≤1) : ‖offDiagonal a‖≤1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  rw [one_mul]
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [PiLp.norm_sq_eq_of_L2,PiLp.norm_sq_eq_of_L2]
  simp only [Fin.sum_univ_two,offDiagonal_zero,offDiagonal_one]
  have h₀ := contraction_apply ha (x 1)
  have h₁ := contraction_apply (a:=star a) (by simpa only [norm_star] using ha) (x 0)
  nlinarith [norm_nonneg (a (x 1)),norm_nonneg (star a (x 0)),norm_nonneg (x 0),norm_nonneg (x 1)]

lemma entry_offDiagonal (a : H →L[ℂ] H) (i j : Fin 2) :
    entry (Fin 2) (offDiagonal a) i j=if i=0 ∧ j=1 then a else if i=1 ∧ j=0 then star a else 0 := by
  ext x
  fin_cases i <;> fin_cases j <;>
    simp [entry_apply,single_apply]

omit [CompleteSpace H] in
lemma single_norm (i : Fin 2) (x : H) : ‖single (Fin 2) i x‖=‖x‖ := by
  have he : single (Fin 2) i x=PiLp.single 2 i x := by
    ext j
    simp [single_apply,PiLp.single_apply]
  rw [he,PiLp.norm_single]

lemma entry_norm_le (T : SumSpace (H:=H) (Fin 2) →L[ℂ] SumSpace (H:=H) (Fin 2)) (i j : Fin 2) :
    ‖entry (Fin 2) T i j‖≤‖T‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro x
  calc
    _≤‖T (single (Fin 2) j x)‖ := PiLp.norm_apply_le _ _
    _≤‖T‖*‖single (Fin 2) j x‖ := T.le_opNorm _
    _=‖T‖*‖x‖ := by rw [single_norm]

end Kadison.Kaplansky

end

end
end

end OAI
end


