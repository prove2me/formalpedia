-- Prove2me | Definitions.Def_OAIQ039C050
-- name    : OAIQ039C050
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T06:28:19.668462+00:00
-- url     : https://prove2.me/theorems/78a0bea8-0519-4767-86e8-235d02cfe44b
-- title:
--   Definitions bundle OAIQ039C050 of the split of OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 11 declarations of OpenAI's Lean: 1 definition and 10 theorems. The definitions and types are `OAI.Kadison.OperatorAmplification.matrixVonNeumann`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis/Commutator, in whole or in part: `Commutator_AmplifiedTowerStage`, `Commutator_MatrixInclusion`, `Commutator_MatrixVonNeumann`, `Commutator_OrbitStateHull`.
--
--   **Imports.** It imports the bundles `OAIQ039C034` and `OAIQ039C039` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ039C056` and `OAIQ039C057`; the statement `OAI.Kadison.OperatorAmplification.matrix_diffuse_of_stages`.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis/Commutator at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ039C034
import Definitions.Def_OAIQ039C039

section
-- module Solutions.OAIQ039_CM.Commutator_MatrixVonNeumann
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open scoped BigOperators InnerProductSpace

namespace Kadison.OperatorAmplification

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (ι : Type*) [Fintype ι] [DecidableEq ι] (i₀ : ι)

def matrixVonNeumann (M : VonNeumannAlgebra H) : VonNeumannAlgebra (SumSpace (H:=H) ι) :=
  (diagonalVonNeumann ι i₀ M.commutant).commutant

lemma mem_matrixVonNeumann (M : VonNeumannAlgebra H)
    (T : SumSpace (H:=H) ι →L[ℂ] SumSpace (H:=H) ι) :
    T∈matrixVonNeumann ι i₀ M ↔ ∀ i j,entry ι T i j∈M := by
  change T∈(diagonalVonNeumann ι i₀ M.commutant).commutant ↔ _
  rw [VonNeumannAlgebra.mem_commutant_iff]
  constructor
  · intro h i j
    rw [←SetLike.mem_coe,←M.centralizer_centralizer]
    intro b hb
    exact entry_commutes ι T b (h (diagonal (H:=H) ι b) ⟨b,VonNeumannAlgebra.mem_commutant_iff.mpr hb,rfl⟩) i j
  · intro h
    rintro _ ⟨b,hb,rfl⟩
    apply commutes_of_entries ι T b
    intro i j
    exact ((VonNeumannAlgebra.mem_commutant_iff.mp hb) _ (h i j)).symm

lemma matrixUnit_mem (M : VonNeumannAlgebra H) (i j : ι) :
    matrixUnit (H:=H) ι i j∈matrixVonNeumann ι i₀ M := by
  apply VonNeumannAlgebra.mem_commutant_iff.mpr
  rintro _ ⟨b,_,rfl⟩
  exact (matrixUnit_commutes ι i j b).symm

lemma diagonal_mem_matrixVonNeumann (M : VonNeumannAlgebra H) {a : H →L[ℂ] H} (ha : a∈M) :
    diagonal (H:=H) ι a∈matrixVonNeumann ι i₀ M := by
  apply VonNeumannAlgebra.mem_commutant_iff.mpr
  rintro _ ⟨b,hb,rfl⟩
  exact (map_mul (diagonal (H:=H) ι) b a).symm.trans
    ((congrArg (diagonal (H:=H) ι) ((VonNeumannAlgebra.mem_commutant_iff.mp hb) a ha).symm).trans (map_mul (diagonal (H:=H) ι) a b))

lemma matrix_representation_mem (M : VonNeumannAlgebra H) (X : CStarMatrix ι ι M) :
    CyclicColumns.matrixRepresentation (A:=M) (H:=H) M.toStarSubalgebra.subtype X∈matrixVonNeumann ι i₀ M := by
  rw [mem_matrixVonNeumann]
  intro i j
  have he : entry ι (CyclicColumns.matrixRepresentation (A:=M) (H:=H) M.toStarSubalgebra.subtype X) i j=
      (X i j:H →L[ℂ] H) := by
    ext x
    simp only [entry_apply,CyclicColumns.matrixRepresentation,CyclicColumns.matrixAction_apply,
      StarAlgHom.coe_mk]
    simp [apply_ite]
    rfl
  rw [he]
  exact (X i j).property

lemma matrixVonNeumann_is_range (M : VonNeumannAlgebra H)
    (T : SumSpace (H:=H) ι →L[ℂ] SumSpace (H:=H) ι) (hT : T∈matrixVonNeumann ι i₀ M) :
    ∃ X : CStarMatrix ι ι M,CyclicColumns.matrixRepresentation (A:=M) (H:=H) M.toStarSubalgebra.subtype X=T := by
  have h := (mem_matrixVonNeumann ι i₀ M T).mp hT
  let X : CStarMatrix ι ι M := CStarMatrix.ofMatrix (fun i j => ⟨entry ι T i j,h i j⟩)
  exact ⟨X,reconstruct ι T⟩

end Kadison.OperatorAmplification

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_AmplifiedTowerStage
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator

namespace Kadison.OperatorAmplification

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (ι : Type) [Fintype ι] (i₀ : ι) (M : VonNeumannAlgebra H)

attribute [local instance] OAI.Kadison.OperatorAmplification.amplifiedTowerStageDecidableEq
omit [CompleteSpace H] [Fintype ι] in
lemma matrixUnit_mul (i j k l : ι) : matrixUnit (H:=H) ι i j*matrixUnit ι k l=
    if j=k then matrixUnit ι i l else 0 := by
  ext x a
  by_cases h : j=k
  · subst k
    simp [mul_apply_eq_comp]
  · simp [mul_apply_eq_comp,single_apply,h]

lemma matrixUnit_star (i j : ι) : star (matrixUnit (H:=H) ι i j)=matrixUnit ι j i := by
  rw [ContinuousLinearMap.star_eq_adjoint]
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro x y
  simp only [matrixUnit_apply,PiLp.inner_apply,single_apply]
  have hl : (∑ k : ι,inner ℂ (if k=j then x i else 0) (y k))=inner ℂ (x i) (y j) := by
    rw [Finset.sum_eq_single j]
    · simp
    · intro k _ hk
      simp [hk]
    · simp
  have hr : (∑ k : ι,inner ℂ (x k) (if k=i then y j else 0))=inner ℂ (x i) (y j) := by
    simp [apply_ite]
  exact hl.trans hr.symm

omit [CompleteSpace H] in
lemma sum_matrixUnit : (∑ i : ι,matrixUnit (H:=H) ι i i)=1 := by
  ext x a
  simp [matrixUnit_apply,single_apply]

end Kadison.OperatorAmplification

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_MatrixInclusion
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier
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

variable (ι : Type*) [Fintype ι] [DecidableEq ι] (i₀ : ι)

lemma matrixVonNeumann_mono {Q M : VonNeumannAlgebra H} (hQM : Q≤M) :
    matrixVonNeumann ι i₀ Q ≤ matrixVonNeumann ι i₀ M := by
  intro X hX
  rw [mem_matrixVonNeumann] at hX ⊢
  exact fun i j => hQM (hX i j)

end Kadison.OperatorAmplification

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_OrbitStateHull
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open Filter

open scoped ComplexOrder InnerProductSpace Topology

namespace Kadison.OrbitStateHull

open PartialIsometryOrder PartialIsometryOrder.DyadicPartition

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H)

lemma hull_nonneg (x : H) {f : WeakDual ℂ M} (hf : f∈hull M x)
    {a : M} (ha : 0≤a) : 0≤f a := by
  apply WeakDualHull.eval_nonneg a _ hf
  rintro g ⟨u,_,rfl⟩
  exact vector_nonneg M _ ha

end Kadison.OrbitStateHull

end

end
end

end OAI
end


