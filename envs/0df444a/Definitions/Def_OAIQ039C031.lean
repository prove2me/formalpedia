-- Prove2me | Definitions.Def_OAIQ039C031
-- name    : OAIQ039C031
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T06:17:41.947318+00:00
-- url     : https://prove2.me/theorems/ac3f3030-814e-4861-94f1-e960ee67a7eb
-- title:
--   Definitions bundle OAIQ039C031 of the split of OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 8 declarations of OpenAI's Lean: 4 definitions, 1 instance and 3 theorems. The definitions and types are `OAI.Kadison.UnitaryOrbit.conjugateLinear`, `OAI.Kadison.UnitaryTransport.algebra`, `OAI.Kadison.WOTDistance.AmplifiedBound`, `OAI.Kadison.countableContractions`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis/Commutator, in whole or in part: `Commutator_ArvesonAnnihilator`, `Commutator_CountableStarHomTests`, `Commutator_FiniteRectangularContraction`, `Commutator_FiniteSquareContraction`, `Commutator_UnitaryMainTransport`, `Commutator_UnitaryOrbitHull`.
--
--   **Imports.** It imports the bundles `OAIQ039C001`, `OAIQ039C002`, `OAIQ039C008` and `OAIQ039C014` of this split.
--
--   **Imported by** (directly, in this split): the statements `OAI.Kadison.CentralSpectral.central_indicators`, `OAI.Kadison.CentralSpectral.stable_model_center`, `OAI.Kadison.InfiniteAmplification.stable_center_range`, `OAI.Kadison.UnitaryTransport.bound_of_conjugate_bound`, `OAI.Kadison.WOTDistance.annihilator_bound` and `OAI.Kadison.WOTDistance.exists_commutant_approximation`; the proofs of `OAI.Kadison.CentralAverage.exists_finite_average`, `OAI.Kadison.CentralSpectral.central_indicators`, `OAI.Kadison.CentralSpectral.stable_model_bound`, `OAI.Kadison.CentralSpectral.stable_model_center`, `OAI.Kadison.CyclicSpatial.exists_cyclic_intertwiner`, `OAI.Kadison.Decomposable.exists_common_tests`, `OAI.Kadison.InfiniteAmplification.stable_center_range`, `OAI.Kadison.MatrixTower.rectangular_bound_after_average`, `OAI.Kadison.MatrixTower.rectangular_contraction_after_average`, `OAI.Kadison.MatrixTower.square_contraction_after_average`, `OAI.Kadison.UnitaryTransport.bound_of_conjugate_bound`, `OAI.Kadison.WOTDistance.annihilator_bound`, `OAI.Kadison.WOTDistance.exists_commutant_approximation` and `OAI.Kadison.uniform_commutator`.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis/Commutator at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ039C001
import Definitions.Def_OAIQ039C002
import Definitions.Def_OAIQ039C008
import Definitions.Def_OAIQ039C014

section
-- module Solutions.OAIQ039_CM.Commutator_ArvesonAnnihilator
attribute [-instance] _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators InnerProductSpace

open ContinuousLinearMapWOT

namespace Kadison.WOTDistance

open OperatorAmplification

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def AmplifiedBound (M : VonNeumannAlgebra H) (G : H →L[ℂ] H) (c : ℝ) : Prop :=
  ∀ (n : ℕ) (T : SumSpace (H:=H) (Fin n) →L[ℂ] SumSpace (H:=H) (Fin n)),
    (∀ i j, entry (Fin n) T i j∈M) →
      ‖diagonal (H:=H) (Fin n) G*T-T*diagonal (H:=H) (Fin n) G‖ ≤ c*‖T‖

end Kadison.WOTDistance

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_CountableStarHomTests
attribute [-instance] _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open Filter

open scoped Topology

namespace Kadison

variable {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [TopologicalSpace.SeparableSpace A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]

instance contraction_nonempty : Nonempty (CStarContractions A) := ⟨⟨0,by simp⟩⟩

def countableContractions : ℕ → A := fun n =>
  (TopologicalSpace.denseSeq (CStarContractions A) n).val

end Kadison

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FiniteSquareContraction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open scoped InnerProductSpace ComplexOrder Matrix.Norms.L2Operator

open Filter

namespace Kadison.MatrixTower

open OperatorAmplification

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (ι : Type) [Fintype ι] [Nonempty ι] (i₀ : ι)

local instance instDecidableEq_solutions_rd4f916_1 : DecidableEq ι := Classical.decEq ι
attribute [local instance] OAI.Kadison.MatrixTower.finiteSquareContractionDoubledIndexDecidableEq
omit [Fintype ι] [Nonempty ι] in
@[defeq] theorem square_index_decidable_eq :
    (inferInstance : DecidableEq ((Fin 2)×ι)) = Classical.decEq _ := rfl

end Kadison.MatrixTower

end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FiniteRectangularContraction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open scoped InnerProductSpace ComplexOrder Matrix.Norms.L2Operator

open Filter

namespace Kadison.MatrixTower

open OperatorAmplification

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (ι κ : Type) [Fintype ι] [Fintype κ] [Nonempty κ] (k₀ : κ)

local instance finiteRectangularContractionIndexDecidableEq_rd4f916_1 : DecidableEq ι := Classical.decEq ι
local instance finiteRectangularContractionColumnDecidableEq_rd4f916_1 : DecidableEq κ := Classical.decEq κ
local instance finiteRectangularContractionSumDecidableEq_rd4f916_1 : DecidableEq (κ⊕ι) := Classical.decEq _
attribute [local instance] OAI.Kadison.MatrixTower.finiteRectangularContractionDoubledSumDecidableEq
omit [Fintype ι] [Fintype κ] [Nonempty κ] in
@[defeq] theorem rectangular_index_decidable_eq :
    (inferInstance : DecidableEq ((Fin 2)×(κ⊕ι))) = Classical.decEq _ := rfl

end Kadison.MatrixTower

end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_UnitaryMainTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace BigOperators

namespace Kadison.UnitaryTransport

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

variable (U : H ≃ₗᵢ[ℂ] K)

def algebra (M : VonNeumannAlgebra H) : VonNeumannAlgebra K where
  toStarSubalgebra := M.toStarSubalgebra.map U.conjStarAlgEquiv.toStarAlgHom
  centralizer_centralizer' := by
    change Set.centralizer (Set.centralizer (U.conjStarAlgEquiv.toMulEquiv '' (M : Set (H →L[ℂ] H))))=_
    rw [EquivariantBicommutant.bicommutant_image U.conjStarAlgEquiv.toMulEquiv]
    change U.conjStarAlgEquiv.toMulEquiv '' Set.centralizer (Set.centralizer M.carrier)=_
    rw [M.centralizer_centralizer']
    rfl

@[simp] lemma mem_algebra (M : VonNeumannAlgebra H) (a : H →L[ℂ] H) :
    U.conjStarAlgEquiv a∈algebra U M ↔ a∈M := by
  change (∃ b,b∈M ∧ U.conjStarAlgEquiv b=U.conjStarAlgEquiv a) ↔ a∈M
  constructor
  · rintro ⟨b,hb,he⟩
    exact U.conjStarAlgEquiv.injective he ▸ hb
  · intro ha; exact ⟨a,ha,rfl⟩

end Kadison.UnitaryTransport

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_UnitaryOrbitHull
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace

namespace Kadison.UnitaryOrbit

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H)

def conjugateLinear (v : unitary M) : (H →L[ℂ] H) →ₗ[ℝ] (H →L[ℂ] H) where
  toFun := conjugate M v
  map_add' _ _ := by simp [conjugate,mul_add,add_mul]
  map_smul' _ _ := by simp [conjugate]

end Kadison.UnitaryOrbit

end

end
end

end OAI
end


