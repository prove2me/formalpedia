-- Prove2me | Definitions.Def_OAIQ039C062
-- name    : OAIQ039C062
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T09:17:31.447548+00:00
-- url     : https://prove2.me/theorems/9fb556de-bc80-47cd-b3da-b3e1af6f208a
-- title:
--   Definitions bundle OAIQ039C062 of the split of OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 9 declarations of OpenAI's Lean: 5 definitions and 4 theorems. The definitions and types are `OAI.Kadison.MatrixTower.scalarStage`, `OAI.Kadison.NormalRepresentation.diagonalAlgebra`, `OAI.Kadison.NormalRepresentation.finiteStandardCompressionDecidableEq`, `OAI.Kadison.OperatorAmplification.diagonalHom`, `OAI.Kadison.OperatorAmplification.scalarMatrixHom`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis/Commutator, in whole or in part: `Commutator_AmplifiedTowerStage`, `Commutator_FiniteStandardCompression`, `Commutator_MatrixDiffuseTransfer`, `Commutator_MatrixTower`, `Commutator_NormalBiprodGNS`, `Commutator_NormalOperatorHom`, `Commutator_NormalRepresentationLinks`.
--
--   **Imports.** It imports the bundles `OAIQ039C054`, `OAIQ039C056` and `OAIQ039C057` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ039C067` and `OAIQ039C075`; the statements `OAI.Kadison.NormalRepresentation.diagonal_factor`, `OAI.Kadison.NormalRepresentation.exists_orthogonal_links`, `OAI.Kadison.NormalRepresentation.exists_orthogonal_links_of_faithful`, `OAI.Kadison.NormalRepresentation.finiteColumn_intertwines`, `OAI.Kadison.NormalRepresentation.link_intertwines`, `OAI.Kadison.NormalRepresentation.right_full_central_support`, `OAI.Kadison.NormalRepresentation.right_mem_commutant` and `OAI.Kadison.OperatorAmplification.matrixTrace_diagonal`; the proofs of `OAI.Kadison.NormalRepresentation.diagonal_factor`, `OAI.Kadison.NormalRepresentation.exists_countable_gns_embedding`, `OAI.Kadison.NormalRepresentation.exists_orthogonal_links`, `OAI.Kadison.NormalRepresentation.exists_orthogonal_links_of_faithful`, `OAI.Kadison.NormalRepresentation.finiteColumn_intertwines`, `OAI.Kadison.NormalRepresentation.finite_standard_compression_bound`, `OAI.Kadison.NormalRepresentation.link_intertwines`, `OAI.Kadison.NormalRepresentation.right_full_central_support`, `OAI.Kadison.NormalRepresentation.right_mem_commutant`, `OAI.Kadison.NormalRepresentation.separable_traced_factor_bound`, `OAI.Kadison.OperatorAmplification.matrixTrace_diagonal` and `OAI.Kadison.OperatorAmplification.matrix_diffuse_of_stages`.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis/Commutator at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ039C054
import Definitions.Def_OAIQ039C056
import Definitions.Def_OAIQ039C057

section
-- module Solutions.OAIQ039_CM.Commutator_MatrixTower
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder BigOperators InnerProductSpace

namespace Kadison.MatrixTower

open TracialGNS MatrixExpectation

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

attribute [instance] Stage.finite Stage.dec Stage.nonempty

variable (M : VonNeumannAlgebra H) (τ : M →ₚ[ℂ] ℂ)

variable (hτ : ∀ a b : M,τ (a*b)=τ (b*a)) (hnormal : NormalGNS.BoundedWOTContinuous M τ)
  (hfaith : ∀ a : M,τ (star a*a)=0 → a=0) (hone : τ 1=1)
  (hfac : FactorCorner.IsFactor M) (hdiffuse : DiffuseProjection.HasNoMinimalProjections M)

def scalarStage : Stage M where
  I := Unit
  finite := inferInstance
  dec := inferInstance
  nonempty := inferInstance
  hom := MatrixUnits.representation (fun _ _ => (1:M)) (by intros; simp)
    (by intros; simp) (by simp)

end Kadison.MatrixTower

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_MatrixDiffuseTransfer
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open scoped BigOperators InnerProductSpace ComplexOrder

namespace Kadison.OperatorAmplification

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (ι : Type*) [Fintype ι] (i₀ : ι) (M : VonNeumannAlgebra H)

attribute [local instance] OAI.Kadison.OperatorAmplification.matrixDiffuseTransferIndexDecidableEq
def diagonalHom : M →⋆ₐ[ℂ] matrixVonNeumann ι i₀ M :=
  rangeRestriction (matrixVonNeumann ι i₀ M)
    ((diagonal (H:=H) ι).comp M.toStarSubalgebra.subtype)
    (fun a => diagonal_mem_matrixVonNeumann ι i₀ M a.property)

lemma coe_diagonalHom (a : M) :
    (diagonalHom ι i₀ M a:SumSpace (H:=H) ι →L[ℂ] SumSpace (H:=H) ι)=
      diagonal (H:=H) ι (a:H →L[ℂ] H) := rfl

end Kadison.OperatorAmplification

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_AmplifiedTowerStage
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.UnitaryDualAction.action
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
def scalarMatrixHom : Matrix ι ι ℂ →⋆ₐ[ℂ] matrixVonNeumann ι i₀ M :=
  MatrixUnits.representation (fun i j => ⟨matrixUnit ι i j,matrixUnit_mem ι i₀ M i j⟩)
    (by
      intro i j k l
      apply Subtype.ext
      change matrixUnit ι i j*matrixUnit ι k l=_
      rw [matrixUnit_mul]
      split_ifs <;> rfl)
    (by intro i j; apply Subtype.ext; exact matrixUnit_star ι i j)
    (by
      apply Subtype.ext
      change (matrixVonNeumann ι i₀ M).toStarSubalgebra.subtype
        (∑ i : ι,⟨matrixUnit ι i i,matrixUnit_mem ι i₀ M i i⟩)=1
      rw [map_sum]
      exact sum_matrixUnit (H:=H) ι)

lemma scalarMatrixHom_coe (x : Matrix ι ι ℂ) :
    (scalarMatrixHom ι i₀ M x:SumSpace (H:=H) ι →L[ℂ] SumSpace (H:=H) ι)=
      ∑ i,∑ j,x i j • matrixUnit ι i j := by
  change (matrixVonNeumann ι i₀ M).toStarSubalgebra.subtype
    (∑ i,∑ j,x i j • ⟨matrixUnit ι i j,matrixUnit_mem ι i₀ M i j⟩)=_
  simp only [map_sum,map_smul]
  rfl

end Kadison.OperatorAmplification

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FiniteStandardCompression
attribute [-instance] _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open scoped ComplexOrder InnerProductSpace

namespace Kadison.NormalRepresentation

open OperatorAmplification IntertwinerCompression MatrixTower


variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H) [Nontrivial M] (τ : M →ₚ[ℂ] ℂ)

variable (ι : Type) [Fintype ι] [Nonempty ι]

local instance finiteStandardCompressionDecidableEq : DecidableEq ι := Classical.decEq ι

end Kadison.NormalRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_NormalOperatorHom
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open scoped Topology

open Filter ContinuousLinearMapWOT

namespace Kadison.NormalOperatorHom

variable {H G : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

variable (M : VonNeumannAlgebra H) (φ : M →⋆ₐ[ℂ] (G →L[ℂ] G))

theorem range_bicommutant (hφ : BoundedNormal M φ) :
    Set.centralizer (Set.centralizer (Set.range φ))=Set.range φ := by
  classical
  apply BicommutantRange.operatorHom_range
  intro T hT hsT hnT
  let a := Kaplansky.starHomNet φ T hT hsT hnT
  let ω : Ultrafilter (Finset G × ℕ) := Ultrafilter.of atTop
  have hω : (ω : Filter (Finset G × ℕ))≤atTop := Ultrafilter.of_le _
  have ha : ∀ i,‖a i‖≤1 := fun i => (Kaplansky.starHomNet_spec φ T hT hsT hnT i).1
  obtain ⟨W,hW,hlim⟩ := WeakOperatorLimit.exists_ultralimit ω
    (fun i => (a i:H →L[ℂ] H)) 1 (by norm_num) ha
  have hWM : W∈M := WeakOperatorLimit.mem_vonNeumann hlim M
    (Eventually.of_forall fun i => (a i).property)
  let b : M := ⟨W,hWM⟩
  refine ⟨b,?_⟩
  ext y
  apply ext_inner_left ℂ
  intro x
  have hb := tendsto M φ hφ a b 1 ha hW hlim x y
  have hc : Continuous (fun z : G => inner ℂ x z) := continuous_const.inner continuous_id
  have ht := (hc.tendsto (T y)).comp
    ((Kaplansky.starHomNet_tendsto φ T hT hsT hnT y).mono_left hω)
  exact tendsto_nhds_unique hb ht

end Kadison.NormalOperatorHom

end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_NormalBiprodGNS
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open scoped Topology ComplexOrder NNReal

open Filter ContinuousLinearMapWOT

namespace Kadison.NormalOperatorHom

variable {H G : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

variable (M : VonNeumannAlgebra H)

lemma diagonal_gns_range (τ : M →ₚ[ℂ] ℂ) (hτ : NormalGNS.BoundedWOTContinuous M τ) :
    Set.centralizer (Set.centralizer
      (Set.range (HilbertBiprod.diagHom (A:=M) (H:=H) (G:=τ.GNS) M.toStarSubalgebra.subtype τ.gnsStarAlgHom)))=
      Set.range (HilbertBiprod.diagHom (A:=M) (H:=H) (G:=τ.GNS) M.toStarSubalgebra.subtype τ.gnsStarAlgHom) :=
  range_bicommutant M _ (diag_normal M _ _ (subtype_normal M) (gns_normal M τ hτ))

end Kadison.NormalOperatorHom

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_NormalRepresentationLinks
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open scoped ComplexOrder InnerProductSpace Topology

namespace Kadison.NormalRepresentation

open HilbertBiprod PartialIsometryOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H) (τ : M →ₚ[ℂ] ℂ)

def diagonalAlgebra (hnormal : NormalGNS.BoundedWOTContinuous M τ) :
    VonNeumannAlgebra (Space H τ.GNS) :=
  BicommutantRange.ofStarHom (A:=M) (H:=Space H τ.GNS)
    (diagHom (A:=M) (H:=H) (G:=τ.GNS) M.toStarSubalgebra.subtype τ.gnsStarAlgHom)
    (NormalOperatorHom.diagonal_gns_range M τ hnormal)

end Kadison.NormalRepresentation

end

end
end

end OAI
end


