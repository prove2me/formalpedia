-- Prove2me | Definitions.Def_OAIB3Kr014
-- name    : OAIB3Kr014
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-25T17:08:04.532157+00:00
-- url     : https://prove2.me/theorems/a1e8da08-2cbb-48a0-ad09-02ac45c98978
-- title:
--   Definitions bundle OAIB3Kr014 of the split of OpenAI, The Kirchberg–Rørdam character criterion
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.KirchbergRordam.character_criterion`, carved from OpenAI's openai/math development (OpenAI, *The Kirchberg–Rørdam character criterion*, OpenAI Math Release, September 25, 2026, result family 299, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 9 declarations of OpenAI's Lean: 7 definitions and 2 instances. The definitions and types are `OAI.KirchbergRordam.PrimeSquareUnitary.diagram`, `OAI.KirchbergRordam.PrimeSquareUnitary.unitarySection`, `OAI.KirchbergRordam.PrimeTensorSections.fiberRange`, `OAI.KirchbergRordam.PrimeTensorSections.sectionRange`, `OAI.KirchbergRordam.dropCoordinate`, `OAI.KirchbergRordam.leftCone`, `OAI.KirchbergRordam.rightCone`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`CharacterCriterion_BalancedLimit`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/CharacterCriterion/BalancedLimit.lean), [`CharacterCriterion_PrimePresentation`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/CharacterCriterion/PrimePresentation.lean), [`CharacterCriterion_PrimeSquare`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/CharacterCriterion/PrimeSquare.lean), [`CharacterCriterion_TensorSections`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/CharacterCriterion/TensorSections.lean).
--
--   **Imports.** It imports the published bundle `Def_CharacterCriterion`; the bundles `OAIB3Kr010` and `OAIB3Kr012` of this split.
--
--   **Imported by** (directly, in this split): the statements `OAI.KirchbergRordam.PrimeSquareUnitary.exists_unitary`, `OAI.KirchbergRordam.PrimeSquareUnitary.fibers` and `OAI.KirchbergRordam.PrimeTensorSections.sectionRange_scalar`; the proofs of `OAI.KirchbergRordam.PrimeDropPresentation.Channels.finite_control`, `OAI.KirchbergRordam.PrimeDropPresentation.HalfFlip.finite_stage`, `OAI.KirchbergRordam.PrimeDropPresentation.central_no_character`, `OAI.KirchbergRordam.PrimeSquareUnitary.exists_unitary`, `OAI.KirchbergRordam.PrimeSquareUnitary.fibers`, `OAI.KirchbergRordam.PrimeTensorSections.sectionRange_scalar` and `OAI.KirchbergRordam.character_criterion`.
-- source:
--   OpenAI, The Kirchberg–Rørdam character criterion, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 299; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Kirchberg-Rordam-character-criterion-September-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit adc7f12

import Mathlib
import Definitions.Def_CharacterCriterion
import Definitions.Def_OAIB3Kr010
import Definitions.Def_OAIB3Kr012

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_BalancedLimit
attribute [-instance] _root_.OAI.KirchbergRordam.PureStates.locallyConvexReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
open scoped InnerProductSpace
open scoped BigOperators
open Set Module
open Topology
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped InnerProductSpace
open NormedSpace
open scoped TensorProduct InnerProductSpace
open UniformSpace
variable [KirchbergRordam.GenericRW.Size]
variable [KirchbergRordam.GenericRW.PauliData]
omit [KirchbergRordam.GenericRW.Size] [KirchbergRordam.GenericRW.PauliData]
open Filter Topology BoundedContinuousFunction
open Filter Topology
open Topology
open scoped TensorProduct CStarAlgebra
open scoped CStarAlgebra ComplexOrder


namespace KirchbergRordam

open scoped Matrix Kronecker ComplexOrder


def dropCoordinate : DimensionDrop23 :=
  ⟨⟨fun t => ((t : ℝ) : ℂ) • (1 : M6), by fun_prop⟩,
    by
      constructor
      · change ∃ a : M2, leftMatrix a = ((0 : unitInterval) : ℝ) • (1 : M6)
        exact ⟨0, by simp⟩
      · change ∃ a : M3, rightMatrix a = ((1 : unitInterval) : ℝ) • (1 : M6)
        exact ⟨1, by simp⟩⟩


def leftCone (a : M2) : DimensionDrop23 :=
  ⟨⟨fun t => (1 - ((t : ℝ) : ℂ)) • leftMatrix a, by fun_prop⟩,
    by
      constructor
      · refine ⟨a, ?_⟩
        change leftMatrix a = (1 - (((0 : unitInterval) : ℝ) : ℂ)) • leftMatrix a
        simp
      · refine ⟨0, ?_⟩
        change rightMatrix 0 = (1 - (((1 : unitInterval) : ℝ) : ℂ)) • leftMatrix a
        simp⟩


def rightCone (a : M3) : DimensionDrop23 :=
  ⟨⟨fun t => ((t : ℝ) : ℂ) • rightMatrix a, by fun_prop⟩,
    by
      constructor
      · refine ⟨0, ?_⟩
        change leftMatrix 0 = (((0 : unitInterval) : ℝ) : ℂ) • rightMatrix a
        simp
      · refine ⟨a, ?_⟩
        change rightMatrix a = (((1 : unitInterval) : ℝ) : ℂ) • rightMatrix a
        simp⟩


end KirchbergRordam


end

end OAI
end

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_TensorSections
attribute [-instance] _root_.OAI.KirchbergRordam.MinTensor.instCStarRingAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
open scoped InnerProductSpace
open scoped BigOperators
open Set Module
open Topology
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped InnerProductSpace
open NormedSpace
open scoped TensorProduct InnerProductSpace
open UniformSpace
variable [KirchbergRordam.GenericRW.Size]
variable [KirchbergRordam.GenericRW.PauliData]
omit [KirchbergRordam.GenericRW.Size] [KirchbergRordam.GenericRW.PauliData]
open Filter Topology BoundedContinuousFunction
open Filter Topology
open Topology
open scoped TensorProduct CStarAlgebra
open scoped CStarAlgebra ComplexOrder
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace

namespace KirchbergRordam.PrimeTensorSections
open scoped CStarAlgebra ComplexOrder TensorProduct
open PrimeDimensionDrop MatrixTensor ContinuousSectionLocality
variable {p q r k : ℕ}

def sectionRange : StarSubalgebra ℂ C(Square,SquareFiber p q r k) :=
  (sectionMap (p:=p) (q:=q) (r:=r) (k:=k)).range


def fiberRange (x : Square) : StarSubalgebra ℂ (SquareFiber p q r k) :=
  (subKronecker (evaluation p q x.1).range (evaluation r k x.2).range).range

end KirchbergRordam.PrimeTensorSections
end

end OAI
end

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_PrimeSquare
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
open scoped InnerProductSpace
open scoped BigOperators
open Set Module
open Topology
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped InnerProductSpace
open NormedSpace
open scoped TensorProduct InnerProductSpace
open UniformSpace
variable [KirchbergRordam.GenericRW.Size]
variable [KirchbergRordam.GenericRW.PauliData]
omit [KirchbergRordam.GenericRW.Size] [KirchbergRordam.GenericRW.PauliData]
open Filter Topology BoundedContinuousFunction
open Filter Topology
open Topology
open scoped TensorProduct CStarAlgebra
open scoped CStarAlgebra ComplexOrder
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped CStarAlgebra ComplexOrder

namespace KirchbergRordam.PrimeSquareUnitary
open scoped CStarAlgebra ComplexOrder
open MatrixTensor PrimeDimensionDrop PrimeTensorSections FourLegSymmetries
variable {p q : ℕ}

def diagram (u : unitInterval → unitary (Fiber p q)) (hu : Continuous u) (h0 : u 0=1) :
    SymmetryConjugacyDiagram.Data (SquareFiber p q p q) where
  H := H
  K := K
  hH := H_selfadjoint
  hK := K_selfadjoint
  commute := flips_commute
  L t := Unitary.map (StarMonoidHom.ofClass (MatrixTensor.leftMatrix (ι:=Fin p×Fin q) (κ:=Fin p×Fin q))) (u t)
  continuous_L := by
    apply Continuous.subtype_mk
    exact (continuous_starHom (A:=(Fiber p q)) (B:=(SquareFiber p q p q)) MatrixTensor.leftMatrix).comp (continuous_subtype_val.comp hu)
  L_zero := by
    apply Subtype.ext
    change MatrixTensor.leftMatrix (u 0 : Fiber p q)=1
    rw [h0]
    exact map_one _

variable (u : unitInterval → unitary (Fiber p q)) (hu : Continuous u) (h0 : u 0=1)

def unitarySection : C(Square,(SquareFiber p q p q)) := ⟨fun x => ((diagram u hu h0).W x:(SquareFiber p q p q)),continuous_subtype_val.comp (diagram u hu h0).W_continuous⟩
end KirchbergRordam.PrimeSquareUnitary


end

end OAI
end

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_PrimePresentation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
open scoped InnerProductSpace
open scoped BigOperators
open Set Module
open Topology
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped InnerProductSpace
open NormedSpace
open scoped TensorProduct InnerProductSpace
open UniformSpace
variable [KirchbergRordam.GenericRW.Size]
variable [KirchbergRordam.GenericRW.PauliData]
omit [KirchbergRordam.GenericRW.Size] [KirchbergRordam.GenericRW.PauliData]
open Filter Topology BoundedContinuousFunction
open Filter Topology
open Topology
open scoped TensorProduct CStarAlgebra
open scoped CStarAlgebra ComplexOrder
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped CStarAlgebra ComplexOrder
open scoped TensorProduct InnerProductSpace
open UniformSpace

namespace KirchbergRordam.PrimeDropPresentation
open scoped CStarAlgebra ComplexOrder
variable (S : PrimeDropPresentation)
instance instSeparableSpaceStage (n : ℕ) : TopologicalSpace.SeparableSpace (S.Stage n) := inferInstanceAs
  (TopologicalSpace.SeparableSpace (PrimeDimensionDrop.Algebra (S.size n) (S.size n+1)))
instance instSeparableSpaceObjSystem (n : ℕ) : TopologicalSpace.SeparableSpace (S.system.obj n) :=
  inferInstanceAs (TopologicalSpace.SeparableSpace (S.Stage n))
end KirchbergRordam.PrimeDropPresentation
end

end OAI
end


