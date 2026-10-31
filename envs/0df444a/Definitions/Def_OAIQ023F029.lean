-- Prove2me | Definitions.Def_OAIQ023F029
-- name    : OAIQ023F029
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T19:21:58.712031+00:00
-- url     : https://prove2.me/theorems/550cd787-40ec-4155-a0ca-376d9fec64da
-- title:
--   Definitions bundle OAIQ023F029 of the split of OpenAI, An algebra of infinite little finitistic dimension (result family 198)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.LittleFinitistic.Main.exists_counterexample`, carved from OpenAI's openai/math development (OpenAI, *An algebra of infinite little finitistic dimension (result family 198)*, OpenAI Math Release, September 23, 2026, result family 198, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1 declaration of OpenAI's Lean: 1 theorem.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: [`Finitistic_Localization_ConcreteFixedDiagram`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/Finitistic/Localization/ConcreteFixedDiagram.lean).
--
--   **Imports.** It imports the bundle `OAIQ023F026` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ023F031`.
-- source:
--   OpenAI, An algebra of infinite little finitistic dimension (result family 198), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 198; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-algebra-of-infinite-little-finitistic-dimension-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ023F026

section
-- module Solutions.OAIQ023_Fin.Finitistic_Localization_ConcreteFixedDiagram
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.instAddCommGroupEvaluation _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.instFiniteDimensionalEvaluation _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.instModuleEvaluation _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.evaluationExact _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.evaluationFacShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.evaluationLift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.evaluationShift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Idempotents
namespace LittleFinitistic.ConcreteFixedDiagram
open SelectionEncoding RelationBasisCoefficients RelationBasisAction FormalSummandAction
universe u v
variable {k : Type u} [Field k] {R : Type v} [Ring R] [Algebra k R]
variable (E : Encoding k R)

attribute [local instance] OAI.LittleFinitistic.ConcreteFixedDiagram.instHasFiniteBiproductsKaroubiQRelations
attribute [local instance] OAI.LittleFinitistic.ConcreteFixedDiagram.instHasBinaryBiproductsKaroubiQRelations
/-- The fixed odd-double diagram in the actual Kᵇ(proj-B) and its actual Verdier
quotient. Every independent relation of the constructed path algebra is included. -/
theorem fixed_diagram {L : SourceVerdier.Q E.relations} (θ : R →ₐ[k] End L)
    (e : R) (he : e*e=e) (hec : ∀ r : R, e*r=r*e) (α : R →ₐ[k] R) :
    ∃ (V₀ : SourceVerdier.Q E.relations) (ρ₀ : R →ₐ[k] End V₀)
      (i : (toKaroubi (SourceVerdier.Q E.relations)).obj V₀ ≅
        summand θ e he ⊞ OddDouble.formalShift (summand θ e he) 3)
      (D₀ D₁ D₂ : SourceVerdier.K E.relations)
      (φ₀ : (SourceVerdier.q E.relations).obj D₀ ≅ V₀)
      (φ₁ : (SourceVerdier.q E.relations).obj D₁ ≅ V₀)
      (φ₂ : (SourceVerdier.q E.relations).obj D₂ ≅ V₀)
      (f : Fin (E.generators+1) → (D₀ ⟶ D₁))
      (g : Fin (E.generators+1) → (D₁ ⟶ D₂)),
      (∀ r : R, (toKaroubi (SourceVerdier.Q E.relations)).map (ρ₀ r) ≫ i.hom =
        i.hom ≫ oddDoubleAction θ e he hec α r) ∧
      (∀ a, (SourceVerdier.q E.relations).map (f a) ≫ φ₁.hom =
        φ₀.hom ≫ ρ₀ (arrow (generator E) a)) ∧
      (∀ b, (SourceVerdier.q E.relations).map (g b) ≫ φ₂.hom =
        φ₁.hom ≫ ρ₀ (arrow (generator E) b)) ∧
      (∀ r : RelationIndex E.relations,
        ∑ a, ∑ b, basisCoefficient E.relations r a b • (f a ≫ g b) = 0) :=
  FixedDiagram.fixed_diagram (SourceVerdier.q E.relations) (SourceVerdier.Sigma E.relations)
    θ e he hec α (E.generators+1) (E.generators+1)
    (Module.finrank k (QuadraticEncoding.relationSpace E.relations))
    (arrow (generator E)) (arrow (generator E)) (basisCoefficient E.relations)
    (encoding_basis_action E)
end LittleFinitistic.ConcreteFixedDiagram

end

end OAI
end


