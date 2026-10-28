-- Prove2me | Definitions.Def_OAIQ039C075
-- name    : OAIQ039C075
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T09:31:46.012236+00:00
-- url     : https://prove2.me/theorems/74b3af51-e312-4bc2-ad85-e8e431088600
-- title:
--   Definitions bundle OAIQ039C075 of the split of OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 2 declarations of OpenAI's Lean: 2 definitions. The definitions and types are `OAI.Kadison.MatrixTower.next`, `OAI.Kadison.MatrixTower.tower`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis/Commutator, in whole or in part: `Commutator_MatrixTower`.
--
--   **Imports.** It imports the bundles `OAIQ039C062` and `OAIQ039C074` of this split.
--
--   **Imported by** (directly, in this split): the statement `OAI.Kadison.MatrixTower.tower_requirement`; the proofs of `OAI.Kadison.MatrixTower.exists_irreducible_stage_tower` and `OAI.Kadison.MatrixTower.tower_requirement`.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis/Commutator at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ039C062
import Definitions.Def_OAIQ039C074

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

variable (x : ℕ → M) (hx : ∀ j,IsSelfAdjoint (x j))

def next (n : ℕ) (F : Stage M) : Stage M :=
  Classical.choose (exists_stage_extension M τ hτ hnormal hfaith hone hfac hdiffuse F
    (x (Nat.unpair n).1) (hx _) (show 0<((Nat.unpair n).2+1:ℝ)⁻¹ by positivity))

def tower : ℕ → Stage M
  | 0 => scalarStage M
  | n+1 => next M τ hτ hnormal hfaith hone hfac hdiffuse x hx n
      (tower n)

end Kadison.MatrixTower

end

end
end

end OAI
end


