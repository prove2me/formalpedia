-- Prove2me | Definitions.Def_OAIQWSQN005
-- name    : OAIQWSQN005
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-18T21:02:35.078721+00:00
-- url     : https://prove2.me/theorems/01a994ad-f169-4516-a742-13d908bd3409
-- title:
--   OpenAI separable quotient split: definitions bundle OAIQWSQN005
-- statement:
--   One of the definitions bundles of the split of OpenAI's proof of `OAI.SeparableQuotient.negative_main`. Under the continuum hypothesis, neither the real nor the complex separable quotient assertion holds. The bundle holds OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Analysis/SeparableQuotients` (OpenAI, *Relative independence of the separable quotient problem*, OpenAI Math Release, September 23, 2026, result family 323, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a. It also holds the lemmas these definitions use in their bodies, and OpenAI's `@[simp]` lemmas about them. Each module section starts by removing the instances `SubfieldClass.toSubringClass` and `SubringClass.toSubsemiringClass` locally, which speeds up instance search and changes nothing that is proved.
--
--   The definitions of the published statement (`CH`, `HasSeparableQuotient`, `SQ`) come from the published bundle `Def_SeparableQuotientNegative`. It also imports the bundles `OAIQWSQN002`, `OAIQWSQN003` of this split.
--
--   Modules: `PerturbationOperator`, `PrefixNormers`.
-- source:
--   OpenAI, Relative independence of the separable quotient problem, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 323; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Relative-independence-of-the-separable-quotient-problem-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis/SeparableQuotients at commit adc7f12

import Mathlib
import Definitions.Def_OAIQWSQN002
import Definitions.Def_OAIQWSQN003

section
-- module Solutions.OAIQW_SeparableQuotient.PrefixNormers
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] SubfieldClass.toSubringClass SubringClass.toSubsemiringClass

namespace OAI

namespace SeparableQuotient
open Set Metric
open scoped BigOperators Topology
universe u
variable {𝕜 : Type} [RCLike 𝕜]
variable {X : Type u} [NormedAddCommGroup X] [NormedSpace 𝕜 X]

namespace PrefixNormers

attribute [local instance] OAI.SeparableQuotient.prefixDualNormedGroup
attribute [local instance] OAI.SeparableQuotient.prefixDualNormedSpace
variable {f : ℕ → StrongDual 𝕜 X} (H : PrefixNormers f)

include H

/-- Bounded algebraic coordinate functionals. -/
noncomputable def spanCoord (a : ℝ) (ha : 0 < a) (hf : ∀ n, a ≤ ‖f n‖) (n : ℕ) :
    StrongDual 𝕜 (Submodule.span 𝕜 (Set.range f)) :=
  LinearMap.mkContinuous ((Finsupp.lapply (R := 𝕜) (M := 𝕜) n).comp (H.linearIndependent a ha hf).repr)
    (4 / a) (fun x => by
      have h := H.finsupp_coefficient_bound a ha hf
        ((H.linearIndependent a ha hf).repr x) n
      rw [LinearIndependent.linearCombination_repr] at h
      exact h)

theorem spanCoord_norm (a : ℝ) (ha : 0 < a) (hf : ∀ n, a ≤ ‖f n‖) (n : ℕ) :
    ‖H.spanCoord a ha hf n‖ ≤ 4 / a := by
  apply LinearMap.mkContinuous_norm_le
  exact div_nonneg (by norm_num) ha.le

/-- Hahn--Banach extension of each coordinate; restrictions to the closed span are canonical. -/
theorem exists_ambientCoord (a : ℝ) (ha : 0 < a) (hf : ∀ n, a ≤ ‖f n‖) :
    ∃ e : ℕ → StrongDual 𝕜 (StrongDual 𝕜 X),
      (∀ n, ‖e n‖ ≤ 4 / a) ∧ (∀ n, ∀ x : Submodule.span 𝕜 (Set.range f),
        e n x = H.spanCoord a ha hf n x) := by
  have he (n : ℕ) := exists_extension_norm_eq (Submodule.span 𝕜 (Set.range f))
    (H.spanCoord a ha hf n)
  choose e he hnorm using he
  exact ⟨e, fun n => (hnorm n).trans_le (H.spanCoord_norm a ha hf n), he⟩

noncomputable def ambientCoord (a : ℝ) (ha : 0 < a) (hf : ∀ n, a ≤ ‖f n‖) :
    ℕ → StrongDual 𝕜 (StrongDual 𝕜 X) :=
  Classical.choose (H.exists_ambientCoord a ha hf)

noncomputable def coord (a : ℝ) (ha : 0 < a) (hf : ∀ n, a ≤ ‖f n‖) (n : ℕ) :
    StrongDual 𝕜 (closedSpan f) :=
  (H.ambientCoord a ha hf n).comp (closedSpan f).subtypeL

attribute [local instance] OAI.SeparableQuotient.PrefixNormers.closedDualNormedGroup
attribute [local instance] OAI.SeparableQuotient.PrefixNormers.closedDualNormedSpace
/-- The coefficient vectors used in the adjoint bound. -/
noncomputable def adjointVector (a : ℝ) (ha : 0 < a) (hf : ∀ n, a ≤ ‖f n‖)
    (h : StrongDual 𝕜 (StrongDual 𝕜 (closedSpan f))) (m : ℕ) : closedSpan f :=
  ∑ i ∈ Finset.range m, h (H.coord a ha hf i) • basisVector f i

/-- The closed coefficient span `Z`. -/
noncomputable def coefficientSpan (a : ℝ) (ha : 0 < a) (hf : ∀ n, a ≤ ‖f n‖) :
    Submodule 𝕜 (StrongDual 𝕜 (closedSpan f)) :=
  (Submodule.span 𝕜 (Set.range (H.coord a ha hf))).topologicalClosure

/-- Evaluation with codomain the closed coefficient span. -/
noncomputable def evaluationToZ (a : ℝ) (ha : 0 < a) (hf : ∀ n, a ≤ ‖f n‖)
    (hZ : ∀ x, evaluation f x ∈ H.coefficientSpan a ha hf) :
    X →L[𝕜] H.coefficientSpan a ha hf :=
  (evaluation f).codRestrict (H.coefficientSpan a ha hf) hZ

noncomputable def coefficientVector (a : ℝ) (ha : 0 < a) (hf : ∀ n, a ≤ ‖f n‖)
    (n : ℕ) : H.coefficientSpan a ha hf :=
  ⟨H.coord a ha hf n, Submodule.le_topologicalClosure _
    (Submodule.subset_span (Set.mem_range_self n))⟩

end PrefixNormers
end SeparableQuotient

end OAI
end

section
-- module Solutions.OAIQW_SeparableQuotient.PerturbationOperator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] SubfieldClass.toSubringClass SubringClass.toSubsemiringClass

namespace OAI

noncomputable section

namespace SeparableQuotient.ActualSpace

open Norming NormConstruction PathCoding Filter
open scoped Classical Topology

attribute [local instance] OAI.SeparableQuotient.ActualSpace.opDualGroup
attribute [local instance] OAI.SeparableQuotient.ActualSpace.opDualSpace
attribute [local instance] OAI.SeparableQuotient.ActualSpace.opXClosed
attribute [local instance] OAI.SeparableQuotient.ActualSpace.opWGroup
attribute [local instance] OAI.SeparableQuotient.ActualSpace.opWSpace
attribute [local instance] OAI.SeparableQuotient.ActualSpace.opWT2
variable (hCH : Cardinal.mk ℝ = Cardinal.aleph 1)

lemma norm_B_le : ‖B hCH‖ ≤ 1/10 := by
  have hb : ‖B hCH‖ ≤ 1/16 := by
    apply tsum_of_norm_bounded tau_hasSum
    intro n
    rw [norm_smul,Real.norm_of_nonneg (tau_pos n).le]
    exact mul_le_of_le_one_right (tau_pos n).le (norm_familyOperator_le hCH _)
  linarith

end SeparableQuotient.ActualSpace

end

end OAI
end


