-- Prove2me | Definitions.Def_OAIQ242Bal004
-- name    : OAIQ242Bal004
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T23:45:21.515066+00:00
-- url     : https://prove2.me/theorems/cd4b4582-8115-4efb-8b91-fe62dd5b9db1
-- title:
--   Definitions bundle OAIQ242Bal004 of the split of OpenAI, Directional transience implies ballisticity
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.DirectionalTransience.directional_transience_implies_ballisticity`, carved from OpenAI's openai/math development (OpenAI, *Directional transience implies ballisticity*, OpenAI Math Release, September 23, 2026, result family 220, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 5 declarations of OpenAI's Lean: 3 definitions, 1 instance and 1 theorem. The definitions and types are `OAI.DirectionalTransience.upwardHitWord`, `OAI.DirectionalTransience.variablePairHitKernel`, `OAI.DirectionalTransience.wordTrace`.
--
--   **Sources.** They come from these modules of lean/OAI/Probability, in whole or in part: [`Ballisticity_Crossings_HitWord`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/Ballisticity/Crossings/HitWord.lean), [`Ballisticity_Estimates_BudgetAdapted`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/Ballisticity/Estimates/BudgetAdapted.lean), [`Ballisticity_Estimates_RawPairLocality`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/Ballisticity/Estimates/RawPairLocality.lean).
--
--   **Imports.** It imports the published bundle `Def_DirectionalBallisticity`; the bundle `OAIQ242Bal000` of this split.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.DirectionalTransience.EpisodeChainLedger.mean_episode_drops_local`, `OAI.DirectionalTransience.OperationalConstants.bad_limit_drop_moment`, `OAI.DirectionalTransience.OperationalConstants.raw_dropCut_upper`, `OAI.DirectionalTransience.actual_finite_stage_estimate`, `OAI.DirectionalTransience.actual_late_protection_first_failure`, `OAI.DirectionalTransience.actual_profile_tail_decorrelation` and `OAI.DirectionalTransience.off_diagonal_comparison`.
-- source:
--   OpenAI, Directional transience implies ballisticity, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 220; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Directional-transience-implies-ballisticity-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Probability at commit adc7f12

import Mathlib
import Definitions.Def_DirectionalBallisticity
import Definitions.Def_OAIQ242Bal000

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Crossings_HitWord
attribute [-instance] _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Pointwise Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Pointwise Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

def wordTrace {d : ℕ} (x : Lattice d) (w : List (Direction d)) : Set (Lattice d) :=
  {z | ∃ j ≤ w.length, wordPath x w j = z}

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_RawPairLocality
attribute [-instance] _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

noncomputable def variablePairHitKernel {d : ℕ} (ℓ : Vector d) (H : ℕ) :
    Kernel (Environment d × (Lattice d × Lattice d)) (Lattice d × Lattice d) :=
  ((variableHitKernel ℓ H).comap (fun p => (p.1,p.2.1)) (by fun_prop)).prod
    ((variableHitKernel ℓ H).comap (fun p => (p.1,p.2.2)) (by fun_prop))

instance variablePairHitKernel_finite {d : ℕ} (ℓ : Vector d) (H : ℕ) :
    IsFiniteKernel (variablePairHitKernel ℓ H) := by unfold variablePairHitKernel; infer_instance

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_BudgetAdapted
attribute [-instance] _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma upwardWord_successful {d : ℕ} (e : Direction d) (x : Lattice d) :
    wordPath x [e] ∈ HitAt (Strip (realPosition (step e)) x (1:ℕ))
      (Upper (realPosition (step e)) x (1:ℕ)) [e].length := by
  constructor
  · change dot (realPosition x) (realPosition (step e)) + (1:ℕ) ≤
      dot (realPosition (x+step e)) (realPosition (step e))
    simp only [dot_signed_direction,signedCoordinate_add,signedCoordinate_step_self,Nat.cast_one,le_refl]
  · intro n hn
    have : n=0 := by simpa using hn
    subst n
    change dot (realPosition x) (realPosition (step e)) ≤ dot (realPosition x) (realPosition (step e)) ∧
      dot (realPosition x) (realPosition (step e)) < dot (realPosition x) (realPosition (step e))+(1:ℕ)
    constructor <;> simp

def upwardHitWord {d : ℕ} (e : Direction d) (x : Lattice d) :
    HitWord x (Strip (realPosition (step e)) x (1:ℕ)) (Upper (realPosition (step e)) x (1:ℕ)) :=
  ⟨[e],upwardWord_successful e x⟩

end DirectionalTransience

end

end OAI
end


