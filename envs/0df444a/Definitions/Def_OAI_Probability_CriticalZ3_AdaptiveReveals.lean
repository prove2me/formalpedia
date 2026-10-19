-- Prove2me | Definitions.Def_OAI_Probability_CriticalZ3_AdaptiveReveals
-- name    : OAI_Probability_CriticalZ3_AdaptiveReveals
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T18:31:45.821217+00:00
-- url     : https://prove2.me/theorems/2d5bcafd-87d7-43cb-a88a-6bccc35a7eec
-- title:
--   Adaptive revealing schemes and revealed histories
-- statement:
--   An abstract framework for exploring a product Bernoulli configuration by adaptively revealing finitely many bits.
--
--   1. **Schemes.** A scheme has states $s$. Each state reveals a finite set of bits under a current parameter field, optionally visits a vertex, and given the revealed values declares that vertex bad or not and moves to a child state. The child's parameters fix the revealed bits to their values.
--   2. **Weights.** The weight of revealed values $a$ is the probability of the corresponding cylinder, and the bad mass of $s$ is the total weight of values declared bad.
--   3. **Hitting.** The event that a set $U$ of vertices is hit within $n$ steps says that each $v\in U$ is visited and declared bad at its first visit; visited vertices are removed from $U$.
--   4. **Histories.** A history records known bits and their values. Its parameter field fixes known bits and uses $q$ elsewhere; observing new bits $R$ merges them in, and freezing replaces the known bits of a configuration:
--   $$
--   \mathrm{param}(\mathrm{observe}(h,R,\omega))=\mathrm{fix}(\mathrm{param}(h),R,\omega).
--   $$
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/CriticalZ3/AdaptiveReveals.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/CriticalZ3/AdaptiveReveals.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the CriticalZ3 mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_CriticalZ3
import Definitions.Def_OAI_Probability_CriticalZ3_Basic
import Definitions.Def_OAI_Probability_CriticalZ3_ProductCylinder
import Definitions.Def_OAI_Probability_CriticalZ3_Symmetry
import Definitions.Def_OAI_Probability_CriticalZ3_QuarterFaces
import Definitions.Def_OAI_Probability_CriticalZ3_Resampling
import Definitions.Def_OAI_Probability_CriticalZ3_HyperedgeComparison
import Definitions.Def_OAI_Probability_CriticalZ3_LatticeGraph
import Definitions.Def_OAI_Probability_CriticalZ3_BoxGeometry
import Definitions.Def_OAI_Probability_CriticalZ3_LatticePaths
import Definitions.Def_OAI_Probability_CriticalZ3_EntryLayers
import Definitions.Def_OAI_Probability_CriticalZ3_SeedTrials
import Definitions.Def_OAI_Probability_CriticalZ3_Conditioning
import Definitions.Def_OAI_Probability_CriticalZ3_ConditionalQuality
import Definitions.Def_OAI_Probability_CriticalZ3_TrialCounts
import Definitions.Def_OAI_Probability_CriticalZ3_ShellProbability
import Definitions.Def_OAI_Probability_CriticalZ3_SeedQuality
import Definitions.Def_OAI_Probability_CriticalZ3_Scales
import Definitions.Def_OAI_Probability_CriticalZ3_Relay
import Definitions.Def_OAI_Probability_CriticalZ3_RelayProbability
import Definitions.Def_OAI_Probability_CriticalZ3_FiniteTrails
import Definitions.Def_OAI_Probability_CriticalZ3_PlanarBoundary
import Definitions.Def_OAI_Probability_CriticalZ3_Matching
import Definitions.Def_OAI_Probability_CriticalZ3_Peierls
import Definitions.Def_OAI_Probability_CriticalZ3_Coarse

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uF

-- [generator] trimmed: open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical Filter Topology Function
open _root_.MeasureTheory ProbabilityTheory Classical Filter Topology Function

open scoped ENNReal BigOperators Matrix

namespace AdaptiveReveals
-- [generator] trimmed: open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical
open _root_.MeasureTheory ProbabilityTheory Classical
open InfiniteConditioning
variable {E V S : Type} [Countable E] [DecidableEq V]

structure Scheme (E V S : Type) where
  reveal : S → Finset E
  parameter : S → E → Set.Icc (0 : ℝ) 1
  vertex : S → Option V
  bad : (s : S) → (reveal s → Bool) → Bool
  child : (s : S) → (reveal s → Bool) → S
  parameter_child : ∀ s a, parameter (child s a) =
    fixedParameter (parameter s) (reveal s) (ProductCylinder.extend (reveal s) a)

namespace Scheme
variable (P : Scheme E V S)

noncomputable def weight (s : S) (a : P.reveal s → Bool) : ℝ :=
  (ProductCylinder.law (P.parameter s)).real
    (pattern (P.reveal s) (ProductCylinder.extend (P.reveal s) a))

noncomputable def badMass (s : S) : ℝ :=
  ∑ a : P.reveal s → Bool, if P.bad s a = true then P.weight s a else 0

/-- Every target must first be tested by the time limit, and its first test
must have declared it bad.  Removing it prevents multiple visits from ever
being counted as distinct successes in this estimate. -/
noncomputable def hit : ℕ → S → Finset V → Set (E → Bool)
  | 0, _, U => if U = ∅ then Set.univ else ∅
  | n+1, s, U => match P.vertex s with
    | none => if U = ∅ then Set.univ else ∅
    | some v => {ω | (v ∈ U → P.bad s ((P.reveal s).restrict ω) = true) ∧
        ω ∈ hit n (P.child s ((P.reveal s).restrict ω)) (U.erase v)}

end Scheme
end AdaptiveReveals

namespace InfiniteConditioning
-- [generator] trimmed: open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical
open _root_.MeasureTheory ProbabilityTheory Classical
variable {E : Type} [Countable E]

omit [Countable E] in
theorem fixedParameter_merge (p : E → Set.Icc (0:ℝ) 1) (J K : Finset E)
    (ξ ω : E → Bool) : fixedParameter (fixedParameter p J ξ) K ω =
      fixedParameter p (J ∪ K) (replace K ω ξ) := by
  funext e
  by_cases hK : e ∈ K <;> by_cases hJ : e ∈ J <;>
    simp [fixedParameter,replace,hK,hJ]

structure History (E : Type) where
  known : Finset E
  values : E → Bool

namespace History
noncomputable def parameter (h : History E) (q : Set.Icc (0:ℝ) 1) :=
  fixedParameter (fun _ => q) h.known h.values
noncomputable def observe (h : History E) (R : Finset E) (ω : E → Bool) : History E :=
  ⟨h.known ∪ R,replace R ω h.values⟩
noncomputable def freeze (h : History E) (ω : E → Bool) := replace h.known h.values ω

omit [Countable E] in
theorem parameter_observe (h : History E) (q : Set.Icc (0:ℝ) 1) (R : Finset E) (ω : E → Bool) :
    (h.observe R ω).parameter q = fixedParameter (h.parameter q) R ω :=
  (fixedParameter_merge _ _ _ _ _).symm

end History
end InfiniteConditioning

end OAI


