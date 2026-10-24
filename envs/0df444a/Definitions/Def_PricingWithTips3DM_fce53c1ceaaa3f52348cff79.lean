-- Prove2me | Definitions.Def_PricingWithTips3DM_fce53c1ceaaa3f52348cff79
-- name    : PricingWithTips3DM_fce53c1ceaaa3f52348cff79
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-22T21:38:27.093871+00:00
-- url     : https://prove2.me/theorems/dbeca20d-6c5e-4d00-af21-801bec7ee8f5
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.OccurrenceReduction.Machine.CompatibilityEdgesCompare
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_55d7fe6eefa08b3d18d1fe6f
import Mathlib.Tactic
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-!
# Occurrence compatibility edges: total unary comparison interfaces

The low-level clause and variable controllers have distinct traces for the
three possible size relations.  This file packages each family as one total
comparison theorem with a common linear time bound.
-/

noncomputable section

open StateTransition

namespace CLRS
namespace Chapter34
namespace Turing
namespace TMClique

open PolyBuilder

/-- Uniform budget for either restored unary comparison. -/
def compatibilityEdgesComparisonSteps (prior current : Nat) : Nat :=
  6 * (prior + current + 1)

private def evalsToInTime_weaken {state : Type}
    {transition : state → Option state} {start : state}
    {finish : Option state} {small large : Nat}
    (run : EvalsToInTime transition start finish small)
    (hbound : small ≤ large) :
    EvalsToInTime transition start finish large :=
  ⟨run.toEvalsTo, run.steps_le_m.trans hbound⟩

/-- Total clause comparison: the Boolean state records equality, the test bit
records the strict `prior < current` branch, and counter two is restored. -/
def compatibilityEdges_priorClauseComparisonRun
    (currentPolarity : Bool) (prior current : Nat)
    (tail work₂ : List UnaryFrameSym) (output : List CliqueSym)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (upper variableCode : Nat) :
    EvalsToInTime (step compatibilityEdgesProgram)
      (compatibilityEdgesCfg (.priorClause currentPolarity false)
        buffer₁ buffer₂ test [] output
        (List.replicate prior .tick ++ .separator :: tail) work₂
        upper current variableCode)
      (some (compatibilityEdgesCfg
        (.priorPolarity currentPolarity (decide (prior = current)))
        (some .separator) none (decide (prior < current)) [] output tail
        (.separator :: List.replicate prior .tick ++ work₂)
        upper current variableCode))
      (compatibilityEdgesComparisonSteps prior current) := by
  by_cases hlt : prior < current
  · let excess := current - prior - 1
    have hcurrent : current = prior + excess + 1 := by
      dsimp [excess]
      omega
    have run := compatibilityEdges_priorClauseLtRun currentPolarity prior
      excess tail work₂ output buffer₁ buffer₂ test upper variableCode
    have hne : prior ≠ prior + excess + 1 := by omega
    refine evalsToInTime_weaken (small := 4 * prior + 6) (large :=
      compatibilityEdgesComparisonSteps prior current) ?_ ?_
    · simpa [hcurrent, hlt, hne] using run
    · simp [compatibilityEdgesComparisonSteps]
      omega
  · by_cases heq : prior = current
    · subst current
      have run := compatibilityEdges_priorClauseEqRun currentPolarity prior
        tail work₂ output buffer₁ buffer₂ test upper variableCode
      refine evalsToInTime_weaken (small := 4 * prior + 5) (large :=
        compatibilityEdgesComparisonSteps prior prior) ?_ ?_
      · simpa using run
      · simp [compatibilityEdgesComparisonSteps]
        omega
    · have hgt : current < prior := by omega
      let excess := prior - current - 1
      have hprior : prior = current + excess + 1 := by
        dsimp [excess]
        omega
      have run := compatibilityEdges_priorClauseGtRun currentPolarity current
        excess tail work₂ output buffer₁ buffer₂ test upper variableCode
      have hne : current + excess + 1 ≠ current := by omega
      have hnlt : ¬ current + excess + 1 < current := by omega
      refine evalsToInTime_weaken
        (small := 4 * current + 2 * (excess + 1) + 5) (large :=
        compatibilityEdgesComparisonSteps prior current) ?_ ?_
      · simpa [hprior, hne, hnlt] using run
      · simp [compatibilityEdgesComparisonSteps]
        omega

/-- Total variable comparison: the previous clause and polarity decisions are
preserved, the equality Boolean is appended, and counter three is restored. -/
def compatibilityEdges_priorVariableComparisonRun
    (currentPolarity clauseEqual priorPolarity : Bool)
    (prior current : Nat)
    (tail work₂ : List UnaryFrameSym) (output : List CliqueSym)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (upper clause : Nat) :
    EvalsToInTime (step compatibilityEdgesProgram)
      (compatibilityEdgesVariableCfg
        (.priorVariable currentPolarity clauseEqual priorPolarity false)
        buffer₁ buffer₂ test [] output
        (List.replicate prior .tick ++ .separator :: tail) work₂
        upper current clause)
      (some (compatibilityEdgesVariableCfg
        (.priorEnd currentPolarity clauseEqual priorPolarity
          (decide (prior = current)))
        (some .separator) none (decide (prior < current)) [] output tail
        (.separator :: List.replicate prior .tick ++ work₂)
        upper current clause))
      (compatibilityEdgesComparisonSteps prior current) := by
  by_cases hlt : prior < current
  · let excess := current - prior - 1
    have hcurrent : current = prior + excess + 1 := by
      dsimp [excess]
      omega
    have run := compatibilityEdges_priorVariableLtRun currentPolarity
      clauseEqual priorPolarity prior excess tail work₂ output
      buffer₁ buffer₂ test upper clause
    have hne : prior ≠ prior + excess + 1 := by omega
    refine evalsToInTime_weaken (small := 4 * prior + 6) (large :=
      compatibilityEdgesComparisonSteps prior current) ?_ ?_
    · simpa [hcurrent, hlt, hne] using run
    · simp [compatibilityEdgesComparisonSteps]
      omega
  · by_cases heq : prior = current
    · subst current
      have run := compatibilityEdges_priorVariableEqRun currentPolarity
        clauseEqual priorPolarity prior tail work₂ output buffer₁ buffer₂
        test upper clause
      refine evalsToInTime_weaken (small := 4 * prior + 5) (large :=
        compatibilityEdgesComparisonSteps prior prior) ?_ ?_
      · simpa using run
      · simp [compatibilityEdgesComparisonSteps]
        omega
    · have hgt : current < prior := by omega
      let excess := prior - current - 1
      have hprior : prior = current + excess + 1 := by
        dsimp [excess]
        omega
      have run := compatibilityEdges_priorVariableGtRun currentPolarity
        clauseEqual priorPolarity current excess tail work₂ output
        buffer₁ buffer₂ test upper clause
      have hne : current + excess + 1 ≠ current := by omega
      have hnlt : ¬ current + excess + 1 < current := by omega
      refine evalsToInTime_weaken
        (small := 4 * current + 2 * (excess + 1) + 5) (large :=
        compatibilityEdgesComparisonSteps prior current) ?_ ?_
      · simpa [hprior, hne, hnlt] using run
      · simp [compatibilityEdgesComparisonSteps]
        omega

end TMClique
end Turing
end Chapter34
end CLRS


