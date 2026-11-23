-- Prove2me | Definitions.Def_NonuniformCompetitive_Snoopy_Supplement_phaseLP
-- name    : NonuniformCompetitive_Snoopy_Supplement_phaseLP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T11:52:51.185258+00:00
-- url     : https://prove2.me/theorems/86655864-2857-4f8a-8bf2-20964a0f344d
-- title:
--   Actual phase costs, feasible potential inequalities and an attained LP bound
-- statement:
--   A complete phase $\rho$ carries its request word, starting state $s$ and ending state $t$. Validity requires a nonempty word, the work-function known-state criterion at its end, and finite positive optimal cost. A family of actual randomized causal task policies is initialized at the corresponding start states.
--
--   For a real factor $\alpha$ and real state potentials $\Phi$, the phase inequalities are
--   $$\mathbf E C_A(\rho)\le \alpha C_{opt}(\rho)+\Phi_s-\Phi_t.$$
--   An LP bound is an attained feasible value no greater than any other feasible value. No empty or unbounded real infimum is assigned a default value, and no probability box constraints are introduced.
--
--   These are the local LP definitions. They do not assert a causal global phase decomposition, filtering, forgetting, or the upper- or lower-bound theorems; those interfaces remain unfinished.
-- source:
--   Karlin, Manasse, McGeoch, Owicki, Competitive Randomized Algorithms for Nonuniform Problems, Algorithmica 11 (1994), DOI 10.1007/BF01189993, §2, pp. 546–549

import Mathlib
import Definitions.Def_NonuniformCompetitive_Snoopy_Supplement_taskSystem

namespace NonuniformCompetitive.Snoopy.Supplement

open scoped NNReal ENNReal

/-- A phase descriptor, not yet a global phase decomposition. A valid descriptor
contains its actual task word and both known endpoint states. -/
structure TaskPhase (S R : Type) where
  start : S
  finish : S
  word : List R

/-- The local source conditions on a complete phase. Global reachability,
causal decomposition and the filtering property remain separate obligations. -/
def TaskPhase.Valid {S R : Type} (T : TaskSystem S R) (ρ : TaskPhase S R) : Prop :=
  ρ.word ≠ [] ∧ TaskRawKnown T ρ.start ρ.word ρ.finish ∧
    0 < taskOpt T ρ.start ρ.word ∧ taskOpt T ρ.start ρ.word ≠ ⊤

/-- The actual phase LP, using costs of causal mixed strategies initialized in
each start state. Potentials have the source sign start minus finish. There are
no artificial box constraints on probabilities, α or potentials. -/
def PhaseLPFeasible {S R P : Type} (T : TaskSystem S R)
    (phases : P → TaskPhase S R) (policy : S → TaskRandomized T)
    (α : ℝ) (Φ : S → ℝ) : Prop :=
  (∀ q : P, TaskPhase.Valid T (phases q)) ∧
  (∀ (s : S) (i : (policy s).ι), ((policy s).alg i).after [] = s) ∧
  ∀ q : P, (policy (phases q).start).expCost (phases q).word ≤
    ENNReal.ofReal (α * (taskOpt T (phases q).start (phases q).word).toReal +
      Φ (phases q).start - Φ (phases q).finish)

/-- An attained finite minimum, not the default of real sInf on an empty or
unbounded feasible set. This only defines the bound; it does not assume any
competitive consequence or any reduction of general algorithms to phase policies. -/
def IsPhaseLPBound {S R P : Type} (T : TaskSystem S R)
    (phases : P → TaskPhase S R) (policy : S → TaskRandomized T) (α : ℝ) : Prop :=
  (∃ Φ : S → ℝ, PhaseLPFeasible T phases policy α Φ) ∧
    ∀ (β : ℝ) (Ψ : S → ℝ), PhaseLPFeasible T phases policy β Ψ → α ≤ β

end NonuniformCompetitive.Snoopy.Supplement


