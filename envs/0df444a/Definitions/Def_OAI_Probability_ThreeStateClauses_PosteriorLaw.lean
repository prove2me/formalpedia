-- Prove2me | Definitions.Def_OAI_Probability_ThreeStateClauses_PosteriorLaw
-- name    : OAI_Probability_ThreeStateClauses_PosteriorLaw
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T19:40:49.079935+00:00
-- url     : https://prove2.me/theorems/581b371b-6102-4189-9ed2-31adc3504d87
-- title:
--   The compact simplex of three-spin likelihood messages
-- statement:
--   The message set is
--   $$
--   \mathcal M=\Bigl\{m\in\mathbb{R}^3:\ m_i\ge0\ (i=0,1,2),\ \ \frac{m_0+m_1+m_2}{3}=1\Bigr\}.
--   $$
--   A message is the likelihood ratio of a posterior distribution on three spins to the uniform distribution: $m_i/3$ is the posterior probability of spin $i$. The file establishes the following.
--
--   1. Every coordinate of a message satisfies $m_i\le3$.
--   2. The average map $\mathbb{R}^3\to\mathbb{R}$ is continuous.
--   3. $\mathcal M$ is closed and compact. Hence the subtype of messages is a compact space.
--
--   Compactness of $\mathcal M$ makes the space of probability laws of messages compact, so sequences of posterior laws have convergent subsequences.
--
--   **Formalization Note** `Message` is the subtype of `messageSet : Set (Fin 3 → ℝ)`, and the `CompactSpace Message` instance is derived from `isCompact_messageSet`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ThreeStateClauses/PosteriorLaw.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/ThreeStateClauses/PosteriorLaw.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the ThreeStateTreeClauses mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_ThreeStateTreeClauses
import Definitions.Def_OAI_Probability_ThreeStateClauses_RadialAlgebra

namespace OAI

/-! Posterior Law. -/

open scoped BigOperators ENNReal NNReal Topology
open Filter
noncomputable section
open Set MeasureTheory
namespace ThreeState.TreeClauses.Experiment
-- [generator] trimmed: open Radial ThreeState.TreeClauses.Positive
open Radial

def messageSet : Set Vec := {m | (∀ i, 0 ≤ m i) ∧ avg m = 1}
abbrev Message := messageSet

lemma coordinate_le_three (m : Message) (i : Fin 3) : m.1 i ≤ 3 := by
  have hs := m.2.2
  dsimp only [avg] at hs
  have h₀ := m.2.1 0
  have h₁ := m.2.1 1
  have h₂ := m.2.1 2
  fin_cases i <;> dsimp at * <;> linarith

lemma continuous_avg : Continuous (avg : Vec → ℝ) :=
  (((continuous_apply 0).add (continuous_apply 1)).add (continuous_apply 2)).div_const 3

lemma isClosed_messageSet : IsClosed messageSet := by
  have h : IsClosed {m : Vec | ∀ i, 0 ≤ m i} := by
    simp only [ofPred_forall]
    exact isClosed_iInter (fun i ↦ isClosed_le continuous_const (continuous_apply i))
  exact h.inter (isClosed_eq continuous_avg continuous_const)

lemma isCompact_messageSet : IsCompact messageSet :=
  (isCompact_Icc (a := fun _ : Fin 3 ↦ (0:ℝ)) (b := fun _ : Fin 3 ↦ (3:ℝ))).of_isClosed_subset
    isClosed_messageSet (fun m hm ↦ ⟨hm.1, fun i ↦ coordinate_le_three ⟨m, hm⟩ i⟩)

instance : CompactSpace Message := isCompact_iff_compactSpace.mp isCompact_messageSet

end ThreeState.TreeClauses.Experiment

end 

noncomputable section
open Set MeasureTheory
namespace ThreeState.TreeClauses.Experiment
-- [generator] trimmed: open ThreeState.TreeClauses.Radial ThreeState.TreeClauses.Positive
open ThreeState.TreeClauses.Radial

end ThreeState.TreeClauses.Experiment

end 

noncomputable section
open Set MeasureTheory
namespace ThreeState.TreeClauses.Experiment
-- [generator] trimmed: open ThreeState.TreeClauses.Radial ThreeState.TreeClauses.Positive
open ThreeState.TreeClauses.Radial

end ThreeState.TreeClauses.Experiment

end

end OAI


