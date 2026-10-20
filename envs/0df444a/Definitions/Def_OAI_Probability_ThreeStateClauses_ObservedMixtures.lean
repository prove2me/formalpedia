-- Prove2me | Definitions.Def_OAI_Probability_ThreeStateClauses_ObservedMixtures
-- name    : OAI_Probability_ThreeStateClauses_ObservedMixtures
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T19:55:25.878985+00:00
-- url     : https://prove2.me/theorems/949608a0-ef04-4078-b3bf-3efd703b5873
-- title:
--   Mixtures indexed by a random number of components
-- statement:
--   Let $(\alpha_n)_{n\in\mathbb{N}}$ be a family of types. Let $\rho$ be a discrete probability distribution on $\mathbb{N}$, and for each $n$ let $p_n$ be a discrete probability distribution on $\alpha_n$. The mixture law on pairs $(n,a)$ with $a\in\alpha_n$ has mass
--   $$
--   P(n,a)=\rho(n)\,p_n(a).
--   $$
--   It is the law of first drawing $n\sim\rho$ and then $a\sim p_n$.
--
--   If every $\alpha_n$ is countable with measurable singletons, then singletons of the type of pairs $(n,a)$ are measurable as well.
--
--   This models a vertex with a random number $n$ of children, followed by an $n$-tuple of child observations. It is the ordered form of the Galton–Watson observation law.
--
--   **Formalization Note** `sigmaPMF ρ p` is a probability mass function on the dependent pair type `Sigma α`. The instance `sigmaMeasurableSingleton` provides the measurability of singletons.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ThreeStateClauses/ObservedMixtures.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/ThreeStateClauses/ObservedMixtures.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the ThreeStateTreeClauses mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_ThreeStateTreeClauses
import Definitions.Def_OAI_Probability_ThreeStateClauses_RadialAlgebra
import Definitions.Def_OAI_Probability_ThreeStateClauses_PosteriorLaw
import Definitions.Def_OAI_Probability_ThreeStateClauses_DiscreteLaw
import Definitions.Def_OAI_Probability_ThreeStateClauses_Products
import Definitions.Def_OAI_Probability_ThreeStateClauses_Degradation
import Definitions.Def_OAI_Probability_ThreeStateClauses_RegularLaw
import Definitions.Def_OAI_Probability_ThreeStateClauses_BranchMoments
import Definitions.Def_OAI_Probability_ThreeStateClauses_CompactLimits
import Definitions.Def_OAI_Probability_ThreeStateClauses_RegularStatistics
import Definitions.Def_OAI_Probability_ThreeStateClauses_InformationLoss
import Definitions.Def_OAI_Probability_ThreeStateClauses_RegularReconstruction

namespace OAI

/-! Observed Mixtures. -/

open scoped BigOperators ENNReal NNReal Topology
open Filter
noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology
namespace ThreeState.TreeClauses.Experiment
-- [generator] trimmed: open ThreeState.TreeClauses.Radial ThreeState.TreeClauses.Positive
open ThreeState.TreeClauses.Radial

variable {X : Type*} [MeasurableSpace X]

variable [TopologicalSpace X] [CompactSpace X] [BorelSpace X]

end ThreeState.TreeClauses.Experiment

end 

noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal
namespace ThreeState.TreeClauses.Experiment
-- [generator] trimmed: open ThreeState.TreeClauses.Radial ThreeState.TreeClauses.Positive
open ThreeState.TreeClauses.Radial

variable {α : ℕ → Type*}

def sigmaPMF (ρ : PMF ℕ) (p : ∀ n, PMF (α n)) : PMF (Sigma α) :=
  ⟨fun z ↦ ρ z.1*p z.1 z.2, ENNReal.summable.hasSum_iff.2 (by
    rw [ENNReal.tsum_sigma']
    simp only [ENNReal.tsum_mul_left]
    have hs (n : ℕ) : (∑' a, p n a) = 1 := (p n).tsum_coe
    simp only [hs, mul_one]
    exact ρ.tsum_coe)⟩

@[simp] lemma sigmaPMF_apply (ρ : PMF ℕ) (p : ∀ n, PMF (α n)) (n : ℕ) (a : α n) :
    sigmaPMF ρ p ⟨n,a⟩ = ρ n*p n a := rfl

section Measures
variable [∀ n, Countable (α n)] [∀ n, MeasurableSpace (α n)]
  [∀ n, MeasurableSingletonClass (α n)]

instance sigmaMeasurableSingleton : MeasurableSingletonClass (Sigma α) := by
  constructor
  intro z
  apply MeasurableSpace.measurableSet_iInf.mpr
  intro n
  change MeasurableSet ((Sigma.mk n) ⁻¹' {z})
  exact Set.Countable.measurableSet (Set.to_countable _)

end Measures
end ThreeState.TreeClauses.Experiment

end

end OAI


