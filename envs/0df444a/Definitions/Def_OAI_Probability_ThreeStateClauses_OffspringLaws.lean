-- Prove2me | Definitions.Def_OAI_Probability_ThreeStateClauses_OffspringLaws
-- name    : OAI_Probability_ThreeStateClauses_OffspringLaws
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T19:57:36.776043+00:00
-- url     : https://prove2.me/theorems/6d6a0745-17e1-40d8-a5d1-0f04b1518862
-- title:
--   Ordered observations of a Galton–Watson broadcast tree and their forgetful image
-- statement:
--   Spins are elements of $\{0,1,2\}$. A parameter $\lambda\in\mathbb{R}$ is admissible if $-\tfrac12\le\lambda\le1$; the channel $M_\lambda(i,\cdot)$ keeps the spin $i$ with probability $\tfrac{1+2\lambda}{3}$ and moves it to each other spin with probability $\tfrac{1-\lambda}{3}$.
--
--   1. **Ordered observations.** A depth-$0$ ordered observation is a spin. A depth-$(\ell+1)$ ordered observation is a pair $(n,v)$, where $n\in\mathbb{N}$ is the number of children and $v=(v_0,\dots,v_{n-1})$ is an ordered tuple of depth-$\ell$ ordered observations. These are countable types with the discrete $\sigma$-algebra.
--   2. **Ordered law.** For an offspring law $\rho$ on $\mathbb{N}$, $\mathcal O_0(i)$ is the point mass at $i$. To sample $\mathcal O_{\ell+1}(i)$, draw $n\sim\rho$, then $n$ independent copies of "child spin $j\sim M_\lambda(i,\cdot)$, then a depth-$\ell$ ordered observation from $\mathcal O_\ell(j)$".
--   3. **Forgetting the order.** The forgetful map is the identity on spins and sends $(n,v)$ to the multiset $\{\phi(v_0),\dots,\phi(v_{n-1})\}$ of the forgotten children.
--
--   The ordered law has a product structure that makes moment computations straightforward. Forgetting the order produces the unordered multiset observations in which the broadcast model is stated.
--
--   **Formalization Note** The type `OrderedObservation ℓ` is defined by recursion, using the dependent pair type `Σ n : ℕ, Fin n → OrderedObservation ℓ`. The law is `orderedLaw ρ lam hlam` and the forgetful map is `forgetOrdered ℓ`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ThreeStateClauses/OffspringLaws.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/ThreeStateClauses/OffspringLaws.lean by skeleton subtraction
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
import Definitions.Def_OAI_Probability_ThreeStateClauses_ObservedMixtures

namespace OAI

/-! Offspring Laws. -/

open scoped BigOperators ENNReal NNReal Topology
open Filter
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal
namespace ThreeState.TreeClauses.Tree
-- [generator] trimmed: open ThreeState.TreeClauses.Experiment ThreeState.TreeClauses.Radial ThreeState.TreeClauses.Positive
open ThreeState.TreeClauses.Experiment ThreeState.TreeClauses.Radial

@[reducible] def OrderedObservation : ℕ → Type
  | 0 => Spin
  | ℓ+1 => Σ n : ℕ, Fin n → OrderedObservation ℓ

instance orderedObservationCountable : (ℓ : ℕ) → Countable (OrderedObservation ℓ)
  | 0 => inferInstanceAs (Countable Spin)
  | ℓ+1 => letI := orderedObservationCountable ℓ
           inferInstanceAs (Countable (Σ n : ℕ, Fin n → OrderedObservation ℓ))

instance orderedObservationMeasurable : (ℓ : ℕ) → MeasurableSpace (OrderedObservation ℓ)
  | 0 => inferInstanceAs (MeasurableSpace Spin)
  | ℓ+1 => letI := orderedObservationMeasurable ℓ
           inferInstanceAs (MeasurableSpace (Σ n : ℕ, Fin n → OrderedObservation ℓ))

instance orderedObservationSingleton : (ℓ : ℕ) → MeasurableSingletonClass (OrderedObservation ℓ)
  | 0 => inferInstanceAs (MeasurableSingletonClass Spin)
  | ℓ+1 => letI := orderedObservationSingleton ℓ
           inferInstanceAs (MeasurableSingletonClass (Σ n : ℕ, Fin n → OrderedObservation ℓ))

def orderedLaw (ρ : PMF ℕ) (lam : ℝ) (hlam : Admissible lam) :
    (ℓ : ℕ) → Spin → PMF (OrderedObservation ℓ)
  | 0, i => PMF.pure i
  | ℓ+1, i => sigmaPMF ρ (fun n ↦ productPMF (fun _ : Fin n ↦
      (channel lam hlam i).bind (orderedLaw ρ lam hlam ℓ)))

def forgetOrdered : (ℓ : ℕ) → OrderedObservation ℓ → Observation ℓ
  | 0, i => i
  | ℓ+1, ⟨_,v⟩ => (List.ofFn (fun j ↦ forgetOrdered ℓ (v j)) : Multiset (Observation ℓ))

end ThreeState.TreeClauses.Tree

end 

noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal
namespace ThreeState.TreeClauses.Tree
open ThreeState.TreeClauses.Experiment

end ThreeState.TreeClauses.Tree

end 

noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace ThreeState.TreeClauses.Experiment
-- [generator] trimmed: open ThreeState.TreeClauses.Radial ThreeState.TreeClauses.Positive
open ThreeState.TreeClauses.Radial

end ThreeState.TreeClauses.Experiment

end

end OAI


