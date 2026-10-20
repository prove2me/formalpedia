-- Prove2me | Definitions.Def_OAI_Probability_ThreeStateClauses_RegularLaw
-- name    : OAI_Probability_ThreeStateClauses_RegularLaw
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T19:44:47.477275+00:00
-- url     : https://prove2.me/theorems/0966a2df-5adc-4103-ae12-fa529d3150d2
-- title:
--   Ordered observations of the $b$-ary broadcast tree and their unordered forgetful image
-- statement:
--   Spins are elements of $\{0,1,2\}$. A parameter $\lambda\in\mathbb{R}$ is admissible if $-\tfrac12\le\lambda\le1$; the channel $M_\lambda(i,\cdot)$ keeps the spin $i$ with probability $\tfrac{1+2\lambda}{3}$ and moves it to each other spin with probability $\tfrac{1-\lambda}{3}$.
--
--   1. **Ordered regular observations.** For $b\in\mathbb{N}$: a depth-$0$ observation is a spin, and a depth-$(\ell+1)$ observation is an ordered $b$-tuple of depth-$\ell$ observations. These are finite types. They carry the discrete $\sigma$-algebra, so all singletons are measurable.
--   2. **Unordered observations.** A depth-$0$ observation is a spin, and a depth-$(\ell+1)$ observation is a finite multiset of depth-$\ell$ observations. These are countable types, also given the discrete $\sigma$-algebra.
--   3. **Regular law.** $\mathcal R_0(i)$ is the point mass at $i$. $\mathcal R_{\ell+1}(i)$ is the product of $b$ independent copies of the law "draw $j\sim M_\lambda(i,\cdot)$, then a depth-$\ell$ observation from $\mathcal R_\ell(j)$".
--   4. **Forgetting the order.** The map from ordered to unordered observations is the identity on spins. At depth $\ell+1$ it turns the $b$-tuple $(v_0,\dots,v_{b-1})$ into the multiset $\{\phi(v_0),\dots,\phi(v_{b-1})\}$ of the forgotten children.
--
--   The ordered model is easier to compute with: it has a finite state space and a product structure. Forgetting the order recovers the unordered observation law of the regular tree.
--
--   **Formalization Note** The types are `RegularObservation b ℓ` and `Observation ℓ`, the law is `regularLaw b lam hlam`, and the forgetful map is `forgetRegular b ℓ`. The `Fintype`, `Countable`, `MeasurableSpace` and `MeasurableSingletonClass` instances are defined by recursion on $\ell$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ThreeStateClauses/RegularLaw.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/ThreeStateClauses/RegularLaw.lean by skeleton subtraction
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

namespace OAI

/-! Regular Law. -/

open scoped BigOperators ENNReal NNReal Topology
open Filter
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal
namespace ThreeState.TreeClauses.Tree
open ThreeState.TreeClauses.Experiment

def RegularObservation (b : ℕ) : ℕ → Type
  | 0 => Spin
  | n+1 => Fin b → RegularObservation b n

instance regularObservationFintype (b ℓ : ℕ) : Fintype (RegularObservation b ℓ) := by
  induction ℓ with
  | zero => exact inferInstanceAs (Fintype Spin)
  | succ ℓ ih => letI := ih; exact inferInstanceAs (Fintype (Fin b → RegularObservation b ℓ))

instance regularObservationMeasurable (b : ℕ) : (ℓ : ℕ) → MeasurableSpace (RegularObservation b ℓ)
  | 0 => inferInstanceAs (MeasurableSpace Spin)
  | ℓ+1 => letI := regularObservationMeasurable b ℓ
           inferInstanceAs (MeasurableSpace (Fin b → RegularObservation b ℓ))
instance regularObservationSingleton (b : ℕ) : (ℓ : ℕ) → MeasurableSingletonClass (RegularObservation b ℓ)
  | 0 => inferInstanceAs (MeasurableSingletonClass Spin)
  | ℓ+1 => letI := regularObservationSingleton b ℓ
           inferInstanceAs (MeasurableSingletonClass (Fin b → RegularObservation b ℓ))

instance observationCountable (ℓ : ℕ) : Countable (Observation ℓ) := by
  induction ℓ with
  | zero => exact inferInstanceAs (Countable Spin)
  | succ ℓ ih => let := ih; exact inferInstanceAs (Countable (Multiset (Observation ℓ)))

instance observationMeasurable (ℓ : ℕ) : MeasurableSpace (Observation ℓ) := ⊤
instance observationSingleton (ℓ : ℕ) : MeasurableSingletonClass (Observation ℓ) :=
  ⟨fun _ ↦ MeasurableSpace.measurableSet_top⟩

def regularLaw (b : ℕ) (lam : ℝ) (hlam : Admissible lam) :
    (ℓ : ℕ) → Spin → PMF (RegularObservation b ℓ)
  | 0, i => PMF.pure i
  | ℓ+1, i => productPMF (fun _ : Fin b ↦ (channel lam hlam i).bind (regularLaw b lam hlam ℓ))

def forgetRegular (b : ℕ) : (ℓ : ℕ) → RegularObservation b ℓ → Observation ℓ
  | 0, i => i
  | ℓ+1, v => (List.ofFn (fun j ↦ forgetRegular b ℓ (v j)) : Multiset (Observation ℓ))

end ThreeState.TreeClauses.Tree

end

end OAI


