-- Prove2me | Definitions.Def_OAI_Probability_ThreeStateClauses_InformationLoss
-- name    : OAI_Probability_ThreeStateClauses_InformationLoss
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T19:52:16.803926+00:00
-- url     : https://prove2.me/theorems/3dcf92f1-95bf-45c6-a25e-c2860329b98d
-- title:
--   Independent kernels on multisets and the growth kernel of observation trees
-- statement:
--   Spins are elements of $\{0,1,2\}$. A parameter $\lambda\in\mathbb{R}$ is admissible if $-\tfrac12\le\lambda\le1$; the channel $M_\lambda(i,\cdot)$ keeps the spin $i$ with probability $\tfrac{1+2\lambda}{3}$ and moves it to each other spin with probability $\tfrac{1-\lambda}{3}$. A depth-$0$ observation is a spin, and a depth-$(\ell+1)$ observation is a finite multiset of depth-$\ell$ observations. For an offspring law $\mu$ on $\mathbb{N}$, $\mathcal L_\ell(i)$ is the law of the depth-$\ell$ observation with root spin $i$. $\mathcal L_0(i)$ is the point mass at $i$. To sample $\mathcal L_{\ell+1}(i)$, draw $K\sim\mu$ and then $K$ independent pairs (child spin $j\sim M_\lambda(i,\cdot)$, observation from $\mathcal L_\ell(j)$), and record the multiset of the $K$ observations.
--
--   1. **Multiset kernel.** For a kernel $K$ from $\alpha$ to $\beta$ and a multiset $s=\{a_1,\dots,a_k\}$ of elements of $\alpha$, draw $b_r\sim K(a_r)$ independently and return the multiset $\{b_1,\dots,b_k\}$. This is well defined because the order of independent draws does not matter. The empty multiset is sent to the point mass at the empty multiset.
--   2. **Observation expansion.** The kernel $G_\ell$ sends a depth-$\ell$ observation to a random depth-$(\ell+1)$ observation. A spin $i$ at depth $0$ is sent to $\mathcal L_1(i)$: it grows its children. A multiset at depth $\ell+1$ is sent to the multiset kernel of $G_\ell$ applied to it.
--
--   Applying $G_\ell$ to a sample of $\mathcal L_\ell(i)$ yields a sample of $\mathcal L_{\ell+1}(i)$. So the deeper observation is a degradation of the shallower one, which makes the reconstruction advantage non-increasing in depth.
--
--   **Formalization Note** `multisetKernel K s` is defined by `Multiset.recOn`, with a proof that consecutive draws commute. `observationExpansion lam hlam offspring ℓ` takes the admissibility proof as an argument.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ThreeStateClauses/InformationLoss.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/ThreeStateClauses/InformationLoss.lean by skeleton subtraction
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

namespace OAI

/-! Information Loss. -/

open scoped BigOperators ENNReal NNReal Topology
open Filter
noncomputable section
open scoped BigOperators
namespace ThreeState.TreeClauses.Experiment

variable {α β γ : Type}

def multisetKernel (K : α → PMF β) (s : Multiset α) : PMF (Multiset β) :=
  Multiset.recOn s (PMF.pure 0)
    (fun a _ p ↦ (K a).bind (fun b ↦ p.map (Multiset.cons b))) (by
      intro a a' s p
      apply heq_of_eq
      simp only [PMF.map_bind, PMF.map_comp]
      rw [PMF.bind_comm (K a) (K a')]
      congr 1
      funext b'
      congr 1
      funext b
      congr 1
      funext t
      exact Multiset.cons_swap _ _ _)

@[simp] lemma multisetKernel_zero (K : α → PMF β) : multisetKernel K 0 = PMF.pure 0 := by
  rw [multisetKernel, Multiset.recOn_0]

@[simp] lemma multisetKernel_cons (K : α → PMF β) (a : α) (s : Multiset α) :
    multisetKernel K (a ::ₘ s) = (K a).bind (fun b ↦ (multisetKernel K s).map (Multiset.cons b)) := by
  rw [multisetKernel, Multiset.recOn_cons]
  rfl

def observationExpansion (lam : ℝ) (hlam : Admissible lam) (offspring : PMF ℕ) :
    (ℓ : ℕ) → Observation ℓ → PMF (Observation (ℓ+1))
  | 0, i => observationLaw lam hlam offspring 1 i
  | ℓ+1, s => multisetKernel (observationExpansion lam hlam offspring ℓ) s

end ThreeState.TreeClauses.Experiment

end 

noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology
namespace ThreeState.TreeClauses.Experiment
-- [generator] trimmed: open ThreeState.TreeClauses.Radial ThreeState.TreeClauses.Positive
open ThreeState.TreeClauses.Radial

variable {α β : Type*} [Countable α] [MeasurableSpace α] [MeasurableSingletonClass α]
  [Countable β] [MeasurableSpace β] [MeasurableSingletonClass β]

end ThreeState.TreeClauses.Experiment

end 

noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace ThreeState.TreeClauses.Experiment
-- [generator] trimmed: open ThreeState.TreeClauses.Radial ThreeState.TreeClauses.Positive
open ThreeState.TreeClauses.Radial

variable {α : Type*} [Countable α] [MeasurableSpace α] [MeasurableSingletonClass α]

end ThreeState.TreeClauses.Experiment

end

end OAI


