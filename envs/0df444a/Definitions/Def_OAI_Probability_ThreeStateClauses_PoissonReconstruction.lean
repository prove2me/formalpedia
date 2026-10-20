-- Prove2me | Definitions.Def_OAI_Probability_ThreeStateClauses_PoissonReconstruction
-- name    : OAI_Probability_ThreeStateClauses_PoissonReconstruction
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T19:59:08.410858+00:00
-- url     : https://prove2.me/theorems/86df03b7-11c0-4a8e-b47d-a82a0bc37e21
-- title:
--   Normalized boundary statistics for Galton–Watson broadcast trees and the Poisson Kesten–Stigum constant
-- statement:
--   Spins are elements of $\{0,1,2\}$, with spin score $\sigma(0)=2$ and $\sigma(1)=\sigma(2)=-1$. Fix $d,\lambda\in\mathbb{R}$.
--
--   1. **On ordered observations.** For a depth-$(\ell+1)$ ordered observation $(n,v)$, with $n$ children and ordered child observations $v_0,\dots,v_{n-1}$,
--   $$
--   S_0(i)=\sigma(i),\qquad S_{\ell+1}(n,v)=\frac{1}{d\lambda}\sum_{j<n}S_\ell(v_j).
--   $$
--   2. **On unordered observations.** $\widehat S_0(i)=\sigma(i)$, and $\widehat S_{\ell+1}(s)$ is $\frac1{d\lambda}$ times the sum of $\widehat S_\ell$ over the elements of the multiset $s$.
--   3. **Constant.**
--   $$
--   \kappa(d,\lambda)=\frac{4\,d\lambda^2}{d\lambda^2-1}.
--   $$
--
--   $S_\ell$ is $(d\lambda)^{-\ell}$ times the sum of the spin scores at depth $\ell$, normalized to have conditional mean $\sigma(i)$ given root spin $i$ when the mean offspring number is $d$. Above the threshold $d\lambda^2>1$, $\kappa(d,\lambda)$ bounds its second moment uniformly in $\ell$.
--
--   **Formalization Note** The names are `orderedStatistic d lam`, `observedStatistic d lam` and `poissonKSConstant d lam`. Lean's convention $x/0=0$ applies when $d\lambda=0$ or $d\lambda^2=1$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ThreeStateClauses/PoissonReconstruction.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/ThreeStateClauses/PoissonReconstruction.lean by skeleton subtraction
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
import Definitions.Def_OAI_Probability_ThreeStateClauses_OffspringLaws

namespace OAI

/-! Poisson Reconstruction. -/

open scoped BigOperators ENNReal NNReal Topology
open Filter
noncomputable section
open Set MeasureTheory
open scoped BigOperators NNReal
namespace ThreeState.TreeClauses.Tree
open ThreeState.TreeClauses.Experiment ThreeState.TreeClauses.Probability

def orderedStatistic (d lam : ℝ) : (ℓ : ℕ) → OrderedObservation ℓ → ℝ
  | 0, i => spinScore i
  | ℓ+1, ⟨_,v⟩ => (∑ j, orderedStatistic d lam ℓ (v j))/(d*lam)

def observedStatistic (d lam : ℝ) : (ℓ : ℕ) → Observation ℓ → ℝ
  | 0, i => spinScore i
  | ℓ+1, s => (s.map (observedStatistic d lam ℓ)).sum/(d*lam)

end ThreeState.TreeClauses.Tree

end 

noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology NNReal
namespace ThreeState.TreeClauses.Tree
open ThreeState.TreeClauses.Experiment ThreeState.TreeClauses.Probability

def poissonKSConstant (d lam : ℝ) : ℝ := 4*(d*lam^2)/(d*lam^2-1)

end ThreeState.TreeClauses.Tree

end

end OAI


