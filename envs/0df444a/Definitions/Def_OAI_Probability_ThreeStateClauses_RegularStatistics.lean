-- Prove2me | Definitions.Def_OAI_Probability_ThreeStateClauses_RegularStatistics
-- name    : OAI_Probability_ThreeStateClauses_RegularStatistics
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T19:50:01.535264+00:00
-- url     : https://prove2.me/theorems/4e058f5d-2919-4951-80fe-889783cf59fb
-- title:
--   Normalized boundary statistics for the $b$-ary broadcast tree
-- statement:
--   Spins are elements of $\{0,1,2\}$, with spin score $\sigma(0)=2$ and $\sigma(1)=\sigma(2)=-1$. Fix $b\in\mathbb{N}$ and $\lambda\in\mathbb{R}$.
--
--   1. **On ordered observations.** The statistic $T_\ell$ on depth-$\ell$ ordered $b$-ary observations is $T_0(i)=\sigma(i)$ and
--   $$
--   T_{\ell+1}(v_0,\dots,v_{b-1})=\frac{1}{b\lambda}\sum_{j<b}T_\ell(v_j).
--   $$
--   2. **On unordered observations.** The statistic $\widehat T_\ell$ on depth-$\ell$ multiset observations is $\widehat T_0(i)=\sigma(i)$. For a multiset $s$ with exactly $b$ elements, $\widehat T_{\ell+1}(s)$ is $\frac{1}{b\lambda}$ times the sum of $\widehat T_\ell$ over the elements of $s$. For any other multiset it is $0$.
--
--   Unrolling the recursion, $T_\ell$ is $(b\lambda)^{-\ell}$ times the sum of the spin scores at depth $\ell$. Its mean given root spin $i$ is $\sigma(i)$, and it is the Kesten–Stigum estimator of the root.
--
--   **Formalization Note** The names are `spinScore`, `regularStatistic b lam` and `observedRegularStatistic b lam`. With Lean's convention $x/0=0$, both statistics vanish beyond depth $0$ if $b\lambda=0$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ThreeStateClauses/RegularStatistics.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/ThreeStateClauses/RegularStatistics.lean by skeleton subtraction
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

namespace OAI

/-! Regular Statistics. -/

open scoped BigOperators ENNReal NNReal Topology
open Filter
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace ThreeState.TreeClauses.Experiment

variable {α β : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]
  [Fintype β] [MeasurableSpace β] [MeasurableSingletonClass β]

end ThreeState.TreeClauses.Experiment

end 

noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace ThreeState.TreeClauses.Tree
open ThreeState.TreeClauses.Experiment

def spinScore (i : Spin) : ℝ := if i=0 then 2 else -1

def regularStatistic (b : ℕ) (lam : ℝ) : (ℓ : ℕ) → RegularObservation b ℓ → ℝ
  | 0, i => spinScore i
  | ℓ+1, v => (∑ j : Fin b, regularStatistic b lam ℓ (v j))/((b:ℝ)*lam)

def observedRegularStatistic (b : ℕ) (lam : ℝ) : (ℓ : ℕ) → Observation ℓ → ℝ
  | 0, i => spinScore i
  | ℓ+1, s => if s.card = b then (s.map (observedRegularStatistic b lam ℓ)).sum/((b:ℝ)*lam) else 0

end ThreeState.TreeClauses.Tree

end

end OAI


