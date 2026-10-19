-- Prove2me | Definitions.Def_OAI_Probability_ThreeState_Supercritical
-- name    : OAI_Probability_ThreeState_Supercritical
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T09:40:28.099608+00:00
-- url     : https://prove2.me/theorems/fc279c40-29b6-4e3d-bbdd-34eabc94ec17
-- title:
--   Spin score, boundary score of tree observations, and posterior score
-- statement:
--   Throughout, a spin is an element of $\{0,1,2\}$. A parameter $\lambda\in\mathbb{R}$ is admissible if $-\tfrac12\le\lambda\le1$; then the symmetric channel $M_\lambda(i,j)=\tfrac{1+2\lambda}{3}$ for $j=i$ and $M_\lambda(i,j)=\tfrac{1-\lambda}{3}$ for $j\ne i$ is a stochastic matrix. A depth-$0$ observation is a spin, and a depth-$(n+1)$ observation is a finite multiset of depth-$n$ observations. A law is a family $(P_i)_{i=0,1,2}$ of discrete distributions on an observation space, indexed by the root spin. Its marginal is $\bar P=\frac13(P_0+P_1+P_2)$. The posterior of spin $i$ given $y$ is $\pi(y,i)=P_i(y)/(3\bar P(y))$, or $\tfrac13$ when $\bar P(y)=0$.
--
--   1. **Sum scores.** For $f:\alpha\to\mathbb{R}$ and a list or multiset $\{a_1,\dots,a_k\}$ of elements of $\alpha$, the score is $\sum_{j=1}^k f(a_j)$.
--   2. **Spin score.** $\sigma(0)=2$ and $\sigma(1)=\sigma(2)=-1$.
--   3. **Boundary score.** $S_0(y)=\sigma(y)$ for a spin $y$, and $S_{n+1}(\{y_1,\dots,y_k\})=\sum_{j}S_n(y_j)$. So $S_n$ is the sum of the spin scores of all generation-$n$ vertices.
--   4. **Second-moment recursion.** For parameters $d,e\in\mathbb{R}$,
--   $$
--   Q_0(i)=\sigma(i)^2,\qquad Q_{n+1}(i)=d\sum_{j}M_\lambda(i,j)\,Q_n(j)+e\bigl((d\lambda)^n\lambda\,\sigma(i)\bigr)^2 .
--   $$
--   5. **Posterior statistics.** For a law $P$ and an observation $y$,
--   $$
--   T(y)=\frac12\sum_{i=0}^{2}\Bigl|\pi(y,i)-\frac13\Bigr|,\qquad \rho(y)=3\,\pi(y,0)-1 .
--   $$
--
--   $S_n$ is the linear (Kesten–Stigum type) estimator of the root spin, and $Q_n$ is its second moment. The marginal expectation of $T$ is the posterior advantage, and $\rho$ is the statistic used to lower-bound the advantage through correlation with $S_n$.
--
--   **Formalization Note** The names are `listScore`, `multisetScore`, `spinScore`, `boundaryScore`, `scoreSecond`, `posteriorTV` and `posteriorScore`. `scoreSecond d e lam h` takes the admissibility proof `h` because the channel is a probability mass function built from it.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ThreeState/Supercritical.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/ThreeState/Supercritical.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the ThreeStateSupercritical mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_ThreeStateSupercritical
import Definitions.Def_OAI_Probability_ThreeState_Basic
import Definitions.Def_OAI_Probability_ThreeState_Expectations
import Definitions.Def_OAI_Probability_ThreeState_Messages
import Definitions.Def_OAI_Probability_ThreeState_Observation
import Definitions.Def_OAI_Probability_ThreeState_Update
import Definitions.Def_OAI_Probability_ThreeState_RadialMoments
import Definitions.Def_OAI_Probability_ThreeState_RadialDerivatives
import Definitions.Def_OAI_Probability_ThreeState_PosteriorMoments
import Definitions.Def_OAI_Probability_ThreeState_PoissonCritical

namespace OAI

/-! Boundary score moments and reconstruction above the Kesten–Stigum threshold. -/

namespace ThreeState

noncomputable def listScore {α : Type*} (f : α → ℝ) (as : List α) : ℝ := (as.map f).sum
noncomputable def multisetScore {α : Type*} (f : α → ℝ) (as : Multiset α) : ℝ := (as.map f).sum

 

 

def spinScore (i : Spin) : ℝ := if i=0 then 2 else -1

noncomputable def boundaryScore : (n : ℕ) → Observation n → ℝ
  | 0 => spinScore
  | n+1 => multisetScore (boundaryScore n)

noncomputable def scoreSecond (d e lam : ℝ) (h : Admissible lam) : ℕ → Spin → ℝ
  | 0, i => (spinScore i)^2
  | n+1, i => d*mean (channelPMF lam h i) (scoreSecond d e lam h n) +
      e*((d*lam)^n*lam*spinScore i)^2

 
 

end ThreeState

namespace ThreeState

 
noncomputable def posteriorTV {α : Type*} (law : Spin → PMF α) (y : α) : ℝ :=
  (∑ i : Spin, |posterior law y i-1/3|)/2

noncomputable def posteriorScore {α : Type*} (law : Spin → PMF α) (y : α) : ℝ :=
  3*posterior law y 0-1

 

end ThreeState

namespace ThreeState

 

 

 

 

end ThreeState

end OAI


