-- Prove2me | Definitions.Def_OAI_Probability_ThreeState_PoissonCritical
-- name    : OAI_Probability_ThreeState_PoissonCritical
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T09:38:35.788286+00:00
-- url     : https://prove2.me/theorems/3071b666-a4b0-4270-8d9b-b17228436cef
-- title:
--   The uninformative message is a fixed point of the message update
-- statement:
--   Throughout, a spin is an element of $\{0,1,2\}$. A parameter $\lambda\in\mathbb{R}$ is admissible if $-\tfrac12\le\lambda\le1$; then the symmetric channel $M_\lambda(i,j)=\tfrac{1+2\lambda}{3}$ for $j=i$ and $M_\lambda(i,j)=\tfrac{1-\lambda}{3}$ for $j\ne i$ is a stochastic matrix. Messages are vectors in $\mathbb{R}^3$ with nonnegative coordinates summing to $3$, and $\mathbf 1=(1,1,1)$ is the uninformative message. For $n$ child messages, $W_i=\prod_j\bigl(1+\lambda(m^{(j)}_i-1)\bigr)$ is the product weight and $Z=\frac13\sum_iW_i$ the normalizer. The combined message is $W/Z$, or $\mathbf 1$ if $Z=0$. Finally, $X(m)=\frac16\sum_i(m_i-1)^2$.
--
--   For every admissible $\lambda$ and every $n\in\mathbb{N}$, the following three facts hold when all $n$ child messages equal $\mathbf 1$:
--
--   1. the normalizer is $Z=1$;
--   2. the combined message is again $\mathbf 1$;
--   3. $X(\mathbf 1)=0$.
--
--   Thus uninformative children produce an uninformative parent. This is the trivial fixed point of the message recursion around which reconstruction questions are posed.
--
--   **Formalization Note** The three facts are the simplification lemmas `normalizer_uninformative`, `combineMessage_uninformative` and `messageX_uninformative`. The rest of the source module is not needed by this mission's proofs.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ThreeState/PoissonCritical.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/ThreeState/PoissonCritical.lean by skeleton subtraction
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

namespace OAI

/-! Informative posterior mass and positive critical Poisson non-reconstruction. -/

namespace ThreeState
open MeasureTheory Filter Topology
open scoped Classical

@[simp] lemma normalizer_uninformative (lam : ℝ) (h : Admissible lam) (n : ℕ) :
    normalizer lam h (fun _ : Fin n => uninformative) = 1 := by
  simp [normalizer,productWeight,edgeMessage,uninformative]

@[simp] lemma combineMessage_uninformative (lam : ℝ) (h : Admissible lam) (n : ℕ) :
    combineMessage lam h (fun _ : Fin n => uninformative) = uninformative := by
  simp only [combineMessage,normalizer_uninformative,one_ne_zero,↓reduceDIte,div_one]
  apply Subtype.ext
  funext i
  simp [productWeight,edgeMessage,uninformative]

end ThreeState
namespace ThreeState
open MeasureTheory Filter Topology
open scoped Classical

@[simp] lemma messageX_uninformative : messageX uninformative = 0 := by
  simp [messageX,Radial.momentX,Radial.avg_expand,messageDeviation,uninformative]

end ThreeState
namespace ThreeState
open MeasureTheory Filter Topology
open scoped Classical

 
end ThreeState

end OAI


