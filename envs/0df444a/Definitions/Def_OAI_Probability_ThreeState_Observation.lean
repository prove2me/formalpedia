-- Prove2me | Definitions.Def_OAI_Probability_ThreeState_Observation
-- name    : OAI_Probability_ThreeState_Observation
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T09:30:06.575488+00:00
-- url     : https://prove2.me/theorems/e54587c3-7711-43aa-9874-6755e362a219
-- title:
--   Growing a depth-$n$ tree observation into a depth-$(n+1)$ observation
-- statement:
--   Throughout, a spin is an element of $\{0,1,2\}$. A parameter $\lambda\in\mathbb{R}$ is admissible if $-\tfrac12\le\lambda\le1$; then the symmetric channel $M_\lambda(i,j)=\tfrac{1+2\lambda}{3}$ for $j=i$ and $M_\lambda(i,j)=\tfrac{1-\lambda}{3}$ for $j\ne i$ is a stochastic matrix.
--
--   Observations are defined by depth. A depth-$0$ observation is a spin, and a depth-$(n+1)$ observation is a finite multiset of depth-$n$ observations. Fix an offspring distribution $\mu$ on $\mathbb{N}$. The law $\mathcal L_n(i)$ of the depth-$n$ observation with root spin $i$ is defined as follows. $\mathcal L_0(i)$ is the point mass at $i$. To sample from $\mathcal L_{n+1}(i)$, draw $K\sim\mu$, then draw $K$ independent copies of the following: a child spin $j\sim M_\lambda(i,\cdot)$, followed by a depth-$n$ observation from $\mathcal L_n(j)$. Record the unordered multiset of the $K$ results.
--
--   1. **Independent sampling commutes.** Discrete probability distributions form a commutative applicative functor. Drawing two independent samples and pairing them gives the same joint law whichever sample is drawn first. This is what makes it legitimate to sample independently over the elements of an unordered multiset.
--   2. **The growth kernel.** $G_n$ sends a depth-$n$ observation to a random depth-$(n+1)$ observation. $G_0(i)=\mathcal L_1(i)$: a spin at depth $0$ grows its own offspring. $G_{n+1}$ applies $G_n$ independently to each element of a multiset and collects the results into a multiset:
--   $$
--   G_{n+1}\bigl(\{y_1,\dots,y_k\}\bigr)=\bigl\{G_n(y_1),\dots,G_n(y_k)\bigr\}\quad(\text{independent draws}).
--   $$
--
--   Applying $G_n$ to a sample of $\mathcal L_n(i)$ produces a sample of $\mathcal L_{n+1}(i)$. So the depth-$(n+1)$ observation is a randomized function of the depth-$n$ observation. This is the source of the monotonicity (information degradation) of the posterior advantage in $n$.
--
--   **Formalization Note** The commutative structure is a `CommApplicative PMF` instance, used through `Multiset.traverse`. `grow offspring lam h n` has type `Observation n → PMF (Observation (n+1))`, and the admissibility proof `h` is an explicit argument.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ThreeState/Observation.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/ThreeState/Observation.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the ThreeStateSupercritical mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_ThreeStateSupercritical
import Definitions.Def_OAI_Probability_ThreeState_Basic
import Definitions.Def_OAI_Probability_ThreeState_Expectations
import Definitions.Def_OAI_Probability_ThreeState_Messages

namespace OAI

/-! Ordered and unlabelled boundary observations and information degradation. -/

namespace ThreeState

 

 
end ThreeState

namespace ThreeState

end ThreeState
universe u
namespace ThreeState

instance pmfCommApplicative : CommApplicative PMF where
  commutative_prod a b := by
    change ((a.map Prod.mk).bind (fun f => b.map f)) =
      ((b.map (fun y x => (x,y))).bind (fun f => a.map f))
    simp only [PMF.map, PMF.bind_bind, PMF.pure_bind, Function.comp_def]
    exact PMF.bind_comm a b (fun x y => PMF.pure (x,y))

 

noncomputable def grow (offspring : PMF ℕ) (lam : ℝ) (h : Admissible lam) :
    (n : ℕ) → Observation n → PMF (Observation (n+1))
  | 0 => observedLaw offspring lam h 1
  | n+1 => Multiset.traverse (grow offspring lam h n)

 
 
 
end ThreeState

end OAI


