-- Prove2me | Definitions.Def_Curvature_InverseLinearActions
-- name    : Curvature_InverseLinearActions
-- status  : Definition
-- author  : @ssakaue
-- created : 2026-11-24T07:20:11.023451+00:00
-- url     : https://prove2.me/theorems/2f984bc5-8b21-4d76-9416-32c50f6a341f
-- title:
--   Action sets, optimal recommendations and the utility shortfall in online inverse linear optimization
-- statement:
--   This file defines the objects of the online inverse linear optimization protocol in Corollary 8. An action set with diameter bound $G$ is a nonempty compact set $\mathcal X\subset\mathbb R^d$ with $\lVert a-b\rVert_2\le G$ for all $a,b\in\mathcal X$. An action $a$ is optimal in $\mathcal X$ for a vector $w$ if $a\in\mathcal X$ and $\langle w,b\rangle\le\langle w,a\rangle$ for every $b\in\mathcal X$. The shortfall of an action $y$ under a utility vector $u$ is
--
--   $$
--   \max_{a\in\mathcal X}\langle u,a-y\rangle.
--   $$
--
--   For a feasible action $y\in\mathcal X$, the shortfall is nonnegative and vanishes exactly when $y$ is optimal in $\mathcal X$ for $u$.
--
--   Given a nonempty compact convex domain $\mathcal K$ with a domain initialization, a weight rule and a bound $G$, the utility estimate of round $t$ is the prediction $w_t\in\mathcal K$ of Algorithm 5 on the inputs of the rounds before $t$. In the protocol of Corollary 8, these inputs are $\widehat a_s-y_s$, the recommended action minus the observed action, and the learner recommends an action that is optimal in the current action set for $w_t$. These definitions follow Section 5.2 and Appendix G.
-- source:
--   arXiv:2611.27572v1, Corollary 8, Section 5.2, pp. 15–16; Appendix G, pp. 65–66. https://arxiv.org/html/2611.27572v1#Thmtheorem8

import Definitions.Def_Curvature_AdaptivePredictor

section
set_option autoImplicit false
noncomputable section
namespace Curvature

variable {d : ℕ} {K : Set (Vec d)} {G W : ℝ}

structure InverseLinearActions (d : ℕ) (G : ℝ) where
  carrier : Set (Vec d)
  nonempty : carrier.Nonempty
  compact : IsCompact carrier
  diameterBound : ∀ a ∈ carrier, ∀ b ∈ carrier, norm₂ (a-b) ≤ G

def InverseLinearActions.Optimal (X : InverseLinearActions d G) (w a : Vec d) : Prop :=
  a ∈ X.carrier ∧ ∀ b ∈ X.carrier, dotProduct w b ≤ dotProduct w a


def InverseLinearActions.shortfall (X : InverseLinearActions d G) (u y : Vec d) : ℝ :=
  sSup ((fun a => dotProduct u (a-y)) '' X.carrier)


section Protocol
variable (I : DomainInitialization K) (hc : IsCompact K) (hcv : Convex ℝ K) (hne : K.Nonempty)
  (P : AdaptiveWeightRule (adaptiveWidthScale G W))

/-- The utility estimate uses only feedback from earlier rounds. -/
def inverseLinearPredict (t : ℕ) (past : Fin t → Vec d) : K :=
  (I.adaptiveBase hne hc hcv).adaptivePlay hcv P G
    (fun j => if h : j < t then past ⟨j,h⟩ else 0) t


end Protocol
end Curvature

end
end


