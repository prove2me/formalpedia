-- Prove2me | Definitions.Def_PGLandscape_ApproxClosure_Condition5
-- name    : PGLandscape_ApproxClosure_Condition5
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T06:28:27.155324+00:00
-- url     : https://prove2.me/theorems/718c5bb7-1b6c-40fa-96f3-a1c076bd0578
-- title:
--   Condition 5, p. 26 — approximate closure under policy improvement
-- statement:
--   Let $\Pi_\Theta=\{\pi_\theta:\theta\in\Theta\}$ be a parameterized policy class and $\Pi$ the class of all feasible measurable stationary policies. The class is **closed under approximate policy improvement** with **inherent Bellman error** $\varepsilon\ge0$ if for every $\pi\in\Pi_\Theta$,
--
--   $$
--   \min_{\pi^+\in\Pi_\Theta}B(\pi^+\mid\eta_\pi,J_\pi)\le\min_{\pi'\in\Pi}B(\pi'\mid\eta_\pi,J_\pi)+\varepsilon ,
--   $$
--
--   where $B(\bar\pi\mid\eta,J)=\int(T_{\bar\pi}J)\,d\eta$. When $\varepsilon=0$ and the minimum over $\Pi$ is attained in $\Pi_\Theta$, this is exact closure under policy improvement (Condition 1). The error is measured in the occupancy distribution of the current policy.
--
--   **Formalization Note** The page's "there exists $\varepsilon\ge0$" is a parameter $\varepsilon$ of the predicate with $0\le\varepsilon$ inside it. The minimum over $\Pi_\Theta$ is read as attained, as the page writes "min": some $\theta^+\in\Theta$ satisfies $B(\theta^+\mid\eta_{\pi_\theta},J_{\pi_\theta})\le B(\pi'\mid\eta_{\pi_\theta},J_{\pi_\theta})+\varepsilon$ for every $\pi'\in\Pi$.
-- source:
--   arXiv:1906.01786v3, Condition 5, (23), p. 26

import Mathlib
import Definitions.Def_PGLandscape_Closure_Conditions

namespace PGLandscape.ApproxClosure

open MeasureTheory ProbabilityTheory

variable {S A : Type*} [MeasurableSpace S] [MeasurableSpace A]

/-- Condition 5 (Closure under approximate policy improvement), (23), p. 26: `ε ≥ 0` and for every
`π = π_θ ∈ Π_Θ`, `min_{π⁺∈Π_Θ} B(π⁺ | η_π, J_π) ≤ min_{π'∈Π} B(π' | η_π, J_π) + ε`. The page's "there
exists `ε ≥ 0`" is the parameter `ε`; the minimum over `Π_Θ` is read as attained (a witness `θ⁺ ∈ Θ`),
and the minimum over `Π` as a lower bound for every `π' ∈ Π` (it is attained by Assumption 2). -/
def Condition5 {d : ℕ} (M : PGLandscape.Closure.MDP S A) (Θ : Set (EuclideanSpace ℝ (Fin d)))
    (πθ : EuclideanSpace ℝ (Fin d) → PGLandscape.Closure.MPolicy S A) (ε : ℝ) : Prop :=
  0 ≤ ε ∧ ∀ θ ∈ Θ, ∃ θplus ∈ Θ, ∀ π' : PGLandscape.Closure.MPolicy S A, PGLandscape.Closure.IsFeasible M π' →
    PGLandscape.Closure.piObjective M πθ θ θplus ≤
      PGLandscape.Closure.bellmanObj M π'.1 (PGLandscape.Closure.occupancy M (πθ θ)) (PGLandscape.Closure.costToGo M (πθ θ)) + ε

end PGLandscape.ApproxClosure


