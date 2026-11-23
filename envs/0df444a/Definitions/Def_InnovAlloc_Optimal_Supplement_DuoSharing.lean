-- Prove2me | Definitions.Def_InnovAlloc_Optimal_Supplement_DuoSharing
-- name    : InnovAlloc_Optimal_Supplement_DuoSharing
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T09:48:15.440008+00:00
-- url     : https://prove2.me/theorems/b95ba37c-6a36-4931-8201-fce264ebccc6
-- title:
--   Equations (13)–(14), pp. 18–19 — symmetric equal-investment sharing problem
-- statement:
--   Let $B$ be capacity, $\alpha\in[0,1]$ the two-product profit parameter, and $\gamma\in(0,1)$ the common share. Under equal investment $(B/2,B/2)$, equation (13) gives symmetric failure probability
--
--   $$y(\alpha,\gamma,B)=\begin{cases}1,&\gamma B\le2,\\\dfrac4{\alpha\gamma B+\sqrt{\gamma B}\sqrt{8-8\alpha+\alpha^2\gamma B}},&\gamma B>2.\end{cases}$$
--
--   The share problem maximizes the published scalar objective $\Pi_d(\alpha,\gamma,B)$, equivalently $(1-\gamma)[2\alpha(1-y)^2+2(1-y)y]$, over all $0<\gamma<1$. A maximizing share must belong to that interval and dominate every other admissible share. The function $\gamma_d(\alpha,B)$ chooses such a maximizer if one exists, and returns zero otherwise. Proposition 5 establishes existence and uniqueness for every $B>2$.
--
--   This is the symmetric-equilibrium benchmark, including $\alpha=0$; it does not assert uniqueness of all effort equilibria. The choice function contains no comparative statics or allocation thresholds.
-- source:
--   Gao, Fan, Huang & Chen, “Resource Allocation Among Competing Innovators”, SSRN preprint 3658157 (February 2021), pp. 18–19, equations (13)–(14)

import Mathlib
import Definitions.Def_InnovAlloc_Optimal_Model

namespace InnovAlloc.Optimal.Supplement

noncomputable section

/-- The symmetric failure probability (13), including the zero-effort branch. -/
def duoFailure (α γ B : ℝ) : ℝ :=
  if γ * B ≤ 2 then 1 else yStar α γ B

/-- Maximize the published scalar equal-investment objective (13)–(14), pp. 18–19.
At α = 0 this is the symmetric-equilibrium benchmark, not a claim of unique game equilibria. -/
def IsDuoShare (α B γ : ℝ) : Prop :=
  γ ∈ Set.Ioo (0 : ℝ) 1 ∧
    ∀ η ∈ Set.Ioo (0 : ℝ) 1, profitDuo α η B ≤ profitDuo α γ B

/-- Choose a genuine maximizer when one exists, and 0 otherwise.
Proposition 5 asserts existence and uniqueness throughout α ∈ [0,1], B > 2. -/
def gammaD (α B : ℝ) : ℝ := by
  classical
  exact if h : ∃ γ, IsDuoShare α B γ then Classical.choose h else 0

end
end InnovAlloc.Optimal.Supplement


