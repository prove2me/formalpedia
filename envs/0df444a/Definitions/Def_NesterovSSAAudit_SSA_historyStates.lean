-- Prove2me | Definitions.Def_NesterovSSAAudit_SSA_historyStates
-- name    : NesterovSSAAudit_SSA_historyStates
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T14:41:37.319258+00:00
-- url     : https://prove2.me/theorems/df49e595-d676-47ce-82ca-07d212fc4192
-- title:
--   Canonical finite-history SSA states, points, averages and gaps
-- statement:
--   Let $E$ be a real normed space, $a:E\times\Xi\to E^*$ an oracle, $x_0\in E$, $\gamma\in\mathbb R$, and $\pi:\mathbb R\times E^*\to E$ a map. For a finite history $h=(\xi_0,\ldots,\xi_{n-1})$, compute the state recursively:
--
--   $$ (x_0,s_0)=(x_0,0),\qquad s_{i+1}=s_i+a(x_i,\xi_i),\qquad x_{i+1}=\pi_{\gamma\hat\beta_{i+1}}(-s_{i+1}).$$
--
--   Here the published sequence has $\hat\beta_0=\hat\beta_1=1$ and $\hat\beta_{i+1}=\hat\beta_i+1/\hat\beta_i$ for $i\ge1$. The time-$n$ state reads only the first $n$ observations. A finite nonempty history is extended by repeating its first entry outside the supplied range; all claimed observables are independent of this unused extension.
--
--   For a path $\omega$, the module defines $g_i=a(x_i,\omega_i)$, the average $\bar x_k=(k+1)^{-1}\sum_{i=0}^k x_i$, and
--
--   $$\delta_k(D)=\sup_{y\in Q,\ d(y)\le D}\sum_{i=0}^k\langle g_i,x_i-y\rangle.$$
--
--   The gap reuses the published level-set gap. In the theorems, $\pi$ is the exact prox map, $\gamma>0$, and the level set is nonempty compact in the admissible range of $D$, so the supremum is the source's maximum. These are actual computed objects rather than free sequences satisfying an accuracy bound.
-- source:
--   Yu. Nesterov, Primal-dual subgradient methods for convex problems, September 2005 revised manuscript, SHA256 095a7bfedc1ebd85f8fbd9e7765194e180a95c38fdfbef172ecd27cbe920f96c, p.10,26, (2.19), (6.3)–(6.4)

import Mathlib
import Definitions.Def_PrimalDualSubgrad_Stoch_ProxSetting
import Definitions.Def_NesterovSSAAudit_SSA_rawOracle

set_option autoImplicit false

namespace NesterovSSAAudit.SSA

open Finset PrimalDualSubgrad.Stoch

variable {E Ξ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Exact SSA state (x_n,s_n) on a history of length n; p.26, (6.3).
The previous state sees only the prefix of length n, then the last sample is queried. -/
noncomputable def historyState (π : ℝ → StrongDual ℝ E → E) (γ : ℝ) (x0 : E)
    (a : E → Ξ → StrongDual ℝ E) : (n : ℕ) → (Fin n → Ξ) → E × StrongDual ℝ E
  | 0, _ => (x0, 0)
  | n + 1, h =>
    let prev := historyState π γ x0 a n (fun i => h i.castSucc)
    let s := prev.2 + a prev.1 (h (Fin.last n))
    (π (γ * betaHat (n + 1)) (-s), s)

/-- The point at time n uses precisely the first n observations of the path. -/
noncomputable def pathPoint (π : ℝ → StrongDual ℝ E → E) (γ : ℝ) (x0 : E)
    (a : E → Ξ → StrongDual ℝ E) (ω : ℕ → Ξ) (n : ℕ) : E :=
  (historyState π γ x0 a n (fun i => ω i.val)).1

/-- The answer queried at time n, before the next state is computed. -/
noncomputable def pathAnswer (π : ℝ → StrongDual ℝ E → E) (γ : ℝ) (x0 : E)
    (a : E → Ξ → StrongDual ℝ E) (ω : ℕ → Ξ) (n : ℕ) : StrongDual ℝ E :=
  a (pathPoint π γ x0 a ω n) (ω n)

/-- Extension of a nonempty finite history. Unused observations are filled with h(0). -/
def padHistory {k : ℕ} (h : Fin (k + 1) → Ξ) : ℕ → Ξ :=
  fun i => if hi : i < k + 1 then h ⟨i, hi⟩ else h 0

/-- The source's arithmetic average includes x_0 through x_k, never x_{k+1}. -/
noncomputable def pathAverage (π : ℝ → StrongDual ℝ E → E) (γ : ℝ) (x0 : E)
    (a : E → Ξ → StrongDual ℝ E) (ω : ℕ → Ξ) (k : ℕ) : E :=
  (1 / ((k : ℝ) + 1)) • ∑ i ∈ range (k + 1), pathPoint π γ x0 a ω i

/-- Gap (6.4), using exactly the published level-set gap with unit weights. -/
noncomputable def pathGap (Q : Set E) (d : E → ℝ)
    (π : ℝ → StrongDual ℝ E → E) (γ : ℝ) (x0 : E)
    (a : E → Ξ → StrongDual ℝ E) (ω : ℕ → Ξ) (k : ℕ) (D : ℝ) : ℝ :=
  gap Q d (pathAnswer π γ x0 a ω) (pathPoint π γ x0 a ω) k D

end NesterovSSAAudit.SSA


