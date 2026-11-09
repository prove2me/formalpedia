-- Prove2me | Definitions.Def_GevreyGibbsSep_GibbsClass
-- name    : GevreyGibbsSep_GibbsClass
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T16:38:15.132359+00:00
-- url     : https://prove2.me/theorems/62d7e122-a0cf-4cd4-aadd-efc5bdcaa11c
-- title:
--   Definition 2 — the $s$-Gevrey potential class $\mathscr W^s(\alpha,\xi,\rho)$
-- statement:
--   For $s\ge1$, $\alpha\ge1$ and $\xi,\rho>0$, the **$s$-Gevrey potential class** is the family of Gibbs states
--   $$\mathscr W^s(\alpha,\xi,\rho)=\Big\{p=e^{-\beta E}/Z\ :\ [\beta E]_{s,\rho}\le\xi\ \text{ and }\ \beta\Delta\le\log\alpha\Big\},\qquad \Delta=\max E-\min E .$$
--   The first condition is smoothness (Definition 1), the second bounds the **barrier amplitude** $e^{\beta\Delta}\le\alpha$, the worst-case ratio of density values.
--
--   **Formalization Note** A member is recorded by its scaled potential $V=\beta E$, a $2\pi$-periodic $C^\infty$ function; its Gibbs state is $e^{-V}/Z_V$. The barrier condition is written $V(x)-V(y)\le\log\alpha$ for all $x,y$. The ranges $s\ge1$, $\alpha\ge1$, $\xi,\rho>0$ are hypotheses of the theorems.
-- source:
--   Olivucci, Sobchuk, Hoque, Hnybida, Kim, Shayeghi, Ronagh, Provable Quantum–Classical Separation for Continuous Gibbs Sampling, arXiv:2608.24527 (held version, sha256 d4fd40eb…), Definition 2, Eq. (5), p.6; Eq. (4), p.5

import Mathlib
import Definitions.Def_GevreyGibbsSep_IsPeriodicSmooth
import Definitions.Def_GevreyGibbsSep_InDotGevrey
import Definitions.Def_GevreyGibbsSep_gibbs

open MeasureTheory
open scoped ENNReal InnerProductSpace

namespace GevreyGibbsSep

/-- Definition 2 (s-Gevrey potential class), arXiv:2608.24527 (sha256 d4fd40eb…), Eq. (5), p.6:
`W^s(α, ξ, ρ) = {p = e^{−βE}/Z : [βE]_{s,ρ} ≤ ξ and β∆ ≤ log α}`, `∆ = max E − min E`.

**Formalization Note** A member is recorded by its scaled potential `V = βE`, a `2π`-periodic
`C^∞` function on `ℝ^d`; the Gibbs state is `gibbs V`. The barrier condition `β∆ ≤ log α` is
written `V x − V y ≤ log α` for all `x, y`. The paper's standing ranges `s ≥ 1`, `α ≥ 1`,
`ξ, ρ > 0` are hypotheses of the theorems that use the class, not part of the set. -/
def GibbsClass (d : ℕ) (s α ξ ρ : ℝ) : Set ((Fin d → ℝ) → ℝ) :=
  {V | IsPeriodicSmooth V ∧ InDotGevrey s ξ ρ V ∧ ∀ x y, V x - V y ≤ Real.log α}

end GevreyGibbsSep


