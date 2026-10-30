-- Prove2me | Definitions.Def_WassersteinDRO_ConvexLossP1_worstCaseRisk
-- name    : WassersteinDRO_ConvexLossP1_worstCaseRisk
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T02:50:30.013494+00:00
-- url     : https://prove2.me/theorems/9369e8fe-14af-4e49-9d9e-6b189d794f9e
-- title:
--   Worst-case risk $\mathcal R_{\varepsilon,p}(\mathbb P, \ell)$
-- statement:
--   With the notation of the ambiguity set and the risk, the **worst-case risk** of a loss $\ell : E \to [-\infty, +\infty]$ is
--   $$\mathcal R_{\varepsilon,p}(\mathbb P, \ell) = \sup_{\mathbb Q \in \mathbb B_{\varepsilon,p}(\mathbb P)} \mathcal R(\mathbb Q, \ell) \in [-\infty, +\infty].$$
--
--   This is problem (6) of the paper: the largest risk over all distributions within Wasserstein distance $\varepsilon$ of the nominal distribution.
--
--   **Formalization Note** The supremum is taken in the complete lattice $[-\infty, +\infty]$; it equals $-\infty$ only when the ball is empty. It ranges over all Borel probability measures in the ball, not only discrete ones.
-- source:
--   Kuhn, Mohajerin Esfahani, Nguyen, Shafieezadeh-Abadeh, Wasserstein Distributionally Robust Optimization: Theory and Applications in Machine Learning, arXiv:1908.08729v2, eq. (6), p. 6

import Mathlib
import Definitions.Def_WassersteinDRO_ConvexLossP1_ambiguityBall
import Definitions.Def_WassersteinDRO_ConvexLossP1_risk

open MeasureTheory

namespace WassersteinDRO.ConvexLossP1

/-- **The worst-case risk `R_{ε,p}(P, ℓ)`.**
Kuhn, Mohajerin Esfahani, Nguyen, Shafieezadeh-Abadeh, *Wasserstein Distributionally Robust Optimization: Theory and Applications in Machine Learning*, arXiv:1908.08729v2, eq. (6), p. 6: "Using the proposed ambiguity set, we define the worst-case risk as
R_{ε,p}(P̂N, ℓ) = sup_{Q∈B_{ε,p}(P̂N)} R(Q, ℓ)."

`worstCaseRisk ε p P Ξ ℓ` is the supremum of `risk Q ℓ` over all `Q` in `ambiguityBall ε p P Ξ`.

**Formalization Note.** The supremum is taken in the complete lattice `EReal = [−∞, ∞]`, so it
always exists; it is `−∞` only if the ball is empty. It ranges over every Borel probability
measure in the ball, not only over discrete ones. -/
noncomputable def worstCaseRisk {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E]
    (ε p : ℝ) (P : Measure E) (Ξ : Set E) (ℓ : E → EReal) : EReal :=
  ⨆ Q ∈ ambiguityBall ε p P Ξ, risk Q ℓ

end WassersteinDRO.ConvexLossP1


