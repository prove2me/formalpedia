-- Prove2me | Definitions.Def_KuhnWass2019_Reformulation_worstCaseRisk
-- name    : KuhnWass2019_Reformulation_worstCaseRisk
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T03:14:43.698197+00:00
-- url     : https://prove2.me/theorems/a60edd81-a083-4537-9e8d-a24c002ddef5
-- title:
--   Extended worst-case risk over a finite-order Wasserstein ball
-- statement:
--   For $p\ge1$ and $\varepsilon\ge0$, $R_{\varepsilon,p}(P_N,\ell)=\sup_{Q\in B_{\varepsilon,p}(P_N)} E_Q[\ell]$. The published ball uses all probability measures supported on $\Xi$ and the coupling definition of $W_p$. The published extended expectation returns $+\infty$ when its positive-part integral is infinite, even if the negative part also has infinite integral. An empty supremum is $-\infty$.
-- source:
--   Kuhn, Mohajerin Esfahani, Nguyen and Shafieezadeh-Abadeh, Wasserstein Distributionally Robust Optimization: Theory and Applications in Machine Learning, arXiv:1908.08729v2 (4 Nov 2024), pp. 2–3 and 6, equations (5)–(6)

import Mathlib
import Definitions.Def_WassersteinDRO_Duality_ambiguitySet
import Definitions.Def_DupacovaWets_Consistency_expect

open MeasureTheory
open scoped ENNReal Classical

namespace KuhnWass2019.Reformulation

/-- Equation (6), for extended losses, with the p. 2 expectation convention. -/
noncomputable def worstCaseRisk {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E]
    (ε p : ℝ) (Ξ : Set E) (PN : Measure E) (ℓ : E → EReal) : EReal :=
  ⨆ Q ∈ WassersteinDRO.Duality.ambiguitySet ε p Ξ PN,
    DupacovaWets.Consistency.expect Q ℓ

end KuhnWass2019.Reformulation


