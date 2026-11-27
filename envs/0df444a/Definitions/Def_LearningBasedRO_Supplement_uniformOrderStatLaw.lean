-- Prove2me | Definitions.Def_LearningBasedRO_Supplement_uniformOrderStatLaw
-- name    : LearningBasedRO_Supplement_uniformOrderStatLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T02:15:10.787803+00:00
-- url     : https://prove2.me/theorems/85bde158-5152-5be9-9421-d2eeb94c73af
-- title:
--   The law of $U_{(r)}$, the $r$-th order statistic of $n$ i.i.d. uniform variables on $[0,1]$
-- statement:
--   Let $U_1,\dots,U_n$ be i.i.d. uniform random variables on $[0,1]$ and $1\le r\le n$. Write $U_{(r)}$ for the $r$-th ranked variable, the $r$-th smallest of $U_1,\dots,U_n$. This module defines the law of $U_{(r)}$ as a probability measure on $\mathbb R$:
--   $$\mathcal L\big(U_{(r)}\big)=\big(\mathrm{Unif}[0,1]^{\otimes n}\big)\circ\big(u\mapsto u_{(r)}\big)^{-1}.$$
--
--   It is the law to which (6) compares the coverage $P(\xi\in U)$ of the learned uncertainty set, conditional on $D_1$.
--
--   **Formalization Note** The uniform law on $[0,1]$ is Lebesgue measure restricted to $[0,1]$; $u_{(r)}$ is the base mission's `orderStat` (1-based rank, ties kept, junk value $0$ outside $1\le r\le n$).
-- source:
--   Hong–Huang–Lam, arXiv:1704.04342v2, (6) and the sentence after it, p.10

import Mathlib
import Definitions.Def_LearningBasedRO_Model

open MeasureTheory

namespace LearningBasedRO.Supplement

/-- The law of `U₍ᵣ₎`, the `r`-th ranked variable (the `r`-th smallest, `1 ≤ r ≤ n`) among `n`
i.i.d. uniform variables on `[0,1]`: the push-forward of the product of `n` copies of the uniform
law on `[0,1]` under `u ↦ u₍ᵣ₎`.
Hong–Huang–Lam, arXiv:1704.04342v2, text after (6), p.10.

**Formalization Note** The uniform law on `[0,1]` is Lebesgue measure restricted to `[0,1]`.
`u₍ᵣ₎` is the base `orderStat` (1-based rank, ties kept, junk `0` outside `1 ≤ r ≤ n`). -/
noncomputable def uniformOrderStatLaw (n r : ℕ) : Measure ℝ :=
  (Measure.pi fun _ : Fin n => (volume : Measure ℝ).restrict (Set.Icc 0 1)).map
    (fun u => orderStat u r)

end LearningBasedRO.Supplement


