-- Prove2me | Definitions.Def_BauerleRiederMDP_Contracting_Treal
-- name    : BauerleRiederMDP_Contracting_Treal
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:27:45.98852+00:00
-- url     : https://prove2.me/theorems/c8cea7e8-9bfc-4fad-80b9-cc3de37da71a
-- title:
--   The maximal reward operator $\mathcal T$ on real-valued functions
-- statement:
--   For a stationary Markov Decision Model $(E,A,D,Q,r,\beta)$ and a real function $v:E\to\mathbb R$, the **maximal reward operator** is
--
--   $$\mathcal Tv(x)=\sup_{a\in D(x)}\Big\{r(x,a)+\beta\int v(x')\,Q(dx'\mid x,a)\Big\},\qquad x\in E .$$
--
--   This definition returns $\mathcal Tv$ as a real-valued function, so that iterates $\mathcal T^n g$ can be formed. When $b$ is a bounding function and $v\in\mathbb B_b$, the supremum is finite: $D(x)$ is nonempty and $|r(x,a)+\beta\int v\,dQ|\le (c_r+\beta c\,\alpha_b)\,b(x)$ on $D$.
--
--   **Formalization Note** The supremum is the published `EReal`-valued operator `MDPFinance.Contracting.T` (actions outside $D(x)$ contribute $-\infty$), converted back to $\mathbb R$. The conversion is exact whenever $\mathcal Tv$ is finite. It is not the platform's real operator `T'`, whose real supremum gives the value $0$ to actions outside $D(x)$.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), Springer Universitext, DOI 10.1007/978-3-642-18324-9, Structure Assumption (SA) (ii), p.199 (PDF p.210); Theorem 7.3.5 d), p.207 (PDF p.218)

import Mathlib
import Definitions.Def_MDPFinance_Contracting_Model

open MeasureTheory ProbabilityTheory

namespace BauerleRiederMDP.Contracting

open MDPFinance.Contracting

variable {E A : Type*} [MeasurableSpace E] [MeasurableSpace A]

/-- The maximal reward operator `T` of Bäuerle & Rieder, *Markov Decision Processes with
Applications to Finance* (2011), p.199, PDF p.210,
`T v(x) = sup_{a ∈ D(x)} { r(x,a) + β ∫ v(x') Q(dx'|x,a) }`,
read on real-valued functions `v : E → ℝ` and returned as a real-valued function, so that the
iterates `T^n g` of Theorem 7.3.5 d) can be written.

**Formalization Note.** This is the published `EReal`-valued operator
`MDPFinance.Contracting.T` (a supremum over the subtype-like binder `a ∈ D(x)`, which in `EReal`
contributes `⊥`, not `0`, for actions outside `D(x)`), applied to `v` cast to `EReal`, then
converted back with `EReal.toReal`. The conversion is exact whenever `T v` is real-valued; for
a bounding function `b` and `v ∈ IB_b` this always holds (`D(x) ≠ ∅` and
`|r(x,a) + β∫v dQ| ≤ (c_r + β c α_b) b(x)` on `D`). It is **not** the platform's real operator
`MDPFinance.Contracting.T'`, whose real `⨆ a ∈ D(x)` returns `0` on actions outside `D(x)`. -/
noncomputable def Treal (M : MarkovDecisionModel E A) (v : E → ℝ) (x : E) : ℝ :=
  (T M (fun y => (v y : EReal)) x).toReal

end BauerleRiederMDP.Contracting


