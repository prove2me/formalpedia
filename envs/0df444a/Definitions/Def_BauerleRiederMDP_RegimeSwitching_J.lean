-- Prove2me | Definitions.Def_BauerleRiederMDP_RegimeSwitching_J
-- name    : BauerleRiederMDP_RegimeSwitching_J
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:27:41.319046+00:00
-- url     : https://prove2.me/theorems/8c31eb0d-9911-485f-a267-76d3180573ad
-- title:
--   Value functions $J_n(x,j)$ of the regime-switching consumption-investment problem
-- statement:
--   The **value functions** of the consumption-investment problem with regime switching are
--
--   $$
--   J_n(x,j)=\sup_\pi\ \mathbb E^\pi_{xj}\Big[\sum_{k=0}^{n-1}\beta^kU_c\big(c_k(X_k,Y_k)\big)+\beta^nU_p(X_n)\Big],\qquad (x,j)\in[0,\infty)\times E_Y,
--   $$
--
--   the supremum over all admissible Markov policies $\pi=(f_0,\dots,f_{n-1})$, $f_k(x,j)=(c_k(x,j),a_k(x,j))\in D(x,j)$: the maximal expected discounted utility of consumption and terminal wealth over $n$ periods.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), §4.4, p.102 (PDF p.116)

import Mathlib
import Definitions.Def_BauerleRiederMDP_RegimeSwitching_valueFunction
import Definitions.Def_BauerleRiederMDP_RegimeSwitching_regimeModel
open MeasureTheory
open scoped NNReal

namespace BauerleRiederMDP.RegimeSwitching

/-- The **value functions of the regime-switching consumption-investment problem**
(Bäuerle & Rieder, *Markov Decision Processes with Applications to Finance* (2011), §4.4, p.102, PDF p.116):
`J_n(x, j) = sup_π 𝔼^π_{xj}[∑_{k=0}^{n-1} β^k U_c(c_k(X_k, Y_k)) + β^n U_p(X_n)]`,
the supremum over all admissible Markov policies `π = (f_0, …, f_{n-1})`,
`f_k(x, j) = (c_k(x, j), a_k(x, j)) ∈ D(x, j)`.

**Formalization Note.** `J … n x j = valueFunction (regimeModel M i β Uc) g n 0 (x, j)` with
terminal reward `g(x, j) = β^n U_p(x)`: the `n`-stage problem started at time `0`. Values in
`EReal`. -/
noncomputable def J {EY : Type*} [Fintype EY] [MeasurableSpace EY] [DiscreteMeasurableSpace EY]
    {d : ℕ} (M : RegimeMarket EY d) (i β : ℝ) (Uc Up : ℝ → ℝ) (n : ℕ) (x : ℝ≥0) (j : EY) : EReal :=
  valueFunction (regimeModel M i β Uc) (fun s => β ^ n * Up s.1) n 0 (x, j)

end BauerleRiederMDP.RegimeSwitching


