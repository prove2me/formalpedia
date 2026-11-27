-- Prove2me | Definitions.Def_BauerleRiederMDP_LQ_Supplement_TradeExec_Top
-- name    : BauerleRiederMDP_LQ_Supplement_TradeExec_Top
-- status  : Definition
-- author  : @iris
-- created : 2026-11-26T23:38:55.105823+00:00
-- url     : https://prove2.me/theorems/6c503809-a2bc-4cea-8733-7efb38e1763a
-- title:
--   The dynamic programming operator $T$ of the trade execution problem
-- statement:
--   **The dynamic programming operator $T$ of the trade execution problem** (Bäuerle & Rieder, *Markov Decision Processes with Applications to Finance* (2011), §9.4, p.295, PDF 305): $(T v)(t, x) = \int _0^{T-t} \lambda  e^{-\lambda s} \min _{u \in  {0,\dots ,x}} {C(u) + v(t + s, x - u)} ds + e^{-\lambda (T-t)} C(x)$.
--
--   **Formalization Note.** The minimum over the finite set ${0, \dots , x}$ is `Finset.inf'` (nonempty); the integral is an interval integral, of a bounded measurable function for $v \in  IB_b$.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), §9.4, p.295, PDF 305

import Mathlib
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_TradeExec

open MeasureTheory

namespace BauerleRiederMDP.LQ.Supplement

/-- **The dynamic programming operator `T` of the trade execution problem** (Bäuerle & Rieder,
*Markov Decision Processes with Applications to Finance* (2011), §9.4, p.295, PDF 305):
`(T v)(t, x) = ∫_0^{T−t} λ e^{−λs} min_{u ∈ {0,…,x}} {C(u) + v(t + s, x − u)} ds + e^{−λ(T−t)} C(x)`.

**Formalization Note.** The minimum over the finite set `{0, …, x}` is `Finset.inf'` (nonempty);
the integral is an interval integral, of a bounded measurable function for `v ∈ IB_b`. -/
noncomputable def TradeExec.Top (P : TradeExec) (v : ℝ × ℕ → ℝ) (p : ℝ × ℕ) : ℝ :=
  (∫ s in (0 : ℝ)..(P.T - p.1), P.lam * Real.exp (-P.lam * s) *
      (Finset.range (p.2 + 1)).inf' Finset.nonempty_range_add_one
        (fun u => P.C u + v (p.1 + s, p.2 - u))) +
    Real.exp (-P.lam * (P.T - p.1)) * P.C p.2

end BauerleRiederMDP.LQ.Supplement


