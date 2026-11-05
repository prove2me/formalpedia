-- Prove2me | Definitions.Def_BauerleRiederMDP_AmericanPut_BinomialMarket_exerciseValue
-- name    : BauerleRiederMDP_AmericanPut_BinomialMarket_exerciseValue
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:32:36.655848+00:00
-- url     : https://prove2.me/theorems/b7389df4-1bbe-437d-b0cf-9a3b64c7419e
-- title:
--   Value $J_f=\lim_{n\to\infty}\mathcal T_f^n0$ of a stationary exercise rule
-- statement:
--   For the exercise rule $f=1_A$,
--   $$J_f(x):=\lim_{n\to\infty}\big(\mathcal T_f^n0\big)(x).$$
--
--   **Formalization Note** The limit is Mathlib's `limUnder` of the real sequence $n\mapsto(\mathcal T_f^n0)(x)$. For $x\ge0$ this sequence is increasing and bounded by $K$, so the limit exists and `limUnder` returns it.
-- source:
--   N. Bäuerle and U. Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, Theorem 11.1.3 d), p.337, PDF 345

import Mathlib
import Definitions.Def_BauerleRiederMDP_AmericanPut_BinomialMarket_exerciseT

open Filter

namespace BauerleRiederMDP.AmericanPut

/-- The **value `J_f := lim_{n→∞} 𝒯_f^n 0` of the stationary exercise rule `f = 1_A`** (Bäuerle & Rieder,
Markov Decision Processes with Applications to Finance (2011), Theorem 11.1.3 d), p.337, PDF 345:
`J_{f*} := lim_{n→∞} 𝒯^n_{f*} 0`).

**Formalization Note.** The limit is Mathlib's `limUnder atTop` of the real sequence `n ↦ (𝒯_f^n 0)(x)`. On
`E = ℝ₊` this sequence is increasing (`𝒯_f` is monotone and `𝒯_f 0 ≥ 0`) and bounded by `K`, so the limit
exists and `limUnder` returns it; `limUnder` would return an arbitrary value only for a divergent sequence,
which does not occur at `x ≥ 0`. -/
noncomputable def BinomialMarket.exerciseValue (M : BinomialMarket) (K : ℝ) (A : Set ℝ) (x : ℝ) : ℝ :=
  limUnder atTop (fun n : ℕ => ((M.exerciseT K A)^[n] (fun _ => 0)) x)

end BauerleRiederMDP.AmericanPut


