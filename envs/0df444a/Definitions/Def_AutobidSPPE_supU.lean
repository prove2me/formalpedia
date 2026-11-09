-- Prove2me | Definitions.Def_AutobidSPPE_supU
-- name    : AutobidSPPE_supU
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:56:57.501429+00:00
-- url     : https://prove2.me/theorems/f805c8b1-f47f-45a7-8b11-bda16329b326
-- title:
--   $U=\max_i\hat v_i$
-- statement:
--   Given certified support upper bounds $\hat v_i\ge\bar v_i$, set
--   $$
--   U=\max_i \hat v_i .
--   $$
--
--   **Formalization Note** The maximum over the bidders is a supremum over `Fin n`, which is the maximum for $n\ge1$; all theorems assume $n\ge2$.
-- source:
--   Chen–Morgenstern–Yang, Convergent Dynamics in Second Price Autobidding Games, STOC 2027 submission (manuscript sha256 185cb93f…77659a6), (10), p.11

import Mathlib

namespace AutobidSPPE

/-- `U = maxᵢ v̂ᵢ`, the largest certified support upper bound (Chen–Morgenstern–Yang, *Convergent Dynamics in Second Price Autobidding Games*, STOC 2027 submission manuscript (sha256 185cb93f…77659a6), (10), p.11).

**Formalization Note** The maximum over `Fin n` is `⨆ i`; it is the maximum for `n ≥ 1` (all
theorems assume `n ≥ 2`). -/
noncomputable def supU {n : ℕ} (vhat : Fin n → ℝ) : ℝ := ⨆ i, vhat i

end AutobidSPPE


