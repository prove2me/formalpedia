-- Prove2me | Definitions.Def_ShapleyNV_worstCase
-- name    : ShapleyNV_worstCase
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:52:16.404288+00:00
-- url     : https://prove2.me/theorems/bf0ab8b6-e87c-43f4-84e2-2cc1d54d79ab
-- title:
--   Worst-case expectation over a Wasserstein ball
-- statement:
--   Given a ground cost $c$, a nominal distribution $\widehat{\mathbb P}$, a radius $\rho$ and a loss $\ell \ge 0$, the worst-case expected loss is
--
--   $$
--   \sup\Big\{ \mathbb E_{\mathbb P}[\ell(\xi)] \;:\; \mathbb P \in \mathcal P_1,\ W_c(\mathbb P, \widehat{\mathbb P}) \le \rho \Big\},
--   $$
--
--   where the supremum is over **every** probability measure $\mathbb P$ with finite first moment whose transport cost to $\widehat{\mathbb P}$ is at most $\rho$.
--
--   This is the inner supremum of (P) and of $(\widehat{\mathrm P})$, and the inner primal value $v_P^f$ of Lemma EC.1.
--
--   **Formalization Note** The value lies in $[0, \infty]$ and may be $+\infty$. The loss enters through its nonnegative part, which is the loss itself for the newsvendor costs of this mission. For $\rho \ge 0$ the nominal distribution belongs to the ball, so the supremum is never over an empty set.
-- source:
--   Zhang, Yang, Gao, Optimal Robust Policy for Feature-Based Newsvendor (author manuscript, 2022-10-17), §2.2, inner supremum of (P), p.6; Theorem 1, (P̂), p.6; Lemma EC.1, v_P^f, p.ec1 (PDF 22)

import Mathlib
import Definitions.Def_ShapleyNV_FirstMoment
import Definitions.Def_ShapleyNV_transportCost

open MeasureTheory NNReal ENNReal

namespace ShapleyNV

/-- **Worst-case expected loss over a Wasserstein ball**:
`sup { E_P[ℓ(ξ)] : P ∈ 𝒫₁, W_c(P, P̂) ≤ ρ }`.
Zhang, Yang, Gao, *Optimal Robust Policy for Feature-Based Newsvendor* (author manuscript, 2022-10-17), §2.2, the inner supremum of (P), p.6, and of (P̂), p.6; Lemma EC.1, `v_P^f`, p.ec1 (PDF 22).

The supremum ranges over **every** probability measure `P` with finite first moment (for `c`)
whose transport cost to the nominal distribution is at most `ρ`.

**Formalization Note.** Values are in `ℝ≥0∞`: the worst case may be `+∞` (p.ec1). The losses used
in this mission are newsvendor costs, which are nonnegative under the standing assumption
`h, b ≥ 0`, so `ENNReal.ofReal` loses nothing. The ball always contains the nominal distribution
when `ρ ≥ 0`, so the supremum is not the junk value of an empty set. -/
noncomputable def worstCase {α : Type*} [MeasurableSpace α] (c : α → α → ℝ) (Phat : Measure α) (ρ : ℝ)
    (ℓ : α → ℝ) : ℝ≥0∞ :=
  ⨆ P ∈ {P : Measure α | IsProbabilityMeasure P ∧ FirstMoment c P ∧
      transportCost c P Phat ≤ ENNReal.ofReal ρ}, ∫⁻ ξ, ENNReal.ofReal (ℓ ξ) ∂P

end ShapleyNV


