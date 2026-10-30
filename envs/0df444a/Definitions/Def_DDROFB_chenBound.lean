-- Prove2me | Definitions.Def_DDROFB_chenBound
-- name    : DDROFB_chenBound
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:05:58.053683+00:00
-- url     : https://prove2.me/theorems/306ec1a2-a317-4177-b982-d2977bf6fb94
-- title:
--   Right-hand side of the Chen–Sim–Sun deviation bound (22)
-- statement:
--   Let $\mathbb P$ be a probability measure on $\mathbb R^d$ with marginals $\mathbb P_i$, let $\epsilon \in \mathbb R$ and $v \in \mathbb R^d$. The right-hand side of the deviation bound (22) is
--
--   $$
--   \sum_{i=1}^d \mathbb E^{\mathbb P}[\tilde u_i]\, v_i \;+\; \sqrt{2\log(1/\epsilon)\Bigl(\sum_{i : v_i < 0} \sigma_b(\mathbb P_i)^2 v_i^2 + \sum_{i : v_i \ge 0} \sigma_f(\mathbb P_i)^2 v_i^2\Bigr)} .
--   $$
--
--   For independent components with finite deviations it bounds $\mathrm{VaR}^{\mathbb P}_\epsilon(v)$; its worst case over $\mathcal P^{FB}$ is the support function (24) of $\mathcal U^{FB}_\epsilon$.
--
--   **Formalization Note** The two sums are one sum with a case split on the sign of $v_i$, as printed. The extended-real deviations are converted to reals; the mission evaluates the expression only at measures whose deviations are finite, where this conversion is exact.
-- source:
--   Bertsimas, Gupta, Kallus, Data-Driven Robust Optimization, arXiv:1401.0212v2, eq. (22), p. 18

import Mathlib
import Definitions.Def_DDROFB_fwdDev
import Definitions.Def_DDROFB_bwdDev
import Definitions.Def_DDROFB_marginal
open MeasureTheory

namespace DDROFB

/-- **The right-hand side of the Chen–Sim–Sun bound (22).**
Bertsimas, Gupta, Kallus, Data-Driven Robust Optimization, arXiv:1401.0212v2, eq. (22), p. 18:
"`VaR^P_ϵ(v) ≤ Σ_{i=1}^d E^P[ũ_i] v_i + √(2 log(1/ϵ) (Σ_{i:v_i<0} σ²_{bi}(P) v²_i +
Σ_{i:v_i≥0} σ²_{fi}(P) v²_i))`."

`chenBound P ε v` is
`Σ_i E^P[ũ_i] v_i + √(2 log(1/ε) · Σ_i (σ_b(P_i)² if v_i < 0, σ_f(P_i)² if v_i ≥ 0) v_i²)`.

**Formalization Note.** The two sums are one sum with an `if` on the sign of `v_i`, using the
printed split (`v_i < 0` → backward deviation). The deviations are `ℝ≥0∞`-valued and converted
with `toReal`; every statement of the mission evaluates `chenBound` only at measures whose
deviations are finite (the hypothesis of (22), or membership of `P^FB`), so `toReal` never maps
`⊤` to `0` there. Means are Bochner integrals, integrable in the same situations. -/
noncomputable def chenBound {d : ℕ} (P : Measure (EuclideanSpace ℝ (Fin d))) (ε : ℝ)
    (v : EuclideanSpace ℝ (Fin d)) : ℝ :=
  ∑ i, (∫ u, u i ∂P) * v i +
    Real.sqrt (2 * Real.log (1 / ε) *
      ∑ i, (if v i < 0 then (bwdDev (marginal P i)).toReal ^ 2
        else (fwdDev (marginal P i)).toReal ^ 2) * v i ^ 2)

end DDROFB


