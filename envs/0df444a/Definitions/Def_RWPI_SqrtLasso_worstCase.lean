-- Prove2me | Definitions.Def_RWPI_SqrtLasso_worstCase
-- name    : RWPI_SqrtLasso_worstCase
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T09:45:42.222385+00:00
-- url     : https://prove2.me/theorems/c2b09651-3533-4f78-acc6-ae77ef3e92a1
-- title:
--   Worst-case expected loss $\sup_{P:\,D_c(P,P_n)\le\delta} E_P[l]$ (the inner problem of (8))
-- statement:
--   Let $Z$ be a measurable space, $c : Z\times Z\to[0,\infty]$ a cost, $P_n$ a probability measure on $Z$ (in the paper, the empirical distribution of the training data), $\delta \ge 0$ a radius and $l : Z \to \mathbb R$ a loss function. The **worst-case expected loss** over the optimal-transport ball of radius $\delta$ around $P_n$ is
--
--   $$
--   \sup_{P :\, D_c(P, P_n) \le \delta} \mathbb E_P\big[l(X,Y)\big],
--   $$
--
--   the supremum over all probability measures $P$ on $Z$ whose optimal transport cost $D_c(P,P_n)$ (Eq. (7)) to $P_n$ is at most $\delta$. This is the inner supremum of the distributionally robust optimization problem (8), $\inf_\beta \sup_{P: D_c(P,P_n)\le\delta} \mathbb E_P[l(X,Y;\beta)]$; the regression parameter $\beta$ enters through the loss.
--
--   **Formalization Note** The value lies in $[0,\infty]$. The expectation is the lower Lebesgue integral of $\max(l,0)$, which equals $\mathbb E_P[l]$ for the nonnegative losses of the paper (square loss) and may be $+\infty$; there is no integrability side condition that could silently exclude measures from the ball. The supremum is taken in $[0,\infty]$ over the measures `P` with `IsProbabilityMeasure P` and $D_c(P,P_n) \le \delta$.
-- source:
--   Blanchet, Kang & Murthy, Robust Wasserstein Profile Inference and Applications to Machine Learning, arXiv:1610.05627v4, p. 9, §2.2, Eq. (8) (inner supremum); p. 8, Eq. (7)

import Mathlib
import Definitions.Def_RWPI_SqrtLasso_transportCost

open MeasureTheory

namespace RWPI.SqrtLasso

/-- The worst-case expected loss over the optimal-transport ball of radius `δ` around `Pn`,
the inner supremum of the DRO problem (8), p. 9:
`sup_{P : D_c(P, Pn) ≤ δ} E_P[l(X, Y)]`.
`P` ranges over all probability measures on `Z` with `D_c(P, Pn) ≤ δ`; the loss `l` is real
valued and its expectation is taken as the lower Lebesgue integral of `max (l, 0)`, which is the
expectation for the nonnegative losses of the paper (and may be `⊤`). -/
noncomputable def worstCase {Z : Type*} [MeasurableSpace Z] (c : Z → Z → ENNReal) (δ : ℝ)
    (Pn : Measure Z) (l : Z → ℝ) : ENNReal :=
  ⨆ (P : Measure Z) (_ : IsProbabilityMeasure P ∧ transportCost c P Pn ≤ ENNReal.ofReal δ),
    ∫⁻ z, ENNReal.ofReal (l z) ∂P

end RWPI.SqrtLasso


