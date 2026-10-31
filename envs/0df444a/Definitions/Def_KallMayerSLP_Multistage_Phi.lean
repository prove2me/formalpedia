-- Prove2me | Definitions.Def_KallMayerSLP_Multistage_Phi
-- name    : KallMayerSLP_Multistage_Phi
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:16:49.516692+00:00
-- url     : https://prove2.me/theorems/381eaf55-1a2b-4ff6-a655-6fed9d64ef55
-- title:
--   Expected cost-to-go $\Phi_t$ of (3.15)
-- statement:
--   The expected cost-to-go is defined by $\Phi_{T+1}\equiv0$ and, for $t=T,\dots,2$,
--   $$
--   \Phi_t(z_{t-1};\widehat\zeta_{t-1})=\mathbb E_{\xi_t}\big[r_t(z_{t-1};\widehat\zeta_{t-1},\xi_t)\big].
--   $$
--
--   **Formalization Note** Extended-real valued: Assumption 3.2 does not make the recourse problems bounded, so $r_t$ may be $-\infty$. The expectation is the published `WassersteinDRO.Duality.erealExpectation`. The realization is a full family, of which $\Phi_t$ uses the coordinates $s<t$.
-- source:
--   Kall & Mayer, Stochastic Linear Programming: Models, Theory, and Computation (Kluwer/Springer 2005), Chapter 3, (3.15), p.263 (PDF 272)

import Mathlib
import Definitions.Def_KallMayerSLP_Multistage_phiAux

namespace KallMayerSLP.Multistage

open MeasureTheory

/-- The expected cost-to-go `Φ_t(z_{t-1}; ζ̂_{t-1})` of the recursion (3.15) (Kall & Mayer,
*Stochastic Linear Programming* (2005), Chapter 3, (3.15), p.263, PDF 272), for `t = 2, …, T + 1`:
`Φ_{T+1} ≡ 0` and `Φ_t(z_{t-1}; ζ̂_{t-1}) = 𝔼_{ξ_t}[r_t(z_{t-1}; ζ̂_{t-1}, ξ_t)]`, with `μ t` the law
`ℙ_{ξ_t}`.

**Formalization Note.** Valued in `EReal`, because under Assumption 3.2 alone `r_t` may be
`-∞`: Assumption 3.2 does not make the recourse problems bounded. The expectation of an
`EReal`-valued function is the published `WassersteinDRO.Duality.erealExpectation` (`+∞` when the
positive part has infinite integral, otherwise `∫ f⁺ − ∫ f⁻`); for the functions here it is a
genuine expectation, since `r_t` is either identically `-∞` or finite, convex and hence bounded on
the bounded interval `Ξ^t`. `w` is a full family of realizations, of which `Phi D μ t` uses the
coordinates `s < t` (its coordinate `t` is integrated out, its later coordinates are unused). -/
noncomputable def Phi (D : MSLP) (μ : ∀ t, Measure (Fin (D.r t) → ℝ)) (t : ℕ)
    (z : ∀ τ, Fin (D.n τ) → ℝ) (w : ∀ s, Fin (D.r s) → ℝ) : EReal :=
  phiAux D μ (D.T + 1 - t) z w

end KallMayerSLP.Multistage


