-- Prove2me | Definitions.Def_PrettyGoodShadow_laplaceRisk
-- name    : PrettyGoodShadow_laplaceRisk
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:23:57.690195+00:00
-- url     : https://prove2.me/theorems/3507aa13-a6e9-48f3-bd38-1d37eb354493
-- title:
--   Binary relative entropy and the risk of the Laplace estimator
-- statement:
--   For $\theta\in[0,1]$ and $a\in(0,1)$, the binary relative entropy in nats is
--
--   $$
--   D(\mathrm{Ber}(\theta)\|\mathrm{Ber}(a))=\theta\log\frac{\theta}{a}+(1-\theta)\log\frac{1-\theta}{1-a}.
--   $$
--
--   The risk of the Laplace estimator $\hat\theta_m=(z_1+\dots+z_m+1)/(m+2)$ on $m$ samples $z_i\sim\mathrm{Ber}(\theta)$ is $\mathbb E_z\,D(\mathrm{Ber}(\theta)\|\mathrm{Ber}(\hat\theta_m))$.
--
--   **Formalization Note** A term with $\theta=0$ or $1-\theta=0$ vanishes, as in the convention $0\log0=0$. Here $\hat\theta_m\in(0,1)$ always.
-- source:
--   Grewal, Pelecanos, Spilecki, Tang, Wright, Pretty good shadow tomography, arXiv:2610.06781 (sha256 bd055b7d…), eqs. (26)–(27), p.27

import Mathlib
import Definitions.Def_PrettyGoodShadow_coinEntropy

namespace PrettyGoodShadow

/-- **Binary relative entropy** `D(Ber(θ) ∥ Ber(a)) = θ log(θ/a) + (1 − θ) log((1 − θ)/(1 − a))` in nats
(arXiv:2610.06781, sha256 bd055b7d…, eq. (26)–(27), p.27).

**Formalization Note** At every use `θ ∈ [0, 1]` and `a ∈ (0, 1)`; a term with `θ = 0` or `1 − θ = 0` vanishes,
as in the convention `0 log 0 = 0`. -/
noncomputable def klBern (θ a : ℝ) : ℝ :=
  θ * Real.log (θ / a) + (1 - θ) * Real.log ((1 - θ) / (1 - a))

/-- **Risk of the Laplace estimator** `E_{z ∼ Ber(θ)^m} D(Ber(θ) ∥ Ber(θ̂_m))`, with
`θ̂_m = (z_1 + … + z_m + 1)/(m + 2)` (arXiv:2610.06781, sha256 bd055b7d…, p.27). -/
noncomputable def laplaceRisk (m : ℕ) (θ : ℝ) : ℝ :=
  ∑ z : Fin m → Bool, coinWeight θ z *
    klBern θ (((∑ i, if z i then (1 : ℝ) else 0) + 1) / ((m : ℝ) + 2))

end PrettyGoodShadow


