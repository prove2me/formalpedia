-- Prove2me | Definitions.Def_OmniMix_Supplement_seqRegret
-- name    : OmniMix_Supplement_seqRegret
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:33:08.496879+00:00
-- url     : https://prove2.me/theorems/bc2bf0c8-00bf-4217-a7cf-cfbefa69e119
-- title:
--   Regret $\mathrm{Reg}_{\ell,F}(T)$ of forecast measures for a real-valued proper loss
-- statement:
--   Let $\ell:[0,1]\times\{0,1\}\to\mathbb R$ be a loss, $F$ a finite class of maps $X\to[0,1]$, $(x_t,y_t)_{t\le T}$ a context–outcome sequence and $D_1,\dots,D_T$ probability measures on $[0,1]$. The **regret** is
--   $$
--   \mathrm{Reg}_{\ell,F}(T)=\sum_{t=1}^T\mathbb E_{P\sim D_t}[\ell(P,y_t)]-\min_{f\in F}\sum_{t=1}^T\ell(f(x_t),y_t).
--   $$
--
--   For a proper loss the downstream agent's post-processing is the identity, so this is the paper's regret $\mathrm{Reg}_{\ell,F}(T)$ with $\pi_\ell(p)=p$; it is used for the lower bounds and for Algorithm 1.
--
--   **Formalization Note** The expectation is a Bochner integral; every statement using it assumes a loss that is measurable and bounded (or Lipschitz) in the prediction, so the integral is the expectation. The value lies in the extended reals so that the minimum over $F$ is an infimum in a complete lattice; for nonempty $F$ it is the real minimum.
-- source:
--   Liu–Luo–Ratliff, Omniprediction for All Mixable Proper Losses and Beyond, arXiv:2610.41023, §1, p.1 (PDF p.3); App. A.1, p.21 (PDF p.23)

import Mathlib

namespace OmniMix.Supplement

/-- **Regret of a sequence of forecast measures, for a real-valued proper loss.** Liu–Luo–Ratliff,
*Omniprediction for All Mixable Proper Losses and Beyond*, arXiv:2610.41023, §1, p.1:
"`Reg_{ℓ,F}(T) = Σ_{t=1}^T E_{P_t∼D_t}[ℓ(π_ℓ(P_t), y_t)] − inf_{f∈F} Σ_{t=1}^T ℓ(f(x_t), y_t)`",
with `π_ℓ(p) = p` for a proper loss.

For a real-valued loss `ℓ`, a finite benchmark class `F`, contexts `x`, outcomes `y` and forecast
probability measures `D_t` on `[0,1]`,
`seqRegret ℓ F x y D = Σ_t ∫ ℓ(p, y_t) dD_t(p) − min_{f∈F} Σ_t ℓ(f(x_t), y_t)`.

**Formalization Note.** Used for proper losses only (Theorems 1.1, 1.3, 3.3), where `π_ℓ = id`
(p.1; p.21: "For these proper losses, we use the identity post-processing"). The expectation is a
Bochner integral; every theorem using it assumes losses that are measurable and bounded in `p`
(or Lipschitz), so the integral is the paper's expectation. The value is in `EReal` so that the
infimum over `F` is taken in a complete lattice: for nonempty `F` it is the real minimum. -/
noncomputable def seqRegret {X : Type*} {T : ℕ} (ℓ : unitInterval → Bool → ℝ)
    (F : Finset (X → unitInterval)) (x : Fin T → X) (y : Fin T → Bool)
    (D : Fin T → MeasureTheory.ProbabilityMeasure unitInterval) : EReal :=
  (((∑ t, ∫ p, ℓ p (y t) ∂(D t : MeasureTheory.Measure unitInterval) : ℝ)) : EReal) -
    ⨅ f ∈ F, (((∑ t, ℓ (f (x t)) (y t) : ℝ)) : EReal)

end OmniMix.Supplement


