-- Prove2me | Definitions.Def_OmniMix_regret
-- name    : OmniMix_regret
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:41:18.987173+00:00
-- url     : https://prove2.me/theorems/36d2b1f7-62dc-480d-8b87-bd2642addd7f
-- title:
--   Regret $\mathrm{Reg}_{\ell,F}(T)$
-- statement:
--   For a proper loss $\ell$, a finite benchmark class $F$ of maps $X\to[0,1]$, a forecaster and a context–outcome sequence of length $T$,
--   $$
--   \mathrm{Reg}_{\ell,F}(T)=\sum_{t=1}^T\mathbb E_{P_t\sim D_t}[\ell(P_t,y_t)]-\inf_{f\in F}\sum_{t=1}^T\ell(f(x_t),y_t),
--   $$
--   where $D_t$ are the forecaster's forecasts on the sequence. (For a proper loss the paper's post-processing $\pi_\ell$ is the identity.)
--
--   **Formalization Note** Computed in the extended reals: the infimum over an empty class is $+\infty$, and $a-(+\infty)=-\infty$ for every $a$, so when every benchmark has infinite total loss the regret is $-\infty$, the paper's convention for an infinite comparator loss.
-- source:
--   Liu–Luo–Ratliff, Omniprediction for All Mixable Proper Losses and Beyond, arXiv:2610.41023, §1, p.1

import Mathlib
import Definitions.Def_OmniMix_Loss
import Definitions.Def_OmniMix_FinDist_expect
import Definitions.Def_OmniMix_Forecaster
import Definitions.Def_OmniMix_forecasts

namespace OmniMix

/-- **Regret `Reg_{ℓ,F}(T)`.** Liu–Luo–Ratliff, *Omniprediction for All Mixable Proper Losses and Beyond*, arXiv:2610.41023, §1, p.1:
"`Reg_{ℓ,F}(T) = Σ_{t=1}^T E_{P_t∼D_t}[ℓ(π_ℓ(P_t), y_t)] − inf_{f∈F} Σ_{t=1}^T ℓ(f(x_t), y_t)`".

**Formalization Note.** Stated for proper losses, where `π_ℓ(p) = p` (§1, p.1). The benchmark class
is a finite set `F` of maps `X → [0,1]` (§1.1, p.2: "throughout, we assume a finite benchmark class
`F`"). Everything is computed in `EReal`. Mathlib's conventions: the infimum over an empty `F` is `⊤`,
and `a − ⊤ = ⊥` for every `a` (including `a = ⊤`), so when every benchmark has infinite total loss the
regret is `−∞`, the paper's convention for an infinite comparator loss ("the corresponding loss
difference is −∞", p.31). -/
noncomputable def regret {X : Type*} {T : ℕ} (ℓ : Loss) (F : Finset (X → unitInterval))
    (A : Forecaster X T) (x : Fin T → X) (y : Fin T → Bool) : EReal :=
  (∑ t, (forecasts A x y t).expect (fun p => ℓ p (y t))) -
    ⨅ f ∈ F, ∑ t, ℓ (f (x t)) (y t)

end OmniMix


