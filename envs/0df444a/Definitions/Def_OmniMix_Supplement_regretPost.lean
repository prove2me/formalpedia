-- Prove2me | Definitions.Def_OmniMix_Supplement_regretPost
-- name    : OmniMix_Supplement_regretPost
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:33:33.031304+00:00
-- url     : https://prove2.me/theorems/e116b163-af20-41b3-a5d8-f692ef97192c
-- title:
--   Regret with a post-processing map $\pi_\ell$
-- statement:
--   Let $\ell$ be a loss, $\pi:[0,1]\to[0,1]$ a post-processing map, $F$ a finite benchmark class and $A$ an online forecaster with finitely supported forecasts $D_t$. On a context–outcome sequence $(x_t,y_t)_{t\le T}$ the **regret with post-processing $\pi$** is
--   $$
--   \mathrm{Reg}_{\ell,F}(T)=\sum_{t=1}^T\mathbb E_{P\sim D_t}\big[\ell(\pi(P),y_t)\big]-\inf_{f\in F}\sum_{t=1}^T\ell(f(x_t),y_t).
--   $$
--
--   In the paper $\pi=\pi_\ell$ is a Bayes-optimal action map, $\pi_\ell(p)\in\arg\min_{q\in[0,1]}\mathbb E_{Y\sim\mathrm{Ber}(p)}[\ell(q,Y)]$ with ties broken in a fixed way: the regret compares a downstream agent who acts optimally on the forecast with the best benchmark. It is needed for losses that are not proper.
--
--   **Formalization Note** The map $\pi$ is a parameter; statements assume it is a Bayes selection. With $\pi=\mathrm{id}$ this is the base mission's regret. Computed in the extended reals with the base conventions.
-- source:
--   Liu–Luo–Ratliff, Omniprediction for All Mixable Proper Losses and Beyond, arXiv:2610.41023, §1, p.1 (PDF p.3)

import Mathlib
import Definitions.Def_OmniMix_Loss
import Definitions.Def_OmniMix_FinDist_expect
import Definitions.Def_OmniMix_Forecaster
import Definitions.Def_OmniMix_forecasts

namespace OmniMix.Supplement

open OmniMix

/-- **Regret with a post-processing map `π_ℓ`.** Liu–Luo–Ratliff, *Omniprediction for All Mixable
Proper Losses and Beyond*, arXiv:2610.41023, §1, p.1:
"`Reg_{ℓ,F}(T) = Σ_{t=1}^T E_{P_t∼D_t}[ℓ(π_ℓ(P_t), y_t)] − inf_{f∈F} Σ_{t=1}^T ℓ(f(x_t), y_t)`, where
`π_ℓ(p) = argmin_{q∈[0,1]} E_{Y∼Ber(p)}[ℓ(q, Y)]` (… tie broken in an arbitrary, fixed way)".

`regretPost ℓ π F A x y` is this regret for the forecaster `A` on the sequence `(x, y)`, where the
downstream agent plays `π(P_t)` when the forecast is `P_t`; the benchmarks play `f(x_t)` directly.

**Formalization Note.** The post-processing map `π` is a parameter; theorems state that it is a
Bayes selection for `ℓ` (`bern p (ℓ (π p)) ≤ bern p (ℓ q)` for all `p, q`). With `π = id` this is
the base mission's `OmniMix.regret`. Computed in `EReal` with the base conventions. -/
noncomputable def regretPost {X : Type*} {T : ℕ} (ℓ : Loss) (π : unitInterval → unitInterval)
    (F : Finset (X → unitInterval)) (A : Forecaster X T) (x : Fin T → X) (y : Fin T → Bool) :
    EReal :=
  (∑ t, (forecasts A x y t).expect (fun p => ℓ (π p) (y t))) -
    ⨅ f ∈ F, ∑ t, ℓ (f (x t)) (y t)

end OmniMix.Supplement


