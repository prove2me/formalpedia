-- Prove2me | Definitions.Def_NSWBetter_thr
-- name    : NSWBetter_thr
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:53:22.999676+00:00
-- url     : https://prove2.me/theorems/33c75d4f-3935-43fa-a659-5ecd7e8e6fed
-- title:
--   Large-good threshold $v(G\setminus L)/(\Delta-\ell)=\Delta\mu/(\Delta-\ell)$
-- statement:
--   The threshold $\tau=\dfrac{v(G\setminus L)}{\Delta-\ell}=\dfrac{\Delta\mu}{\Delta-\ell}$ of Definition 3.2: large goods have value $>\tau$, small goods value $\le\tau$.
-- source:
--   Viswanathan, A Better-than-e^{1/e} Approximation Algorithm for Nash Social Welfare under Additive Valuations, arXiv:2607.13340 (held version, sha256 08811cb468c2df39231dca4222c5af94163587c7c83e205e50bbf0b91fc1deb3), Definition 3.2, p.11

import Mathlib
import Definitions.Def_NSWBetter_tailSum
import Definitions.Def_NSWBetter_largeCount

namespace NSWBetter

/-- **The threshold of Definition 3.2.**
Viswanathan, *A Better-than-e^{1/e} Approximation Algorithm for Nash Social Welfare under Additive Valuations*, arXiv:2607.13340 (held version, sha256 08811cb4…), Definition 3.2, p.11: `v(G\L)/(∆−ℓ)`; it equals `∆µ/(∆−ℓ)` (Definition 3.4).

`thr Δ s = tailSum s ℓ / (Δ − ℓ)` with `ℓ = largeCount Δ s`. A good is large iff its value exceeds `thr`. -/
noncomputable def thr (Δ : ℕ) (s : Multiset ℝ) : ℝ :=
  tailSum s (largeCount Δ s) / ((Δ : ℝ) - largeCount Δ s)

end NSWBetter


