-- Prove2me | Definitions.Def_VolunteerNotify_f
-- name    : VolunteerNotify_f
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T05:37:35.589724+00:00
-- url     : https://prove2.me/theorems/4fa51795-5a20-4309-b483-f9336c80de61
-- title:
--   (3), (4) — the always-active objective $f$ and the contributions $f_v$
-- statement:
--   For $x\in\mathbb R^{V\times S\times T}$,
--   $$
--   f(x)=\sum_{t=1}^T\sum_{s=1}^S\lambda_{s,t}\Bigl(1-\prod_{v=1}^V(1-x_{v,s,t}p_{v,s})\Bigr) \tag{3}
--   $$
--   is the expected number of completed tasks if each volunteer were always active and were notified independently according to $x$, and
--   $$
--   f_v(x)=\sum_{t=1}^T\sum_{s=1}^S\lambda_{s,t}\Bigl(\prod_{u<v}(1-p_{u,s}x_{u,s,t})\Bigr)p_{v,s}x_{v,s,t} \tag{4}
--   $$
--   is the part of it credited to volunteer $v$ under the index-based priority scheme.
--
--   These functions connect the benchmark to the policy: the ex ante solution is compared to $\mathrm{LP}_{\mathcal I}$ through $f$, and the dynamic program is compared to $f_v$.
-- source:
--   Manshadi, Rodilitz, Online Policies for Efficient Volunteer Crowdsourcing, arXiv:2002.08474v7, (3), p.13; (4), p.14

import Mathlib
import Definitions.Def_VolunteerNotify_Instance

namespace VolunteerNotify

variable {V S T : ℕ}

/-- The always-active objective `f`, Manshadi–Rodilitz, arXiv:2002.08474v7, (3), p.13:
`f(x) = ∑_t ∑_s λ_{s,t} (1 − ∏_v (1 − x_{v,s,t} p_{v,s}))`. -/
noncomputable def f (I : Instance V S T) (x : Decision V S T) : ℝ :=
  ∑ t, ∑ s, I.lam s t * (1 - ∏ v, (1 - x v s t * I.p v s))

/-- The priority-based contribution `f_v`, arXiv:2002.08474v7, (4), p.14:
`f_v(x) = ∑_t ∑_s λ_{s,t} (∏_{u<v} (1 − p_{u,s} x_{u,s,t})) p_{v,s} x_{v,s,t}`. -/
noncomputable def fv (I : Instance V S T) (x : Decision V S T) (v : Fin V) : ℝ :=
  ∑ t, ∑ s, I.lam s t * (∏ u ∈ Finset.Iio v, (1 - I.p u s * x u s t)) * I.p v s * x v s t

end VolunteerNotify


