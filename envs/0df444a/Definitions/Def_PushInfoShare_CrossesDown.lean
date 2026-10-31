-- Prove2me | Definitions.Def_PushInfoShare_CrossesDown
-- name    : PushInfoShare_CrossesDown
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:45:19.45015+00:00
-- url     : https://prove2.me/theorems/08db99d2-94bf-4de0-af72-e27b301be01c
-- title:
--   Downward crossing at a threshold
-- statement:
--   A function $g$ **crosses zero downward** at $\hat\phi$ if $\hat\phi>0$, $g>0$ on $[0,\hat\phi)$, $g(\hat\phi)=0$ and $g<0$ on $(\hat\phi,\infty)$. This is the threshold shape of Proposition 5.
--
--   **Formalization Note** The printed "otherwise" would give a strict sign at $\hat\phi$ itself; a continuous function changing sign vanishes there.
-- source:
--   Jain, Sharing Demand Information with Retailer under Upstream Competition, SSRN:3388957 (PDF of 2021-04-25), Proposition 5, p.17

import Mathlib

namespace PushInfoShare

/-- `g` crosses zero downward at `φhat` on `[0, ∞)`: `φhat > 0`, `g > 0` on `[0, φhat)`,
`g φhat = 0`, and `g < 0` on `(φhat, ∞)`. This is the threshold shape of Proposition 5, Jain, SSRN:3388957 (PDF of
2021-04-25), p.17.

**Formalization Note.** The printed "otherwise" would give a strict sign at `φhat` itself; a
continuous function changing sign is zero there, so equality holds at `φhat`. -/
def CrossesDown (g : ℝ → ℝ) (φhat : ℝ) : Prop :=
  0 < φhat ∧ (∀ φ, 0 ≤ φ → φ < φhat → 0 < g φ) ∧ g φhat = 0 ∧ ∀ φ, φhat < φ → g φ < 0

end PushInfoShare


