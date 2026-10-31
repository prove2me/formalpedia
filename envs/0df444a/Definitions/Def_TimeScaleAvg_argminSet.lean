-- Prove2me | Definitions.Def_TimeScaleAvg_argminSet
-- name    : TimeScaleAvg_argminSet
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:08:55.590413+00:00
-- url     : https://prove2.me/theorems/6ffe5182-e668-439b-beeb-029f93da0c0a
-- title:
--   The solution set $S=\operatorname{argmin}_{\mathcal H} f$
-- statement:
--   Let $f:\mathcal H\to\mathbb R$. The solution set of the problem $\min\{f(x):x\in\mathcal H\}$ is
--
--   $$
--   S=\operatorname{argmin}_{\mathcal H}f=\{x\in\mathcal H:\ f(x)\le f(y)\ \text{ for all }y\in\mathcal H\}.
--   $$
--
--   Every weak limit in this mission is required to lie in $S$.
-- source:
--   Attouch, Boţ & Nguyen, Fast Convex Optimization via Time Scale and Averaging of the Steepest Descent, arXiv:2208.08260v3, Eqs. (1)–(2), p.1

import Mathlib

namespace TimeScaleAvg

/-- The solution set `S = argmin_H f` of problem (1), `min {f(x) : x ∈ H}`
(Attouch, Boţ & Nguyen, Fast Convex Optimization via Time Scale and Averaging of the Steepest
Descent, arXiv:2208.08260v3, Eqs. (1)–(2), p.1): the points at which `f` attains its minimum over
the whole space. -/
def argminSet {H : Type*} (f : H → ℝ) : Set H :=
  {x | ∀ y, f x ≤ f y}

end TimeScaleAvg


