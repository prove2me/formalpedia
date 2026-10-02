-- Prove2me | Definitions.Def_TeschlODE_Shared_tentMap
-- name    : TeschlODE_Shared_tentMap
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T17:57:45.067345+00:00
-- url     : https://prove2.me/theorems/54eb36b4-a7fe-49dd-90fa-830e1036df6e
-- title:
--   The tent map $T_\mu(x) = \frac{\mu}{2}(1 - |2x - 1|)$ on $\mathbb{R}$ (11.12), (11.15)
-- statement:
--   For a real parameter $\mu$, the **tent map** is
--   $$T_\mu(x) = \frac{\mu}{2}\bigl(1 - |2x - 1|\bigr), \qquad x \in \mathbb{R}.$$
--   For $\mu \le 2$ it maps $[0,1]$ into itself; for $\mu > 2$ it does not, and the book considers it as a map on the whole real line $M = \mathbb{R}$ (11.15). Its graph is a tent with peak $T_\mu(1/2) = \mu/2$ and $T_\mu(0) = T_\mu(1) = 0$.
--
--   This one definition serves chunk 09-interval-maps (Theorem 11.5, p. 301; Theorem 11.20, p. 309; and through $\Lambda$ Lemma 11.4, p. 299) and chunk 11-horseshoe (Theorem 11.5, p. 301, and through $\Lambda$ Lemma 11.4, p. 299, and the horseshoe's invariant set (13.8), p. 332).
--
--   **Formalization Note.** The parameter is unrestricted in the definition; every theorem states the book's range ($\mu \ge 2$ or $\mu > 2$).
-- source:
--   Teschl, Ordinary Differential Equations and Dynamical Systems (author's preliminary version of AMS GSM 140, 2012), p. 297, §11.3, Eq. (11.12), and p. 298, §11.4, Eq. (11.15)

import Mathlib

namespace TeschlODE.Shared

/-- Teschl, §11.3–11.4, p. 297, (11.12) and p. 298, (11.15): the tent map
`T_µ(x) = (µ/2)(1 − |2x − 1|)`, considered as a map on `M = ℝ` (for `µ > 2` it no longer maps
`[0, 1]` into itself). The parameter `µ` is unrestricted here; theorems assume `µ ≥ 2` or
`µ > 2` as the book does. -/
noncomputable def tentMap (μ : ℝ) (x : ℝ) : ℝ :=
  μ / 2 * (1 - |2 * x - 1|)

end TeschlODE.Shared


