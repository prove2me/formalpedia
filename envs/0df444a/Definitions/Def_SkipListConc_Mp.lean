-- Prove2me | Definitions.Def_SkipListConc_Mp
-- name    : SkipListConc_Mp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:49:58.69584+00:00
-- url     : https://prove2.me/theorems/ce8dd228-8c54-4baa-b60a-76b7c325dbd1
-- title:
--   Moment generating function $M_p(\eta)$ of $\mathrm{Geom}_0(p)$
-- statement:
--   For $Z\sim\mathrm{Geom}_0(p)$, so $\Pr[Z\ge r]=(1-p)^r$, and $0<\eta<\ln\frac{1}{1-p}$,
--   $$
--   M_p(\eta)=\mathbb E\bigl[e^{\eta Z}\bigr]=\frac{p}{1-(1-p)e^{\eta}}\ \ge 1 .
--   $$
--
--   **Formalization Note** The closed form, used only in that range of $\eta$.
-- source:
--   Kapoor–Tanveer, Counter-Free Self-Adjusting Skip Lists: Concentration Bounds, STOC 2027 submission (manuscript sha256 f82c3d35…), Definition 4.8, p.26

import Mathlib

namespace SkipListConc

/-- The moment generating function of `Z ∼ Geom₀(p)` (`Pr[Z ≥ r] = (1 − p)^r`) (Kapoor–Tanveer,
*Counter-Free Self-Adjusting Skip Lists: Concentration Bounds*, STOC 2027 submission manuscript
(sha256 f82c3d35…6dab6c), Definition 4.8, p.26): for `0 < η < ln(1/(1 − p))`,
`M_p(η) = E[e^{ηZ}] = p / (1 − (1 − p) e^η) ≥ 1`.

**Formalization Note** The closed form; it is used only in that range of `η`. -/
noncomputable def Mp (p η : ℝ) : ℝ :=
  p / (1 - (1 - p) * Real.exp η)

end SkipListConc


