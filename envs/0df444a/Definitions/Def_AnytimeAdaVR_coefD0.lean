-- Prove2me | Definitions.Def_AnytimeAdaVR_coefD0
-- name    : AnytimeAdaVR_coefD0
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:27:02.409547+00:00
-- url     : https://prove2.me/theorems/8192bcbf-860e-4261-9baa-226e402588db
-- title:
--   Noiseless coefficient $D_0$
-- statement:
--   $$
--   D_0=2+2\Delta_f+2L\log\big(\max\{1,2L\}\big),
--   $$
--   the coefficient of the D path's noiseless guarantee $\mathbb E\|\nabla f(R_{D,N})\|\le D_0/\sqrt N$.
-- source:
--   Jiang–Wang–Yang–Zhang–Li, Adaptive Variance Reduction across Smoothness and Noise Conditions (preprint, 2026; held artifact sha256 6f3caf41…74006), App. D, eq. (50), p.25; §5.2, p.9

import Mathlib

namespace AnytimeAdaVR

/-- **The noiseless D-path coefficient `D₀ = 2 + 2∆f + 2L log(max{1, 2L})`.** Jiang–Wang–Yang–Zhang–Li, *Adaptive Variance Reduction across Smoothness and Noise Conditions*
(preprint, 2026), App. D, p.25,
eq. (50); also §5.2, p.9 and App. G.1, p.30. -/
noncomputable def coefD0 (Δf L : ℝ) : ℝ :=
  2 + 2 * Δf + 2 * L * Real.log (max 1 (2 * L))

end AnytimeAdaVR


