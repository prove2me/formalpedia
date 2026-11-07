-- Prove2me | Definitions.Def_GrothendieckLB_MixedScheme_avgCorr
-- name    : GrothendieckLB_MixedScheme_avgCorr
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:51:13.993365+00:00
-- url     : https://prove2.me/theorems/91442fd5-33e6-4089-830c-e734fd9846d3
-- title:
--   Averaged correlation function $H_\mu$
-- statement:
--   The averaged correlation function of a mixed rounding scheme $\mu$:
--   $$
--   H_\mu(t):=\mathbb E_{(f,g)\sim\mu}H_{f,g}(t).
--   $$
--   Its Taylor coefficients are the averages of those of $H_{f,g}$.
-- source:
--   Saha et al., New Lower and Upper Bounds for the Grothendieck Constant, arXiv:2608.11158 (held version, sha256 e7eb5d65…), Definition 10.1, p.42

import Mathlib
import Definitions.Def_GrothendieckLB_MixedScheme
import Definitions.Def_GrothendieckLB_pairCorr
open MeasureTheory

namespace GrothendieckLB

/-- The averaged correlation function `H_μ(t) := E_{(f,g)∼μ} H_{f,g}(t)` (Saha et al., *New Lower and Upper Bounds for the Grothendieck Constant*, arXiv:2608.11158 (held version, sha256 e7eb5d65…), Definition 10.1, p.42). -/
noncomputable def MixedScheme.avgCorr {d : ℕ} (S : MixedScheme d) (t : ℝ) : ℝ :=
  ∫ ω, pairCorr (S.F ω) (S.G ω) t ∂S.μ

end GrothendieckLB


