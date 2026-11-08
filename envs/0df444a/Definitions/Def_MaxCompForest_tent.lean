-- Prove2me | Definitions.Def_MaxCompForest_tent
-- name    : MaxCompForest_tent
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:33:11.6538+00:00
-- url     : https://prove2.me/theorems/b6003ccb-5739-4fc5-9a69-68c825dbc2e2
-- title:
--   The tent $f_c(v)=(r_v-\rho(c,v))_+$
-- statement:
--   For radii $r_v$ and a pseudometric $\rho$, the tent of a row facility $c$ is
--   $$
--   f_c(v)=(r_v-\rho(c,v))_+ .
--   $$
-- source:
--   Chao–Ma–Gao–Cen–Wang, Maximum-Completion Forests via Sharp Spectral Quantization, STOC 2027 submission (manuscript sha256 48edea4274461ccd90489c3ddd2e07e5628e8f897e0b81d21055e99f6a7a83e2), Lemma 2.2, p.7

import Mathlib

namespace MaxCompForest

variable {V : Type*}

/-- **The tent** `f_c(v) = (r_v − ρ(c,v))₊` of a facility `c` under radii `r`.
Chao–Ma–Gao–Cen–Wang, *Maximum-Completion Forests via Sharp Spectral Quantization*, STOC 2027 submission manuscript (sha256 48edea42…83e2), Lemma 2.2, p.7. -/
noncomputable def tent (r : V → ℝ) (ρ : V → V → ℝ) (c v : V) : ℝ := max (r v - ρ c v) 0

end MaxCompForest


