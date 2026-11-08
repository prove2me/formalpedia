-- Prove2me | Definitions.Def_MaxCompForest_distEnergy
-- name    : MaxCompForest_distEnergy
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:33:17.391196+00:00
-- url     : https://prove2.me/theorems/5a2757d1-7377-4623-bb21-e90b9aa94946
-- title:
--   Energy $\mathcal E_\rho$ of a pseudometric
-- statement:
--   For a pseudometric $\rho$ on $V$,
--   $$
--   \mathcal E_\rho=\sum_{e=uv}c_e\,\rho(u,v)^2 .
--   $$
-- source:
--   Chao–Ma–Gao–Cen–Wang, Maximum-Completion Forests via Sharp Spectral Quantization, STOC 2027 submission (manuscript sha256 48edea4274461ccd90489c3ddd2e07e5628e8f897e0b81d21055e99f6a7a83e2), Lemma 2.2, p.7

import Mathlib
import Definitions.Def_EffResSparsify_ResistanceSketch_Graph
open EffResSparsify.ResistanceSketch

namespace MaxCompForest

variable {V E : Type*} [Fintype E] [DecidableEq E]

/-- **The energy of a pseudometric** `E_ρ = ∑_{e=uv} c_e ρ(u,v)²`.
Chao–Ma–Gao–Cen–Wang, *Maximum-Completion Forests via Sharp Spectral Quantization*, STOC 2027 submission manuscript (sha256 48edea42…83e2), Lemma 2.2, p.7. -/
noncomputable def distEnergy (G : WGraph V E) (ρ : V → V → ℝ) : ℝ :=
  ∑ e, G.w e * ρ (G.head e) (G.tail e) ^ 2

end MaxCompForest


