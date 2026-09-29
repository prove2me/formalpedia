-- Prove2me | Definitions.Def_douglas_flux_vacua_count
-- name    : douglas_flux_vacua_count
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-24T18:47:33.562264+00:00
-- url     : https://prove2.me/theorems/c24cfa29-fcc0-4401-b6e7-d57c8c076a21
-- title:
--   Flux potential and flux vacua count (Bousso–Polchinski model)
-- statement:
--   For $J\in\mathbb N$, $c\in\mathbb R$ and a flux vector $N\in\mathbb Z^J$, the **flux potential** is $V(N)=c\sum_{i=1}^J N_i^2$ (eq. (3.12), with $c=M_{pl}^2/(M^{2p}V_{p+1}^2)$). The **flux vacua count** at level $V$ is
--   $$\mathcal N_J(c,V)=\#\{N\in\mathbb Z^J : V(N)\le V\},$$
--   the cumulative distribution of the number measure $d\mu(V)=\sum_N\delta(V-V(N))$ of eq. (3.13). (Formally the cardinality is `Set.ncard`, which is $0$ on an infinite set; for $c>0$ the set is finite.)
-- source:
--   Michael R. Douglas, *The statistics of string/M theory vacua*, JHEP 05 (2003) 046, https://doi.org/10.1088/1126-6708/2003/05/046 (arXiv:hep-th/0303194). Section 3.6, pp. 23–24, eqs. (3.11)–(3.13).

import Mathlib

namespace DouglasVacua

/-- The flux potential of the Bousso–Polchinski model (Douglas 2003, eq. (3.12)):
for a flux vector `N ∈ ℤ^J` and a constant `c = M_pl^2 / (M^{2p} V_{p+1}^2)`,
`V(N) = c · ∑ᵢ Nᵢ²`. -/
noncomputable def fluxPotential {J : ℕ} (c : ℝ) (N : Fin J → ℤ) : ℝ :=
  c * ∑ i, ((N i : ℝ)) ^ 2

/-- The number of flux vectors `N ∈ ℤ^J` whose flux potential is at most `V`,
i.e. the cumulative distribution `∫_{-∞}^{V} dμ` of the measure (3.13) of Douglas 2003. -/
noncomputable def fluxVacuaCount (J : ℕ) (c V : ℝ) : ℕ :=
  Set.ncard {N : Fin J → ℤ | fluxPotential c N ≤ V}

end DouglasVacua


