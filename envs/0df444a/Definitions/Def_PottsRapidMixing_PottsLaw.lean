-- Prove2me | Definitions.Def_PottsRapidMixing_PottsLaw
-- name    : PottsRapidMixing_PottsLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:52:32.304052+00:00
-- url     : https://prove2.me/theorems/a06a5d4b-7c91-4428-a865-fe3c1157ea40
-- title:
--   The Potts law $\mu_{G,\beta,q}$
-- statement:
--   For an integer $q$ and a graph $H=(W,F)$, the ferromagnetic $q$-state Potts model at inverse temperature $\beta$ is the law on $\sigma\in[q]^W$ given by
--   $$\mu_{H,\beta,q}(\sigma)=\frac1Z e^{\beta M(\sigma)},\qquad M(\sigma)=\sum_{uv\in F}\mathbf 1\{\sigma_u=\sigma_v\},\quad Z=\sum_\sigma e^{\beta M(\sigma)}.$$
--
--   This is the target law of the mission; Glauber dynamics is its single-site heat-bath chain.
--
--   **Formalization Note** $M$ and $Z$ are the published `ExpanderBIS.Potts.monoEdges` and `pottsZ`. The conditional law $\mu^\tau_{F^+}$ of the paper is the law `condLaw` of the Potts law on $F^+$ given the spins off $F$.
-- source:
--   Blanca, Gheissari, Park, Zhang, Rapid mixing of Potts Glauber dynamics throughout uniqueness, arXiv:2610.42059, (1.1), p.1

import Mathlib
import Definitions.Def_ExpanderBIS_Potts_Setting

open scoped Classical

namespace PottsRapidMixing

variable {W : Type*} [Fintype W] [DecidableEq W]

/-- The ferromagnetic `q`-state Potts law at inverse temperature `β` on a graph `H`, (1.1):
`µ_{H,β,q}(σ) = e^{β M(σ)}/Z` (Blanca, Gheissari, Park, Zhang, arXiv:2610.42059, p.1), with `M`
the published `monoEdges` and `Z` the published `pottsZ`. Spins are `Fin q`. -/
noncomputable def pottsLaw (H : SimpleGraph W) (β : ℝ) (q : ℕ) : (W → Fin q) → ℝ :=
  fun σ => Real.exp (β * (ExpanderBIS.Potts.monoEdges H σ : ℝ)) / ExpanderBIS.Potts.pottsZ H q β

end PottsRapidMixing


