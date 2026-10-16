-- Prove2me | Definitions.Def_LPCommunity_LPFail_Setting
-- name    : LPCommunity_LPFail_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T11:03:26.139485+00:00
-- url     : https://prove2.me/theorems/09b433a0-920d-4219-90d6-ddeebc07cc99
-- title:
--   §3.2, p. 12 — graph distances ρ_G, the diameter ρ_max(G), the average distance ρ_avg(G), and the constant c(G) of (17)
-- statement:
--   Let $G=(V,E)$ be a simple graph on the vertex set $V=\{1,\dots,n\}$.
--
--   1. **Distances.** $\rho_G(i,j)\in\mathbb Z_{\ge0}\cup\{+\infty\}$ is the length of a shortest path from $i$ to $j$ in $G$, with $\rho_G(i,j)=+\infty$ if $i$ and $j$ lie in different connected components.
--   2. **Diameter and average distance.**
--   $$\rho_{\max}(G)=\max_{i,j\in V}\rho_G(i,j),\qquad \rho_{\mathrm{avg}}(G)=\mathbb E_{i,j\sim\mathrm{Unif}(V)}[\rho_G(i,j)]=\frac{2}{n^2}\sum_{1\le i<j\le n}\rho_G(i,j).$$
--   The average is over ordered pairs $(i,j)$ drawn uniformly from $V^2$, the diagonal included; it is not the average over the $\binom n2$ unordered pairs.
--   3. **The constant of display (17).**
--   $$c(G)=\max\Big\{0,\ \frac{3\rho_{\max}(G)-4\rho_{\mathrm{avg}}(G)}{1-\frac4n}\Big\}.$$
--
--   These quantities enter the paper's necessary condition (18) for recovery by the metric relaxation (LP-P) (Theorem 5), and their asymptotics for random graphs drive the non-recovery results under the stochastic block model (Theorems 7 and 8).
--
--   **Formalization Note** Vertices are `Fin n` (0-based). $\rho_G$ and $\rho_{\max}$ take values in $\mathbb N\cup\{\infty\}$ (Mathlib's `SimpleGraph.edist` and `SimpleGraph.ediam`, the latter a maximum attained on a finite vertex set), and $\rho_{\mathrm{avg}}$ in $[0,\infty]$, so a disconnected graph has infinite diameter and infinite average distance. $c(G)$ is computed from the real values of $\rho_{\max}$ and $\rho_{\mathrm{avg}}$; these are the true values only when $G$ is connected, which is the only case in which the paper uses $c(G)$ (Theorem 5 assumes $G$ connected and $n\ge5$, so $1-4/n\neq0$). Bisections, the cut vector and (LP-P) are imported from the companion definitions of §2 and §3.
-- source:
--   Del Pia, Khajavirad, Kunisky, Linear Programming and Community Detection, arXiv:2006.03213v2, p. 12, §3.2 (ρ_G, ρ_max, ρ_avg) and display (17)

import Mathlib
import Definitions.Def_LPCommunity_LPRecovery_Setting
import Definitions.Def_LPCommunity_MinBisect_Setting

open Finset
open scoped Classical ENNReal

namespace LPCommunity.LPFail

/-! §3.2 of Del Pia, Khajavirad, Kunisky, *Linear Programming and Community Detection*
(arXiv:2006.03213v2): the graph distances ρ_G, ρ_max, ρ_avg (p. 12) and the constant c(G) of
display (17). Bisections come from `LPCommunity.MinBisect`, the metric relaxation (LP-P) and LP
recovery from `LPCommunity.LPRecovery`. Vertices are `Fin n` (the paper's {1,…,n}, shifted to
0-based). -/

/-- `ρ_G(i, j)`: the length of a shortest `i`–`j` path, `⊤` (= `+∞`) across components (p. 12). -/
noncomputable def rho {n : ℕ} (G : SimpleGraph (Fin n)) (i j : Fin n) : ℕ∞ := G.edist i j

/-- The diameter `ρ_max(G) = max_{i,j ∈ V} ρ_G(i, j)` (p. 12). -/
noncomputable def rhoMax {n : ℕ} (G : SimpleGraph (Fin n)) : ℕ∞ := G.ediam

/-- The average distance `ρ_avg(G) = (2/n²) ∑_{i<j} ρ_G(i, j)` (p. 12): the mean of `ρ_G(i, j)` over
`n²` ordered pairs, the diagonal included. -/
noncomputable def rhoAvg {n : ℕ} (G : SimpleGraph (Fin n)) : ℝ≥0∞ :=
  2 / (n : ℝ≥0∞) ^ 2 * ∑ i, ∑ j, if i < j then ((G.edist i j : ℕ∞) : ℝ≥0∞) else 0

/-- `c(G) = max{0, (3ρ_max(G) − 4ρ_avg(G)) / (1 − 4/n)}`, display (17), p. 12. Stated with the real
values of `ρ_max`, `ρ_avg`, which are finite for a connected graph (the only case it is used in). -/
noncomputable def cG {n : ℕ} (G : SimpleGraph (Fin n)) : ℝ :=
  max 0 ((3 * ((rhoMax G : ℕ∞) : ℝ≥0∞).toReal - 4 * (rhoAvg G).toReal) / (1 - 4 / (n : ℝ)))

end LPCommunity.LPFail


