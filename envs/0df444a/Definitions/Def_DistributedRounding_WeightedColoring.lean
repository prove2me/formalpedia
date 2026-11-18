-- Prove2me | Definitions.Def_DistributedRounding_WeightedColoring
-- name    : DistributedRounding_WeightedColoring
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-17T18:16:35.862358+00:00
-- url     : https://prove2.me/theorems/e7296abe-8550-48b0-8bac-69999d440b5e
-- title:
--   Operational weighted average defective coloring in LOCAL
-- statement:
--   This is the interface for weighted average defective coloring used in local distributed rounding.
--
--   Let $H$ be a finite simple communication graph, with nonnegative symmetric weights $w_{vu}$ on adjacent vertices, and a supplied proper vertex coloring from a palette of size $\zeta$. A processor receives its own color and a dictionary of its incident weights, addressed by neighbor identifiers. For integer precision $Q\ge2$, the contract asks for one deterministic LOCAL protocol and a positive absolute integer constant $C$ such that the output coloring $c$ uses fewer than $CQ$ colors, takes at most $C(Q+\max\{1,\log^*\zeta\})$ physical rounds, and satisfies
--
--   $$
--   Q\sum_v\sum_{u\sim v}\mathbf 1_{c(u)=c(v)}w_{vu}
--   \le4\sum_v\sum_{u\sim v}w_{vu}.
--   $$
--
--   The ordered incidence convention counts every undirected edge twice on both sides. The protocol and constant precede every graph, weight system, precision and input coloring. This contract supplies the coloring subroutine needed to control simultaneous rounding interactions.
--
--   **Formalization Note** Graphs use $\operatorname{Fin}(N)$; the processor input contains no carrier index. Weights are obtained by evaluating the local dictionary at actual neighbor identifiers. The symmetric nonnegative table may be extended by zero away from edges. Unlike the CONGEST specialization of Lemma 2.6, this LOCAL interface imposes no encoding-size or magnitude restriction on real weights.
-- source:
--   Faour, Ghaffari, Grunau, Kuhn, Rozhon, Local Distributed Rounding: Generalized to MIS, Matching, Set Cover, and Beyond, arXiv:2209.11651v1, https://arxiv.org/abs/2209.11651v1, Definition 1.1 p.12 and proof of Lemma 2.6 pp.22–24 (PDF pp.24–26); LOCAL specialization of the weighted coloring construction, with unrestricted messages and real weights. Also Ghaffari–Grunau STOC2027 submission1024, Lemma2.2 p.7/PDF9.

import Definitions.Def_FasterDistributedMatching_ApproximateMatching_Routing

namespace DistributedRounding
open FasterDistributedMatching.ApproximateMatching

abbrev WeightedInput := (ℕ → ℝ) × ℕ

open Classical in
noncomputable def incident {N : ℕ} (H : SimpleGraph (Fin N))
    (w : Fin N → Fin N → ℝ) (v : Fin N) : ℝ := ∑ u ∈ H.neighborFinset v, w v u

open Classical in
noncomputable def monochromatic {N : ℕ} (H : SimpleGraph (Fin N))
    (w : Fin N → Fin N → ℝ) (col : Fin N → ℕ) : ℝ :=
  ∑ v, ∑ u ∈ H.neighborFinset v, if col u = col v then w v u else 0

/- A LOCAL weighted average defective coloring contract. Inputs supply only the
own color and own incident weights addressed by neighbor identifiers. -/
def WeightedAverageColoring : Prop :=
  ∃ (A : Deterministic (ℕ × ℕ) WeightedInput ℕ) (C : ℕ), 0 < C ∧
    (∀ Q zeta, 2 ≤ Q → A.program.rounds (Q,zeta) ≤ C*(Q+logStar zeta)) ∧
    ∀ (N : ℕ) (H : SimpleGraph (Fin N)) (ids : Fin N → ℕ)
      (weights : Fin N → ℕ → ℝ) (col : Fin N → ℕ) (Q zeta : ℕ),
      2 ≤ Q → Proper H zeta col →
      (∀ v u, 0 ≤ weights v (ids u)) →
      (∀ v u, weights v (ids u) = weights u (ids v)) →
      let out := execute A H (Q,zeta) ids (fun v => (weights v,col v))
      (∀ v, out v < C*Q) ∧
      (Q:ℝ)*monochromatic H (fun v u => weights v (ids u)) out ≤
        4*(∑ v, incident H (fun v u => weights v (ids u)) v)

end DistributedRounding


