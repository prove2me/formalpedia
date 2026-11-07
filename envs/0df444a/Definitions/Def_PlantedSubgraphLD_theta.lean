-- Prove2me | Definitions.Def_PlantedSubgraphLD_theta
-- name    : PlantedSubgraphLD_theta
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:20:30.304426+00:00
-- url     : https://prove2.me/theorems/3e8a8e8d-2631-4412-af29-3598e0bff9d7
-- title:
--   The connected sum $\theta_{n,\varepsilon}$
-- statement:
--   For $c>0$, $\varepsilon\in(0,1)$ and the planted graph $\Gamma_n$,
--
--   $$
--   \theta_{n,\varepsilon}=\sum_{\substack{F:\,N_{\Gamma_n}(F)>0\\ F\text{ connected}}}(1-\varepsilon)^{2e(F)}\,\beta_n(F),
--   $$
--
--   the sum over the connected nonempty abstract graphs that occur in $\Gamma_n$. The proof of Theorem 1.1 shows $\theta_{n,\varepsilon}=o(1)$ (Lemma 4.6) and then passes to all subgraphs by factoring over connected components (Lemma 4.5).
-- source:
--   Chen, Li, Rigorous Low-Degree Implications for Planted Subgraph Detection: Noise and Treewidth (manuscript of Nov. 3, 2026, arXiv:2608.06279, sha256 405d09c0…), §4.2, p.20 (PDF p.22)

import Mathlib
import Definitions.Def_PlantedSubgraphLD_beta

open Classical

namespace PlantedSubgraphLD

/-- `θ_{n,ε} = ∑_{F : N_Γ(F) > 0, F connected} (1 − ε)^{2e(F)} βₙ(F)`.

Chen, Li, *Rigorous Low-Degree Implications for Planted Subgraph Detection* (manuscript of
Nov. 3, 2026, arXiv:2608.06279, sha256 405d09c0…), §4.2, p.20 (before Lemma 4.5).

**Formalization Note** The sum is over the connected elements of `AbsGraph Γ` (nonempty abstract
graphs with `N_Γ(F) > 0`), a finite set. -/
noncomputable def theta (c ε : ℝ) (n : ℕ) {V : Type} [Fintype V] [DecidableEq V]
    (Γ : SimpleGraph V) : ℝ :=
  ∑ F ∈ (Finset.univ.filter (fun F : AbsGraph Γ => IsConn F)),
    (1 - ε) ^ (2 * numEdges F) * beta c n F

end PlantedSubgraphLD


