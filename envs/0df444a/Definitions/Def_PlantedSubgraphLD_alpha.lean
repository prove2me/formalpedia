-- Prove2me | Definitions.Def_PlantedSubgraphLD_alpha
-- name    : PlantedSubgraphLD_alpha
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:19:29.992091+00:00
-- url     : https://prove2.me/theorems/c96ae8db-dcba-4c31-ba23-12b3c503ceb3
-- title:
--   The exact summand $\alpha_n(F)$
-- statement:
--   For $c>0$, $n$ and a nonempty abstract graph $F$ with $N_{\Gamma}(F)>0$,
--
--   $$
--   \alpha_n(F)=\Big(\frac{1-c/n}{c/n}\Big)^{e(F)}\frac{N_{\Gamma}(F)^2\,|\mathrm{Aut}(F)|}{(n)_{v(F)}},\qquad (n)_v=n(n-1)\cdots(n-v+1).
--   $$
--
--   It is the total contribution of the copies of $F$ to the squared $L^2(Q_n)$ norm of the likelihood ratio, the summand of the exact expansions (3.5) and (3.6).
--
--   **Formalization Note** $(n)_v$ is `Nat.descFactorial n v`. For $n\le c$ or $v(F)>n$ the value is junk; the statements that use it are about large $n$.
-- source:
--   Chen, Li, Rigorous Low-Degree Implications for Planted Subgraph Detection: Noise and Treewidth (manuscript of Nov. 3, 2026, arXiv:2608.06279, sha256 405d09c0…), §3.3, p.15 (PDF p.17)

import Mathlib
import Definitions.Def_PlantedSubgraphLD_AbsGraph

namespace PlantedSubgraphLD

/-- The exact summand of (3.5):
`αₙ(F) = ((1 − c/n)/(c/n))^{e(F)} · N_Γ(F)² |Aut(F)| / (n)_{v(F)}`.

Chen, Li, *Rigorous Low-Degree Implications for Planted Subgraph Detection* (manuscript of
Nov. 3, 2026, arXiv:2608.06279, sha256 405d09c0…), §3.3, p.15 (definition of αn(F) before
Lemma 3.1).

**Formalization Note** `(n)_v` is `Nat.descFactorial n v`. For `n ≤ c` or `v(F) > n` the value is
junk; the statements using it are eventual in `n`. -/
noncomputable def alpha {V : Type} [Fintype V] [DecidableEq V] {Γ : SimpleGraph V}
    (c : ℝ) (n : ℕ) (F : AbsGraph Γ) : ℝ :=
  ((1 - c / n) / (c / n)) ^ numEdges F * (count F : ℝ) ^ 2 * (autCard F : ℝ) /
    (n.descFactorial (numVerts F) : ℝ)

end PlantedSubgraphLD


