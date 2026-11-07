-- Prove2me | Definitions.Def_PlantedSubgraphLD_beta
-- name    : PlantedSubgraphLD_beta
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:19:31.404904+00:00
-- url     : https://prove2.me/theorems/fdb2c07c-13b9-4db5-986c-3837f2507b10
-- title:
--   The simplified summand $\beta_n(F)$
-- statement:
--   For $c>0$, $n\ge1$ and a nonempty abstract graph $F$ with $N_{\Gamma}(F)>0$,
--
--   $$
--   \beta_n(F)=\frac{n^{e(F)-v(F)}}{c^{e(F)}}\,N_{\Gamma}(F)^2\,|\mathrm{Aut}(F)| .
--   $$
--
--   By Lemma 3.1, $\beta_n(F)$ agrees with the exact summand $\alpha_n(F)$ up to a factor $1+o(1)$ whenever $e(F)=o(\sqrt n)$; unlike $\alpha_n$ it factors exactly over pieces of a decomposition, which is how the paper bounds large subgraphs.
--
--   **Formalization Note** $n^{e(F)-v(F)}$ is an integer power of the real number $n$; the exponent may be negative.
-- source:
--   Chen, Li, Rigorous Low-Degree Implications for Planted Subgraph Detection: Noise and Treewidth (manuscript of Nov. 3, 2026, arXiv:2608.06279, sha256 405d09c0…), §3.3, p.15 (PDF p.17)

import Mathlib
import Definitions.Def_PlantedSubgraphLD_AbsGraph

namespace PlantedSubgraphLD

/-- The simplified summand `βₙ(F) = n^{e(F) − v(F)} / c^{e(F)} · N_Γ(F)² |Aut(F)|`.

Chen, Li, *Rigorous Low-Degree Implications for Planted Subgraph Detection* (manuscript of
Nov. 3, 2026, arXiv:2608.06279, sha256 405d09c0…), §3.3, p.15 (definition of βn(F) before
Lemma 3.1).

**Formalization Note** `n^{e − v}` is the integer power of the real `n` (the exponent can be
negative). -/
noncomputable def beta {V : Type} [Fintype V] [DecidableEq V] {Γ : SimpleGraph V}
    (c : ℝ) (n : ℕ) (F : AbsGraph Γ) : ℝ :=
  (n : ℝ) ^ ((numEdges F : ℤ) - numVerts F) / c ^ numEdges F * (count F : ℝ) ^ 2 * (autCard F : ℝ)

end PlantedSubgraphLD


