-- Prove2me | Definitions.Def_PlantedSubgraphLD_noisedPlanted
-- name    : PlantedSubgraphLD_noisedPlanted
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:21:22.158581+00:00
-- url     : https://prove2.me/theorems/63a0fdc7-7509-4860-951f-d5355ec5932b
-- title:
--   The noise operator $T_\varepsilon$ and the noised planted law $T_\varepsilon P_n$
-- statement:
--   For $\varepsilon\in(0,1)$ the **noise operator** $T_\varepsilon$ acts on a random graph on $[n]$ independently for each unordered pair $e$ of distinct vertices: with probability $\varepsilon$ it resamples the indicator of $e$ from the Bernoulli distribution with parameter $c/n$, and otherwise leaves it unchanged. Its transition kernel is
--
--   $$
--   K_\varepsilon(G,G')=\prod_{1\le i<j\le n}\Big((1-\varepsilon)\,\mathbf 1\big[\{i,j\}\in G\Leftrightarrow\{i,j\}\in G'\big]+\varepsilon\,b(\{i,j\}\in G')\Big),\qquad b(\text{true})=\tfrac cn,\ b(\text{false})=1-\tfrac cn,
--   $$
--
--   and a law $\mu$ is mapped to $(T_\varepsilon\mu)(G')=\sum_G\mu(G)K_\varepsilon(G,G')$. The **noised planted law** is $T_\varepsilon P_n$; the testing problem of the paper is $H_0:G_n\sim Q_n$ against $H_1:G_n\sim T_\varepsilon P_n$.
--
--   **Formalization Note** This is the paper's definition of $T_\varepsilon$ (resampling). Its equivalent description, deleting each planted edge with probability $\varepsilon$ before planting, is a theorem of the mission (`noise_equivalence`). The edge probability $c/n$ is used without clamping; it lies in $(0,1)$ for $n>c$.
-- source:
--   Chen, Li, Rigorous Low-Degree Implications for Planted Subgraph Detection: Noise and Treewidth (manuscript of Nov. 3, 2026, arXiv:2608.06279, sha256 405d09c0…), §1.1, p.3 (PDF p.5); §3.2, p.12 (PDF p.14)

import Mathlib
import Definitions.Def_PlantedSubgraphLD_planted

open Classical

namespace PlantedSubgraphLD

/-- The transition kernel of the noise operator `T_ε` on graphs on `[n]`: independently for each
unordered pair `{i, j}`, with probability `ε` the indicator is resampled from Bernoulli(`c/n`),
otherwise it is kept. For one pair the kernel is `(1 − ε)·1[x = y] + ε·Bern_{c/n}(y)`. -/
noncomputable def noiseKernel (c ε : ℝ) (n : ℕ) (G G' : SimpleGraph (Fin n)) : ℝ :=
  ∏ p ∈ LPCommunity.SBMRecovery.pairs n,
    ((1 - ε) * (if (G.Adj p.1 p.2 ↔ G'.Adj p.1 p.2) then 1 else 0) +
      ε * (if G'.Adj p.1 p.2 then c / n else 1 - c / n))

/-- The image `T_ε μ` of a law `μ` on graphs on `[n]` under the noise kernel. -/
noncomputable def noise (c ε : ℝ) (n : ℕ) (μ : SimpleGraph (Fin n) → ℝ)
    (G' : SimpleGraph (Fin n)) : ℝ :=
  ∑ G : SimpleGraph (Fin n), μ G * noiseKernel c ε n G G'

/-- The noised planted law `T_ε Pₙ`.

Chen, Li, *Rigorous Low-Degree Implications for Planted Subgraph Detection* (manuscript of
Nov. 3, 2026, arXiv:2608.06279, sha256 405d09c0…), §3.2, p.12: "The noise operator Tε acts on a
graph on [n] independently for each pair e ∈ ([n] choose 2): with probability ε it resamples the
indicator of e from the Bernoulli distribution with parameter c/n, and otherwise it leaves the
indicator unchanged." (Also §1.1, p.3.)

**Formalization Note** This is the paper's definition of `T_ε` (resampling), applied to `Pₙ`.
The equivalent description by deleting planted edges is a theorem of the mission
(`noise_equivalence`), not the definition. Pairs are `(i, j)` with `i < j`
(`LPCommunity.SBMRecovery.pairs`). The edge probability is `c/n` without clamping; it lies in
`(0, 1)` for `n > c`, the only regime the theorems are about. -/
noncomputable def noisedPlanted (c ε : ℝ) (n : ℕ) {V : Type} [Fintype V] [DecidableEq V]
    (Γ : SimpleGraph V) : SimpleGraph (Fin n) → ℝ :=
  noise c ε n (planted c n Γ)

end PlantedSubgraphLD


